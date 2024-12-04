(* Distributed under the terms of the MIT license. *)
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config Environment uGraph.
From MetaCoq.Template Require Import Ast AstUtils LiftSubst UnivSubst Typing Evars.
Import MCMonadNotation.

Unset Guard Checking.

(** This file implements :
    - several variants of alpha equivalence on terms 
      (e.g. with or without unfolding evars or removing casts) :
      [eq_term], [eq_term_evars].
    - reduction (both strong reduction and weak-head reduction) 
      with arbitrary reduction flags : [reduce] and [weak_head_reduce].
    - conversion and cumulativity checking with arbitrary reduction flags : 
      [check_conv].
    - type inference, type checking and retyping for terms :
      [infer], [check] and [retype].
    
    It is intended for practical use and is not verified 
    (we even disable the guard checker). *)

(** * Alpha equivalence. *)

(** [rebuild_case env ci pred bs] rebuilds the terms corresponding to the 
    case predicate and branches of [tCase ci pred _ bs]. 
    This involves adding lambda abstractions and let-ins as needed. *)
Definition rebuild_case Σ ci pred bs : option (term * list term) :=
  match lookup_inductive Σ ci.(ci_ind) with 
  | None => None 
  | Some (mbody, body) =>
    (* Add abstractions to the predicate. *)
    let pred_ctx := case_predicate_context ci.(ci_ind) mbody body pred in
    let pred_term := it_mkLambda_or_LetIn pred_ctx pred.(preturn) in 
    (* Add abstractions to each branch. *)
    let bs_terms := 
      map2 
        (fun b cbody =>
          let b_ctx := case_branch_context ci.(ci_ind) mbody cbody pred b in
          it_mkLambda_or_LetIn b_ctx b.(bbody))
        bs
        body.(ind_ctors)
    in
    (* Return the updated predicate and branches. *)
    Some (pred_term, bs_terms)
  end.

Section EqTermGen.
Context `{checker_flags} (φ : universes_graph).
Context (on_subterms : conv_pb -> term -> term -> bool).

(** [eq_term_gen pb t t'] compares [t] and [t'] for conversion (if [pb] is Conv)
    or cumulativity (if [pb] is Cumul).
    It compares the head-constructors of [t] and [t'] without reducing, 
    and uses [on_subterms] to compare subterms. *)
Definition eq_term_gen pb (t t' : term) : bool :=
  match t, t' with 
  (* Type-Same *)
  | tSort s, tSort s' =>
    match pb with 
    | Conv => check_eqb_sort φ s s' 
    | Cumul => check_leqb_sort φ s s'
    end
  (* Lam-Same *)
  | tLambda x ty body, tLambda _ ty' body' =>
    on_subterms Conv ty ty' && on_subterms pb body body'
  (* Prod-Same *)
  | tProd x a b, tProd _ a' b' =>
    on_subterms Conv a a' && on_subterms pb b b'
  (* Let-Same *)
  | tLetIn x def ty body, tLetIn _ def' ty' body' =>
    on_subterms Conv def def' && on_subterms pb body body'
  (* Rel-Same *)
  | tRel n, tRel n' => n == n'
  (* Var-Same *)
  | tVar v, tVar v' => v == v'
  (* Const-Same *)
  | tConst c u, tConst c' u' => 
    (c == c') && eqb_univ_instance φ u u'
  (* Ind-Same *)
  | tInd ind u, tInd ind' u' => 
    (ind == ind') && eqb_univ_instance φ u u'
  (* Construct-Same *)
  | tConstruct ind n u, tConstruct ind' n' u' =>
    (ind == ind') && (n == n') && eqb_univ_instance φ u u'
  (* Proj-Same *)
  | tProj p t, tProj p' t' =>
    (p == p') && on_subterms Conv t t' 
  (* (Co)Fix-Same *)
  | tFix defs n, tFix defs' n'
  | tCoFix defs n, tCoFix defs' n' =>
    (n == n') && 
    (* First compare the types. *)
    forallb2 (fun d d' => on_subterms Conv d.(dtype) d'.(dtype)) defs defs' &&
    (* Then compare the bodies. *)
    forallb2 (fun d d' => on_subterms Conv d.(dbody) d.(dbody)) defs defs'
  (* Case-Same *)
  | tCase ci pred x bs, tCase ci' pred' x' bs' =>
    (ci == ci') && 
    eqb_predicate (eqb_univ_instance φ) (on_subterms Conv) pred pred' &&
    on_subterms Conv x x' &&
    forallb2 (fun b b' => on_subterms Conv b.(bbody) b'.(bbody)) bs bs'
  (* Int-Same *)
  | tInt x, tInt x' => x == x'
  (* Float-Same *)
  | tFloat x, tFloat x' => x == x'
  (* String-Same *)
  | tString s, tString s' =>
    match PrimString.compare s s' with 
    | Eq => true 
    | _ => false
    end
  (* Array-Same *)
  | tArray l ts t1 t2, tArray l' ts' t1' t2' =>
    eqb_univ_instance φ [l] [l'] &&
    forallb2 (on_subterms Conv) (t1 :: t2 :: ts) (t1' :: t2' :: ts')
  | _, _ => false
  end.

End EqTermGen.

Section EqTermCtx.
Context `{checker_flags} (Σ : global_env) (φ : universes_graph).
Context (on_subterms : context -> conv_pb -> term -> term -> bool).

(** Helper function to compare case predicates. *)
Definition on_predicates ind Γ pred pred' : bool :=
  eqb_univ_instance φ pred.(puinst) pred'.(puinst) &&
  match lookup_inductive Σ ind with 
  | Some (mbody, ibody) =>
    let Γ_pred := Γ ,,, case_predicate_context ind mbody ibody pred in
    on_subterms Γ_pred Conv pred.(preturn) pred'.(preturn)
  | None => false 
  end.

(** Helper function to compare case branches. *)
Definition on_branches ind i pred Γ branch branch' : bool :=
  match lookup_constructor Σ ind i with 
  | Some (mbody, ibody, cbody) =>
    let Γ_branch := Γ ,,, case_branch_context ind mbody cbody pred branch in
    on_subterms Γ_branch Conv branch.(bbody) branch'.(bbody)
  | None => false 
  end.

(** Same as [eq_term_ctx], but it threads a local context. 
    This requires access to a global environment (to rebuild the context 
    of case predicates and branches). *)
Definition eq_term_ctx Γ pb (t t' : term) : bool :=
  match t, t' with 
  (* Type-Same *)
  | tSort s, tSort s' =>
    match pb with 
    | Conv => check_eqb_sort φ s s' 
    | Cumul => check_leqb_sort φ s s'
    end
  (* Lam-Same *)
  | tLambda x ty body, tLambda _ ty' body' =>
    on_subterms Γ Conv ty ty' && on_subterms (Γ ,, vass x ty) pb body body'
  (* Prod-Same *)
  | tProd x a b, tProd _ a' b' =>
    on_subterms Γ Conv a a' && on_subterms (Γ ,, vass x a) pb b b'
  (* Let-Same *)
  | tLetIn x def ty body, tLetIn _ def' ty' body' =>
    on_subterms Γ Conv def def' && on_subterms (Γ ,, vdef x def ty) pb body body'
  (* Rel-Same *)
  | tRel n, tRel n' => n == n'
  (* Var-Same *)
  | tVar v, tVar v' => v == v'
  (* Const-Same *)
  | tConst c u, tConst c' u' => 
    (c == c') && eqb_univ_instance φ u u'
  (* Ind-Same *)
  | tInd ind u, tInd ind' u' => 
    (ind == ind') && eqb_univ_instance φ u u'
  (* Construct-Same *)
  | tConstruct ind n u, tConstruct ind' n' u' =>
    (ind == ind') && (n == n') && eqb_univ_instance φ u u'
  (* Proj-Same *)
  | tProj p t, tProj p' t' =>
    (p == p') && on_subterms Γ Conv t t' 
  (* (Co)Fix-Same *)
  | tFix defs n, tFix defs' n'
  | tCoFix defs n, tCoFix defs' n' =>
    (n == n') && 
    (* First compare the types. *)
    forallb2 (fun d d' => on_subterms Γ Conv d.(dtype) d'.(dtype)) defs defs' &&
    (* Then compare the bodies in an extended context. *)
    let Γ_fix := Γ ,,, fix_context defs in
    forallb2 (fun d d' => on_subterms Γ_fix Conv d.(dbody) d.(dbody)) defs defs'
  (* Case-Same *)
  | tCase ci pred x bs, tCase ci' pred' x' bs' =>
    (ci == ci') && 
    on_subterms Γ Conv x x' &&
    on_predicates ci.(ci_ind) Γ pred pred' &&
    forallb (fun '(i, b, b') => on_branches ci.(ci_ind) i pred Γ b b') (map2i (fun i b b' => (i, b, b')) bs bs')
  (* Int-Same *)
  | tInt x, tInt x' => x == x'
  (* Float-Same *)
  | tFloat x, tFloat x' => x == x'
  (* String-Same *)
  | tString s, tString s' =>
    match PrimString.compare s s' with 
    | Eq => true 
    | _ => false
    end
  (* Array-Same *)
  | tArray l ts t1 t2, tArray l' ts' t1' t2' =>
    eqb_univ_instance φ [l] [l'] &&
    forallb2 (on_subterms Γ Conv) (t1 :: t2 :: ts) (t1' :: t2' :: ts')
  | _, _ => false
  end.

End EqTermCtx.

(** Equality of terms modulo :
    - alpha equivalence.
    - universe equivalence/cumulativity. *)
Fixpoint eq_term `{checker_flags} φ pb t u : bool := 
  eq_term_gen φ (eq_term φ) pb t u.

(** Equality of terms modulo :
    - alpha equivalence.
    - universe equivalence/cumulativity.
    - evar expansion. *)
Fixpoint eq_term_evars `{checker_flags} evm pb t u : bool := 
  let on_subterms pb t u :=
    eq_term_evars evm pb (whd_evars evm t) (whd_evars evm u)
  in
  eq_term_gen (EvarMap.evm_universes evm) on_subterms pb (whd_evars evm t) (whd_evars evm u).

(** * Reduction. *)

(** Reduction flags control which reduction rules to apply. *)
Module RedFlags.

Record t := mk
  { (** Should we reduce beta-redexes (function applications) ? *)
    beta : bool
  ; (** Should we substitute local variable bindings (let-in) ?  *)
    zeta : bool
  ; (** Should we reduce cases ? *)
    case : bool
  ; (** Should we reduce fixpoints ? *)
    fix_ : bool
  ; (** Should we reduce co-fixpoints ? *)
    cofix_ : bool
  ; (** Should we remove explicit type-casts ? *)
    erase_cast : bool
  ; (** Should we replace tRels by their definition ? *)
    delta_rel : bool
  ; (** Should we replace tVars by their definition ? *)
    delta_var : bool
  ; (** Should we replace tConsts by their definition ? *)
    delta_const : bool
  ; (** Should we replace tEvars by their definition ? *)
    delta_evar : bool }.

(** Reduce everything. *)
Definition all : t := 
  mk true true true true true true true true true true.

End RedFlags.

Section Reduce.
Context (flags : RedFlags.t) (evm : EvarMap.t) (Σ : global_env) (Δ : named_context).

Definition zip (t : term * list term) := mkApps t.1 t.2.

(** A helper function to implement weak-head reduction.
    It is implemented as a standard stack machine. *)
Fixpoint weak_head_stack (Γ : context) (t : term) (stack : list term) {struct t} : term * list term :=
  match t with
  
  (* Accumulate arguments. *)
  | tApp f args => weak_head_stack Γ f (args ++ stack)

  (* Evar-unfolding *)
  | tEvar ev inst =>
    if RedFlags.delta_evar flags then
      match EvarMap.lookup evm ev with 
      | Some {| ev_nctx := nctx ; ev_def := Some def |} => 
        let inst := map (fun '(id, _) => tVar id) nctx in 
        weak_head_stack Γ (instantiate_evar nctx inst def) stack
      | _ => (t, stack)
      end
    else (t, stack)

  (* Rel-unfolding *)  
  | tRel n =>
    if RedFlags.delta_rel flags then
      match nth_error Γ n with
      | Some {| decl_body := Some body |} => weak_head_stack Γ (lift0 (S n) body) stack
      | _ => ret (t, stack)
      end
    else ret (t, stack)

  (* Var-unfolding *) 
  | tVar v =>
    if RedFlags.delta_var flags then 
      match lookup_nctx Δ v with 
      | Some {| decl_body := Some body |} => weak_head_stack Γ body stack
      | _ => ret (t, stack)
      end
    else ret (t, stack)

  (* Const-unfolding *)
  | tConst c u =>
    if RedFlags.delta_const flags then
      match lookup_env Σ c with
      | Some (ConstantDecl {| cst_body := Some body |}) =>
        let body' := subst_instance u body in
        weak_head_stack Γ body' stack
      | _ => ret (t, stack)
      end
    else ret (t, stack)

  (* Zeta-reduction *)
  | tLetIn _ b _ c =>
    if RedFlags.zeta flags then 
      weak_head_stack Γ (subst10 b c) stack
    else ret (t, stack)

  (* Beta-reduction *)
  | tLambda na ty body =>
    if RedFlags.beta flags then
      match stack with
      | a :: args' => weak_head_stack Γ (subst10 a body) args'
      | _ => (t, stack)
      end
    else (t, stack)

  (* Match-reduction *)
  | tCase ci p c brs =>
    if RedFlags.case flags then
      match weak_head_stack Γ c [] with
      | (tConstruct ind ctor_idx _, args) =>
        match nth_error brs ctor_idx, lookup_constructor Σ ind ctor_idx with
        | Some br, Some (mdecl, _, cdecl) =>
          let bctx := case_branch_context ind mdecl cdecl p br in
          weak_head_stack Γ (iota_red ci.(ci_npar) args bctx br) stack
        | _, _ => (t, stack)
        end
      | c => (tCase ci p (zip c) brs, stack)
      end
    else (t, stack)

  (* Fix-reduction *)
  | tFix mfix idx =>
    if RedFlags.fix_ flags then
      match unfold_fix mfix idx with 
      | Some (narg, fn) =>
        match List.nth_error stack narg with
        | Some c =>
          match weak_head_stack Γ c [] with
          | (tConstruct _ _ _, _) => weak_head_stack Γ fn stack
          | _ => (t, stack)
          end
        | _ => (t, stack)
        end
      | None => (t, stack)
      end
    else (t, stack)

  (* CoFix-reduction *)
  | tCoFix mfix idx =>
    if RedFlags.cofix_ flags then 
      match unfold_fix mfix idx with 
      | Some (narg, fn) => weak_head_stack Γ fn stack
      | None => (t, stack)
      end
    else (t, stack)

  (* Cast-erasure *)
  | tCast c _ _ => 
    if RedFlags.erase_cast flags then 
      weak_head_stack Γ c stack
    else (t, stack)

  | _ => ret (t, stack)

  end.

(** Weak-head reduce a term.
    It implements weak-head call-by-need reduction, i.e. does not reduce under binders. *)
Definition weak_head_reduce (Γ : context) (t : term) : term :=
  let (f, args) := weak_head_stack Γ t [] in mkApps f args.

Definition rebuild_case_predicate_ctx ind (p : predicate term) : context :=
  match lookup_inductive Σ ind with
  | Some (mib, oib) => case_predicate_context ind mib oib p
  | None => []
  end.

Definition map_context_with_binders (f : context -> term -> term) (c : context) Γ : context :=
  fold_left (fun acc decl => map_decl (f (Γ ,,, acc)) decl :: acc) (rev c) [].

Definition map_predicate_with_binders (f : context -> term -> term) Γ ind (p : predicate term) :=
  let pctx := rebuild_case_predicate_ctx ind p in
  let Γ' := map_context_with_binders f pctx Γ in
  {| pparams := map (f Γ) p.(pparams);
     puinst := p.(puinst);
     pcontext := p.(pcontext);
     preturn := f Γ' (preturn p) |}.

Definition rebuild_case_branch_ctx ind i p br :=
  match lookup_constructor Σ ind i with
  | None => []
  | Some (mib, _, cdecl) => case_branch_context ind mib cdecl p br
  end.

Definition map_case_branch_with_binders ind i (f : context -> term -> term) Γ p br :=
  let ctx := rebuild_case_branch_ctx ind i p br in
  map_branch (f (Γ ,,, ctx)) br.

Definition map_constr_with_binders (f : context -> term -> term) Γ (t : term) : term :=
  match t with
  | tRel i => t
  | tEvar ev args => tEvar ev (List.map (f Γ) args)
  | tLambda na T M => tLambda na (f Γ T) (f Γ M)
  | tApp u v => tApp (f Γ u) (List.map (f Γ) v)
  | tProd na A B =>
    let A' := f Γ A in
    tProd na A' (f (Γ ,, vass na A') B)
  | tCast c kind t => tCast (f Γ c) kind (f Γ t)
  | tLetIn na b t c =>
    let b' := f Γ b in
    let t' := f Γ t in
    tLetIn na b' t' (f (Γ ,, vdef na b' t') c)
  | tCase ci p c brs =>
    let p' := map_predicate_with_binders f Γ ci.(ci_ind) p in
    let brs' := mapi (fun i x => map_case_branch_with_binders ci.(ci_ind) i f Γ p' x) brs in
    tCase ci p' (f Γ c) brs'
  | tProj p c => tProj p (f Γ c)
  | tFix mfix idx =>
    let Γ' := Γ ,,, fix_context mfix in
    let mfix' := List.map (map_def (f Γ) (f Γ')) mfix in
    tFix mfix' idx
  | tCoFix mfix k =>
    let Γ' := Γ ,,, fix_context mfix in
    let mfix' := List.map (map_def (f Γ) (f Γ')) mfix in
    tCoFix mfix' k
  | x => x
  end.

(** [reduce Γ t] reduces the term [t] in context [Γ]. 
    It implements strong call-by-need reduction, i.e. it reduces under binders. *)
Fixpoint reduce (Γ : context) (t : term) {struct t} : term :=
  let t := weak_head_reduce Γ t in
  map_constr_with_binders reduce Γ t.

End Reduce.

Section ThetaReduce.
Context (evm : EvarMap.t) (Σ : global_env) (Δ : named_context).

(** [whd_theta_stack Γ t stack] implements a specific strategy for weak-head reducing [t stack],
    which is used e.g. during conversion checking and unification.

    It weak-head reduces using all rules except variable and constant unfolding, and additionally tries to reduce 
    match scrutinees and fixpoint recursive arguments using _all_ rules (including unfolding)
    if it allows a iota reduction to trigger.
    
    As with [whd_reduce_stack] it uses a weak call-by-need startegy. *)
Definition whd_theta_stack (Γ : context) (t : term) (args : list term) : term * list term :=
  (* We call [whd_reduce_stack RedFlags.all] inside match scrutinees 
     and fixpoint recursive arguments. *)
  let fix loop (t : term) (args : list term) {struct t} := 
    match (t, args) with
    
    (* Evar-unfolding *)
    | (tEvar ev inst, args) =>
      match EvarMap.lookup evm ev with 
      | Some {| ev_nctx := nctx ; ev_def := Some def |} => 
        let inst := map (fun '(id, _) => tVar id) nctx in 
        loop (instantiate_evar nctx inst def) args
      | _ => (t, args)
      end

    (* Beta reduction. *)
    | (tLambda _ _ body, arg :: args) => loop (subst0 [arg] body) args
    
    (* Zeta-reduction. *)
    | (tLetIn _ def _ body, args) => loop (subst0 [def] body) args
    
    (* Cast-erasure. *)
    | (tCast c _ _, args) => loop c args

    (* Match-reduction. *)
    | (tCase ci pred x bs, args) =>
      (* If the (fully reduced) scrutinee is a constructor, reduce the match. *)
      match weak_head_stack RedFlags.all evm Σ Δ Γ x [] with
      | (tConstruct ind n _, x_args) =>
        match nth_error bs n, lookup_constructor Σ ind n with
        | Some branch, Some (mbody, _, cbody) =>
          let bctx := case_branch_context ind mbody cbody pred branch in
          loop (iota_red ci.(ci_npar) x_args bctx branch) args
        | _, _ => (tCase ci pred x bs, args)
        end
      | _ => (tCase ci pred x bs, args)
      end
  
    (* Fix-reduction. *)
    | (tFix mfix n, args) =>
      (* Get the body of the fixpoint. *)
      match unfold_fix mfix n with 
      | Some (rec_idx, fix_body) =>
        match chop rec_idx args with 
        (* We have enough arguments to reduce. *)
        | (args1, ra :: args2) =>
          (* If the (reduced) recursive fixpoint argument is a constructor,
             reduce the fixpoint. *)
          match weak_head_stack RedFlags.all evm Σ Δ Γ ra [] with 
          | (tConstruct _ _ _ as ra, ra_args) => 
            loop fix_body (args1 ++ mkApps ra ra_args :: args2)
          | _ => (tFix mfix n, args)
          end
        (* We don't have enough arguments to reduce. *)
        | (args, []) => (tFix mfix n, args)
        end 
      | None => (tFix mfix n, args)
      end
  
    (* CoFix-Reduction. *)
    | (tCoFix mfix n, args) =>
      (* Get the body of the co-fixpoint. *)
      match unfold_fix mfix n with 
      | Some (_, cofix_body) => 
        (* For co-fixpoints we don't need to wait for the recursive argument to be a constructor. *)
        loop cofix_body args 
      | None => (tFix mfix n, args)
      end
  
    (* No applicable rule. *)
    | t => t
    end
  in
  loop t args.
      
End ThetaReduce.

(** Conversion. *)

Section Conversion.
Context `{checker_flags} (flags : RedFlags.t) (evm : EvarMap.t) (Σ : global_env) (Δ : named_context).

(** [check_conv pb t t'] checks that [t = t'] modulo conversion (if [pb] is Conv)
    or cumulativity (if [pb] is Cumul). It uses all reduction rules. 
    
    The current implementation is not very efficient : we fully weak-head reduce 
    at each step. A better solution might be to first reduce using all rules except 
    unfolding (we would probably use [whd_theta_stack]), and carefully unfold 
    constants when needed, but this requires backtracking so one has to take extra care 
    to ensure it is indeed more efficient. 
    An even better solution would be to use delayed substitutions when reducing.
    Anyways optimizing this function does not seem worth the effort for the moment. *)
Fixpoint check_conv (Γ : context) (pb : conv_pb) (t t' : term) {struct pb} : bool :=
  let red t := weak_head_reduce flags evm Σ Δ Γ t in
  eq_term_ctx Σ (EvarMap.evm_universes evm) 
    (fun Γ pb t t' => check_conv Γ pb (red t) (red t')) Γ pb (red t) (red t').

End Conversion.

(** * Typing. *)

Inductive type_error :=
| UnboundRel (n : nat)
| UnboundVar (id : string)
| UnboundMeta (m : nat)
| UnboundEvar (ev : nat)
| UndeclaredConstant (c : kername)
| UndeclaredInductive (c : inductive)
| UndeclaredConstructor (c : inductive) (i : nat)
| UndeclaredProjection (p : projection)
| NotConvertible (Γ : context) (t u t' u' : term)
| NotASort (t : term)
| NotAProduct (t t' : term)
| NotAnInductive (t : term)
| IllFormedFix (m : mfixpoint term) (i : nat)
| IllFormedProjection (p : projection) (t : term)
| UnsatisfiedConstraints (c : ConstraintSet.t)
| UnsatisfiableConstraints (c : ConstraintSet.t)
| NotSupported (s : string).

Definition string_of_type_error (e : type_error) : string :=
  match e with
  | UnboundRel n => "Unboound rel " ^ string_of_nat n
  | UnboundVar id => "Unbound var " ^ id
  | UnboundMeta m => "Unbound meta " ^ string_of_nat m
  | UnboundEvar ev => "Unbound evar " ^ string_of_nat ev
  | UndeclaredConstant c => "Undeclared constant " ^ string_of_kername c
  | UndeclaredInductive c => "Undeclared inductive " ^ string_of_kername (inductive_mind c)
  | UndeclaredConstructor c i => "Undeclared constructor for inductive " ^ string_of_kername (inductive_mind c)
  | UndeclaredProjection p => "Undeclared projection for for inductive " ^ string_of_kername (inductive_mind p.(proj_ind))
  | NotConvertible Γ t u t' u' => "Terms are not convertible: " ^
      string_of_term t ^ " " ^ string_of_term u ^ " after reduction: " ^
      string_of_term t' ^ " " ^ string_of_term u'
  | NotASort t => "Not a sort"
  | NotAProduct t t' => "Not a product"
  | NotAnInductive t => "Not an inductive"
  | IllFormedFix m i => "Ill-formed recursive definition"
  | IllFormedProjection p t => "Ill-formed primitive projection"
  | UnsatisfiedConstraints c => "Unsatisfied constraints"
  | UnsatisfiableConstraints c => "Unsatisfiable constraints"
  | NotSupported s => s ^ " are not supported"
  end.

(** Typing and retyping functions return a [typing_result]. *)
Inductive typing_result (A : Type) :=
| Checked (a : A)
| TypeError (t : type_error).
Global Arguments Checked {A} a.
Global Arguments TypeError {A} t.

Global Instance typing_monad : Monad typing_result :=
{| ret A a := Checked a ;
   bind A B m f :=
     match m with
     | Checked a => f a
     | TypeError t => TypeError t
     end
|}.

Global Instance monad_exc : MonadExc type_error typing_result :=
{ raise A e := TypeError e;
  catch A m f :=
    match m with
    | Checked a => m
    | TypeError t => f t
    end
}.

Section Lookups.
Context (Σ : global_env).

Definition polymorphic_constraints u :=
  match u with
  | Monomorphic_ctx => ConstraintSet.empty
  | Polymorphic_ctx ctx => (AUContext.repr ctx).2.2
  end.

Definition lookup_constant_type cst u :=
  match lookup_env Σ cst with
  | Some (ConstantDecl {| cst_type := ty; cst_universes := uctx |}) =>
    ret (subst_instance u ty)
  |  _ => raise (UndeclaredConstant cst)
  end.

Definition lookup_constant_type_cstrs cst u :=
  match lookup_env Σ cst with
  | Some (ConstantDecl {| cst_type := ty; cst_universes := uctx |}) =>
    let cstrs := polymorphic_constraints uctx in
    ret (subst_instance u ty, subst_instance_cstrs u cstrs)
    |  _ => raise (UndeclaredConstant cst)
  end.

Definition lookup_ind_decl ind i :=
  match lookup_env Σ ind with
  | Some (InductiveDecl mdecl) =>
    match nth_error mdecl.(ind_bodies) i with
    | Some body => ret (mdecl, body)
    | None => raise (UndeclaredInductive (mkInd ind i))
    end
  | _ => raise (UndeclaredInductive (mkInd ind i))
  end.

Definition lookup_ind_type ind i (u : list Level.t) :=
  res <- lookup_ind_decl ind i ;;
  ret (subst_instance u (snd res).(ind_type)).

Definition lookup_ind_type_cstrs ind i (u : list Level.t) :=
  '(mib, body) <- lookup_ind_decl ind i ;;
  let uctx := mib.(ind_universes) in
  let cstrs := polymorphic_constraints uctx in
  ret (subst_instance u body.(ind_type), subst_instance_cstrs u cstrs).

Definition lookup_constructor_decl ind i k :=
  '(mib, body) <- lookup_ind_decl ind i;;
  match nth_error body.(ind_ctors) k with
  | Some cdecl => ret (mib, cdecl)
  | None => raise (UndeclaredConstructor (mkInd ind i) k)
  end.

Definition lookup_constructor_type ind i k u :=
  '(mib, cdecl) <- lookup_constructor_decl ind i k ;;
  ret (subst0 (inds ind u mib.(ind_bodies)) (subst_instance u cdecl.(cstr_type))).

Definition lookup_constructor_type_cstrs ind i k u :=
  '(mib, cdecl) <- lookup_constructor_decl ind i k ;;
  let cstrs := polymorphic_constraints mib.(ind_universes) in
  ret (subst0 (inds ind u mib.(ind_bodies)) (subst_instance u cdecl.(cstr_type)),
      subst_instance_cstrs u cstrs).

Definition lookup_projection_type p c args u :=
  match lookup_projection Σ p with
  | Some (_, _, _, pbody) =>
    ret (subst0 (c :: rev args) (subst_instance u pbody.(proj_type)))
  | None => raise (UndeclaredProjection p)
  end.

End Lookups.

Section Typing.
Context `{checker_flags} (evm : EvarMap.t) (Σ : global_env) (Δ : named_context).

(** [reduce_to_sort t] weak-head reduces [t] to a sort. *)
Definition reduce_to_sort Γ (t : term) : typing_result sort :=
  match weak_head_reduce RedFlags.all evm Σ Δ Γ t with
  | tSort s => ret s
  | _ => raise (NotASort t)
  end.

(** [reduce_to_prod t] weak-head reduces [t] to a product. *)
Definition reduce_to_prod Γ (t : term) : typing_result (aname * term * term) :=
  match weak_head_reduce RedFlags.all evm Σ Δ Γ t with
  | tProd binder a b => ret (binder, a, b)
  | t' => raise (NotAProduct t t')
  end.

(** [reduce_to_ind t] weak-head reduces [t] to an inductive applied to arguments. *)
Definition reduce_to_ind Γ (t : term) : typing_result (inductive * Instance.t * list term) :=
  match weak_head_stack RedFlags.all evm Σ Δ Γ t [] with
  | (tInd i u, args) => ret (i, u, args)
  | _ => raise (NotAnInductive t)
  end.

Section InferAux.
Variable (infer : context -> term -> typing_result term).
  
Definition infer_cumul Γ t t' : typing_result unit :=
  tx <- infer Γ t ;;
  if check_conv RedFlags.all evm Σ Δ Γ Cumul tx t' then ret tt 
  else raise (NotConvertible Γ tx t' tx t').

Fixpoint infer_spine (Γ : context) (ty : term) (l : list term) {struct l} : typing_result term :=
  match l with
  | [] => ret ty
  | x :: xs =>
     mlet '(_, a1, b1) <- reduce_to_prod Γ ty ;;
     infer_cumul Γ x a1 ;;
     infer_spine Γ (subst10 x b1) xs
  end.

Definition infer_type Γ t :=
  tx <- infer Γ t ;;
  reduce_to_sort Γ tx.

End InferAux.

Definition check_consistent_constraints cstrs :=
  if check_constraints (EvarMap.evm_universes evm) cstrs then ret tt
  else raise (UnsatisfiedConstraints cstrs).

(** [infer Γ t] checks [t] is well-typed in local context Γ and returns its type. *)
Fixpoint infer (Γ : context) (t : term) : typing_result term :=
  match t with
  | tRel n =>
    match nth_error Γ n with
    | Some d => ret (lift0 (S n) d.(decl_type))
    | None => raise (UnboundRel n)
    end

  | tVar n => 
    match lookup_nctx Δ n with 
    | Some d => ret d.(decl_type)
    | None => raise (UnboundVar n)
    end
      
  | tEvar ev args => 
    match EvarMap.lookup evm ev with 
    | Some entry =>
      let inst := map (fun '(id, _) => tVar id) entry.(ev_nctx) in
      ret (instantiate_evar entry.(ev_nctx) inst entry.(ev_concl))
    | None => raise (UnboundEvar ev)
    end

  | tSort s => ret (tSort (Sort.super s))

  | tCast c k t =>
    infer_type infer Γ t ;;
    infer_cumul infer Γ c t ;;
    ret t

  | tProd n t b =>
    s1 <- infer_type infer Γ t ;;
    s2 <- infer_type infer (Γ ,, vass n t) b ;;
    ret (tSort (Sort.sort_of_product s1 s2)) 

  | tLambda n t b =>
    infer_type infer Γ t ;;
    t2 <- infer (Γ ,, vass n t) b ;;
    ret (tProd n t t2)

  | tLetIn n b b_ty b' =>
    infer_type infer Γ b_ty ;;
     infer_cumul infer Γ b b_ty ;;
     b'_ty <- infer (Γ ,, vdef n b b_ty) b' ;;
     ret (tLetIn n b b_ty b'_ty)

  | tApp t l =>
    t_ty <- infer Γ t ;;
    infer_spine infer Γ t_ty l

  | tConst cst u =>
    tycstrs <- lookup_constant_type_cstrs Σ cst u ;;
    let '(ty, cstrs) := tycstrs in
    check_consistent_constraints cstrs;;
    ret ty

  | tInd (mkInd ind i) u =>
    tycstrs <- lookup_ind_type_cstrs Σ ind i u;;
    let '(ty, cstrs) := tycstrs in
    check_consistent_constraints cstrs;;
    ret ty

  | tConstruct (mkInd ind i) k u =>
    tycstrs <- lookup_constructor_type_cstrs Σ ind i k u ;;
    let '(ty, cstrs) := tycstrs in
    check_consistent_constraints cstrs;;
    ret ty

  | tCase ci p c brs =>
    ty <- infer Γ c ;;
    indargs <- reduce_to_ind Γ ty ;;
    (* TODO check branches *)
    let '(ind, u, args) := indargs in
    if eq_inductive ind ci.(ci_ind) then
      let pctx := rebuild_case_predicate_ctx Σ ind p in
      let ptm := it_mkLambda_or_LetIn pctx p.(preturn) in
      ret (tApp ptm (List.skipn ci.(ci_npar) args ++ [c]))
    else
      let ind1 := tInd ind u in
      let ind2 := tInd ci.(ci_ind) u in
      raise (NotConvertible Γ ind1 ind2 ind1 ind2)

  | tProj p c =>
    ty <- infer Γ c ;;
    '(ind, u, args) <- reduce_to_ind Γ ty ;;
    match lookup_projection Σ p with 
    | Some (mbody, ibody, _, pbody) =>
      if (eq_inductive ind p.(proj_ind)) &&
         (#|args| == p.(proj_npars)) && 
         (mbody.(ind_npars) == p.(proj_npars)) &&
         (nth_error ibody.(ind_projs) p.(proj_arg) == Some pbody) 
      then ret (subst0 (c :: rev args) (subst_instance u pbody.(proj_type)))
      else raise (IllFormedProjection p c)
    | None => raise (UndeclaredProjection p)
    end
    
  | tFix mfix n =>
    match nth_error mfix n with
    | Some f => ret f.(dtype)
    | None => raise (IllFormedFix mfix n)
    end

  | tCoFix mfix n =>
    match nth_error mfix n with
    | Some f => ret f.(dtype)
    | None => raise (IllFormedFix mfix n)
    end

  | tInt _ | tFloat _ | tString _ | tArray _ _ _ _ => raise (NotSupported "primitive types")
  end.
  
(** [check t ty] checks that [t] has type [ty], assuming [ty] is itself well-typed. *)
Definition check (Γ : context) (t : term) (ty : term) : typing_result unit :=
  infer_type infer Γ ty ;;
  infer_cumul infer Γ t ty.

(** Same as [check] but returns a boolean. *)
Definition typechecking (Γ : context) (t ty : term) : bool :=
  match check Γ t ty with
  | Checked _ => true
  | TypeError _ => false
  end.

End Typing.

Arguments bind _ _ _ _ ! _.

Fixpoint fresh id (env : global_declarations) : bool :=
  match env with
  | nil => true
  | cons g env => negb (g.1 == id) && fresh id env
  end.

Section Checker.
Context `{checker_flags}.

Inductive env_error :=
| IllFormedDecl (e : string) (e : type_error)
| AlreadyDeclared (id : string).

Inductive EnvCheck (A : Type) :=
| CorrectDecl (a : A)
| EnvError (e : env_error).
Global Arguments EnvError {A} e.
Global Arguments CorrectDecl {A} a.

Instance envcheck_monad : Monad EnvCheck :=
{| ret A a := CorrectDecl a ;
   bind A B m f :=
     match m with
     | CorrectDecl a => f a
     | EnvError e => EnvError e
     end
|}.

Definition wrap_error {A} (id : string) (check : typing_result A) : EnvCheck A :=
  match check with
  | Checked a => CorrectDecl a
  | TypeError e => EnvError (IllFormedDecl id e)
  end.

Definition check_wf_type id Σ (G : universes_graph) t :=
  let evm := EvarMap.from_ugraph G in
  wrap_error id (infer_type evm Σ [] (infer evm Σ []) [] t) ;; ret tt.

Definition check_wf_judgement id Σ (G : universes_graph) t ty :=
  let evm := EvarMap.from_ugraph G in
  wrap_error id (check evm Σ [] [] t ty) ;; ret tt.

Definition infer_term Σ (G : universes_graph) t :=
  let evm := EvarMap.from_ugraph G in
  wrap_error "" (infer evm Σ [] [] t).

Definition check_wf_decl Σ (G : universes_graph) kn (g : global_decl) : EnvCheck unit :=
  let evm := EvarMap.from_ugraph G in
  match g with
  | ConstantDecl cst =>
    match cst.(cst_body) with
    | Some term => check_wf_judgement (string_of_kername kn) Σ G term cst.(cst_type)
    | None => check_wf_type (string_of_kername kn) Σ G cst.(cst_type)
    end
  | InductiveDecl inds =>
    List.fold_left (fun acc body =>
                      acc ;; check_wf_type body.(ind_name) Σ G body.(ind_type))
                   inds.(ind_bodies) (ret tt)
  end.

Fixpoint check_fresh id (env : global_declarations) : EnvCheck unit :=
  match env with
  | [] => ret tt
  | g :: env =>
    check_fresh id env;;
    if id == g.1 then
      EnvError (AlreadyDeclared (string_of_kername id))
    else ret tt
  end.

Definition add_gc_constraints ctrs  (G : universes_graph) : universes_graph
  := (G.1.1,  GoodConstraintSet.fold
                (fun ctr => wGraph.EdgeSet.add (edge_of_constraint ctr)) ctrs G.1.2,
      G.2).

Fixpoint check_wf_declarations (univs : ContextSet.t) (retro : Retroknowledge.t) (G : universes_graph) (g : global_declarations)
  : EnvCheck unit :=
  match g with
  | [] => ret tt
  | g :: env =>
    check_wf_declarations univs retro G env ;;
    check_wf_decl {| universes := univs; declarations := env; retroknowledge := retro |} G g.1 g.2 ;;
    check_fresh g.1 env ;;
    ret tt
  end.

Definition typecheck_program (p : program) : EnvCheck term :=
  let Σ := fst p in
  let '(univs, decls, retro) := (Σ.(universes), Σ.(declarations), Σ.(retroknowledge)) in
  match gc_of_constraints (snd univs) with
  | None => EnvError (IllFormedDecl "toplevel"
      (UnsatisfiableConstraints univs.2))
  | Some ctrs =>
    let G := add_gc_constraints ctrs init_graph in
    if wGraph.is_acyclic G then
      check_wf_declarations univs retro G decls ;;
      infer_term Σ G (snd p)
    else EnvError (IllFormedDecl "toplevel"
      (UnsatisfiableConstraints univs.2))
  end.

End Checker.

(** * Retyping. *)

Section Retyping.
Context `{checker_flags} (evm : EvarMap.t) (Σ : global_env) (Δ : named_context).

Section RetypeAux.
Variable (retype : context -> term -> typing_result term).

Fixpoint retype_spine (Γ : context) (ty : term) (l : list term) {struct l} : typing_result term :=
  match l with
  | nil => ret ty
  | cons x xs =>
     pi <- reduce_to_prod evm Σ Δ Γ ty ;;
     let '(_, b1) := pi in
     retype_spine Γ (subst10 x b1) xs
  end.

Definition retype_type Γ t :=
  tx <- retype Γ t ;;
  reduce_to_sort evm Σ Δ Γ tx.

End RetypeAux.

(** [retype t] infers the type of [t], assuming [t] is already well-typed. 
    This allows it to skip many checks and is thus much faster than [infer]. 
    A downside is that it does not always raise an error when [t] is ill-typed. *)
Fixpoint retype (Γ : context) (t : term) : typing_result term :=
  (* We don't call [whd_evars], but instead handle evars explicitly below.
     This way we avoid substituting in the body of an evar. *)
  match t with
  | tRel n =>
    match nth_error Γ n with
    | Some d => ret (lift0 (S n) d.(decl_type))
    | None => raise (UnboundRel n)
    end

  | tVar n => 
    match lookup_nctx Δ n with 
    | Some d => ret d.(decl_type)
    | None => raise (UnboundVar n)
    end
      
  | tEvar ev args =>
    match EvarMap.lookup evm ev with 
    | Some entry => ret (instantiate_evar entry.(ev_nctx) args entry.(ev_concl))
    | None => raise (UnboundEvar ev)
    end

  | tSort s => ret (tSort (Sort.super s))

  | tCast c k t => ret t

  | tProd n t b =>
    s1 <- retype_type retype Γ t ;;
    s2 <- retype_type retype (Γ ,, vass n t) b ;;
    ret (tSort (Sort.sort_of_product s1 s2))

  | tLambda n t b =>
    t2 <- retype (Γ ,, vass n t) b ;;
    ret (tProd n t t2)

  | tLetIn n b b_ty b' =>
    b'_ty <- retype (Γ ,, vdef n b b_ty) b' ;;
    ret (tLetIn n b b_ty b'_ty)

  | tApp t l =>
    t_ty <- retype Γ t ;;
    retype_spine Γ t_ty l

  | tConst cst u => lookup_constant_type Σ cst u

  | tInd (mkInd ind n) u => lookup_ind_type Σ ind n u
     
  | tConstruct (mkInd ind n) k u => lookup_constructor_type Σ ind n k u
      
  | tCase ci p c brs =>
    mlet ty <- retype Γ c ;;
    mlet '(ind, u, args) <- reduce_to_ind evm Σ Δ Γ ty ;;
    (* [rebuild_case_predicate_ctx] handles evars correctly,
       so no need to expand evars or thread the evar map. *)
    let pctx := rebuild_case_predicate_ctx Σ ind p in
    let ptm := it_mkLambda_or_LetIn pctx p.(preturn) in
    ret (mkApps ptm (List.skipn ci.(ci_npar) args ++ [c]))
    
  | tProj p c => 
    mlet ty <- retype Γ c ;;
    mlet '(_, u, args) <- reduce_to_ind evm Σ Δ Γ ty ;;
    lookup_projection_type Σ p c args u
    
  | tFix mfix n
  | tCoFix mfix n =>
    match nth_error mfix n with
    | Some f => ret f.(dtype)
    | None => raise (IllFormedFix mfix n)
    end

  | tInt _ | tFloat _ | tString _ | tArray _ _ _ _ => raise (NotSupported "primitive types")
  end.

End Retyping.