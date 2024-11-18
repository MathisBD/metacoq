(* Distributed under the terms of the MIT license. *)

(** This file defines a unification algorithm. It is intended for practical use 
    and is not verified. *)

From Coq.FSets Require Import FMapAVL.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import BasicAst uGraph config.
From MetaCoq.Template Require Import Ast AstUtils Checker.

Unset Guard Checking.

(** A convenient notation for function application, which saves many parentheses. *)
Notation "f $ x" := (f x) 
  (at level 10, x at level 100, right associativity, only parsing).

(** * Evar map. *)

(** An evar entry in the evar map. *)
Record evar_entry := 
  { ev_name : aname 
  ; ev_type : term 
  ; ev_def  : option term }.

Module EvarMap.

(** [NatMap T] are maps from natural numbers to elements of type [T]. *)
(** TODO : use binary numbers (or even primitive integers) instead of nats for the keys. *)
Module NatMap := FMapAVL.Make (OrderedTypeEx.Nat_as_OT).

(** An evar map is a map from evar identifiers to entries. *)
Definition t := NatMap.t evar_entry.

(** The empty evar map. *)
Definition empty : t := @NatMap.empty evar_entry.

(** [evar_type evm ev] retrieves the type of evar [ev] in the evar map [evm]. *)
Definition evar_type evm ev : option term :=
  match NatMap.find ev evm with 
  | None => None 
  | Some entry => Some entry.(ev_type)
  end. 

(** [evar_def evm ev] retrieves the definition of evar [ev] in the evar map [evm]. *)
Definition evar_def evm ev : option term :=
  match NatMap.find ev evm with 
  | None => None 
  | Some entry => entry.(ev_def)
  end.
  
Definition add evm ev entry : EvarMap.t :=
  NatMap.add ev entry evm.

(* Precondition : [ev] is present in [evm] but not defined. *)
Definition define evm ev def : EvarMap.t :=
  match NatMap.find ev evm with 
  | None => evm 
  | Some e => 
    let e : evar_entry := 
      {| ev_name := e.(ev_name) 
      ;  ev_type := e.(ev_type)
      ;  ev_def  := Some def |}
    in
    NatMap.add ev e evm
  end.

End EvarMap.

(** [nf_evars evm t] replaces all defined evars that appear in [t] 
    by their body. *)
Definition nf_evars (evm : EvarMap.t) (t : term) : term. 
(* TODO : use map_term. *)
Admitted.

(** [whd_evars evm t] expands evars just enough to expose the first 
    constructor which is not [tEvar] in [t]. *)
Fixpoint whd_evars (evm : EvarMap.t) (t : term) {struct t} : term :=
  match t with 
  | tEvar ev [] => 
    match EvarMap.evar_def evm ev with 
    | None => t 
    | Some def => whd_evars evm def
    end
  (* TODO : evars with an instance. *)
  | _ => t 
  end.

(** * Unification errors. *)

Inductive unif_error := 
  | NotSameHead : unif_error
  | UnivInconsistency : unif_error
  | InternalError : string -> unif_error.

(** Unification returns a [unif_result]. *)
Inductive unif_result A : Type := 
  (** [Success x] : unification succeeded with result [x] (typically the updated evar map). *)
  | Success : A -> unif_result A
  (** [UnifError err] : unification failed with error [err]. *)
  | UnifError : unif_error -> unif_result A.
Arguments Success {A}%_type_scope a.
Arguments UnifError {A}%_type_scope error.

(** * Logging. *)

(*Module Log.

(** A log element contains the data pertaining to a single unification problem. *)
Record elem := mkelem 
  { (** Did this unification problem succeed ? *) 
    le_success : bool  
  ; (** The first term we are unifying. *)
    le_t1 : term 
  ; (** The second term we are unifying. *)
    le_t2 : term
  ; (** The conversion problem. *)
    le_pb : conv_pb }.

Definition t := list elem.

(** The empty log. *)
Definition empty : t := [].

Definition concat (l l' : t) : t := List.app l l'.

End Log.*)

(** Monadic return. *)
Definition ret {A} (a : A) : unif_result A := Success a.

(** Monadic bind. *)
Definition bind {A} {B} (ma : unif_result A) (mf : A -> unif_result B) : unif_result B :=
  match ma with 
  | Success a => mf a 
  | UnifError err => UnifError err
  end.
Notation "'let*' x := c1 'in' c2" := (bind c1 (fun x => c2))
  (at level 100, x pattern, c1 at next level, right associativity).

(** Monadic alternative. *)
Definition msum {A} (x y : unif_result A) : unif_result A :=
  match x with 
  | Success _ => x 
  | UnifError _ => y
  end.
Notation "x <|> y" := (msum x y) (at level 85, right associativity).
   
(** Lift a value from the [option] monad to the [unif_result] monad.
    [None] is mapped to [UnifError (InternalError ...)]. *)
Definition lift_option {A} (x : option A) : unif_result A :=
  match x with 
  | Some x => ret x
  | None => UnifError (InternalError "lift_option")
  end.

(*Definition assert (msg : string) s (cond : bool) : state :=
  if cond then s 
  else (s.1, UnifFailure (AssertionFailure msg)).*)

(** * Unification algorithm. *)

Definition is_evar evm t : bool :=
  match whd_evars evm t with 
  | tEvar _ _ => true 
  | _ => false 
  end.

Fixpoint ise_list2 {A B} (f : A -> B -> EvarMap.t -> unif_result EvarMap.t) 
  (xs : list A) (ys : list B) (evm : EvarMap.t) : unif_result EvarMap.t :=
  match xs, ys with 
  | [], [] => ret evm 
  | x :: xs, y :: ys =>
    let* evm := f x y evm in ise_list2 f xs ys evm
  | _, _ => UnifError NotSameHead
  end.

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

Section Algorithm.
Context `{cf : checker_flags} (φ : universes_graph) (Σ : global_env) (Δ : named_context).

Implicit Types (pb : conv_pb) (Γ : context).

(** Main unification function. *)
Fixpoint unify pb Γ t t' evm {struct pb} : unif_result EvarMap.t :=
  if is_evar evm t || is_evar evm t'
  then try_instantiate pb Γ t t' evm
  else try_same_head pb Γ t t' evm

(** Precondition : either t or t' is an evar. *)
with try_instantiate pb Γ t t' evm {struct pb} : unif_result EvarMap.t :=
  match whd_evars evm t, whd_evars evm t' with 
  | tEvar ev [], tEvar ev' [] => 
    if ev == ev' 
    (* Meta-Same : TODO *)
    then ret evm   
    (* Try both Meta-InstL and Meta-InstR *)
    else instantiate pb Γ ev t' evm <|> instantiate pb Γ ev' t evm
  (* Meta-InstL *)
  | tEvar ev [], _ => instantiate pb Γ ev t' evm
  (* Meta-InstR *)
  | _, tEvar ev [] => instantiate pb Γ ev t evm
  | _, _ => UnifError (InternalError "try_instantiate : expected an evar")
  end

with instantiate pb Γ ev t evm {struct pb} : unif_result EvarMap.t :=
  (* Check the evar and t have the same type. *)
  let* t_ty := 
    match @Checker.infer cf default_fuel Σ φ Δ Γ t with 
    | Checked t_ty => ret t_ty 
    | TypeError err => UnifError (InternalError "Attempt to instantiate with an ill-typed term")
    end 
  in 
  let* ev_ty := lift_option $ EvarMap.evar_type evm ev in
  let* evm := unify pb Γ ev_ty t_ty evm in 
  (* Define the evar. *)
  let evm := EvarMap.define evm ev t in 
  ret evm

with try_same_head pb Γ t t' evm {struct pb} : unif_result EvarMap.t :=
  match whd_evars evm t, whd_evars evm t' with 
  (* Type-Same *)
  | tSort s, tSort s' =>
    let ok :=
      match pb with 
      | Conv => check_eqb_sort φ s s' 
      | Cumul => check_leqb_sort φ s s'
      end
    in 
    (* TODO : add universe constraints if needed. *)
    if ok then ret evm else UnifError UnivInconsistency
  (* Lam-Same *)
  | tLambda x ty body, tLambda _ ty' body' =>
    let* evm := unify Conv Γ ty ty' evm in 
    unify pb (Γ ,, vass x ty) body body' evm
  (* Prod-Same *)
  | tProd x a b, tProd _ a' b' =>
    let* evm := unify Conv Γ a a' evm in 
    unify pb (Γ ,, vass x a) b b' evm
  (* Let-Same *)
  | tLetIn x def ty body, tLetIn _ def' ty' body' =>
    let* evm := unify Conv Γ def def' evm in
    unify pb (Γ ,, vdef x def ty) body body' evm
  (* Rigid-Same *)
  | tRel n, tRel n' => 
    if n == n' then ret evm else UnifError NotSameHead
  | tVar v, tVar v' => 
    if v == v' then ret evm else UnifError NotSameHead
  | tConst c _, tConst c' _ =>
    if c == c' then ret evm else UnifError NotSameHead
  | tInd ind _, tInd ind' _ =>
    if ind == ind' then ret evm else UnifError NotSameHead
  | tConstruct ind n _, tConstruct ind' n' _ =>
    if (ind == ind') && (n == n') then ret evm else UnifError NotSameHead  
  | tProj p t, tProj p' t' =>
    if p == p' then unify Conv Γ t t' evm else UnifError NotSameHead
  | tFix defs n, tFix defs' n'
  | tCoFix defs n, tCoFix defs' n' =>
    if n == n' then 
      (* First unify the types. *)
      let* evm := ise_list2 (unify Conv Γ) (List.map dtype defs) (List.map dtype defs') evm in
      (* Then unify the bodies in an extended context. *)
      ise_list2 (unify Conv (Γ ,,, fix_context defs)) (List.map dbody defs) (List.map dbody defs') evm
    else UnifError NotSameHead
  | tCase ci pred x bs, tCase ci' pred' x' bs' =>
    if ci == ci' then 
      let* (pred, bs) := lift_option $ rebuild_case Σ ci pred bs in
      let* (pred', bs') := lift_option $ rebuild_case Σ ci' pred' bs' in 
      (* Unify the return predicates. *)
      let* evm := unify Conv Γ pred pred' evm in 
      (* Unify the scrutinees. *)
      let* evm := unify Conv Γ x x' evm in
      (* Unify the branches. *)
      ise_list2 (unify Conv Γ) bs bs' evm
    else UnifError NotSameHead
  (* App-FO *)
  | tApp f ts, tApp f' ts' => 
    let* evm := unify pb Γ f f' evm in 
    ise_list2 (unify Conv Γ) ts ts' evm
  | _, _ => UnifError NotSameHead
  end.

(** Main unification function entry point. *)
(*Definition unify_constr (pb : conv_pb) (t1 t2 : term) (s : state) : state := 
  let (log, evm) := s in
  unify pb (decompose_app_list evm t1) (decompose_app_list evm t2) s.*)


(*Definition destruct_app evm (t : term) : term * list term :=
  match EvarMap.head evm t with
  | tApp f args => (f, args)
  | _ => (t, [])
  end.*)

(*Fixpoint decompose_evar (evm : EvarMap.t) (t : term * list term) : term * list term :=
  let*)

(**  (** Given a head term c and with arguments l it whd reduces c if it is
      an evar, returning the new head and list of arguments.
  *)
  let rec decompose_evar sigma (c, l) =
    let (c', l') = decompose_app_list sigma c in
    if isCast sigma c' then
      let (t, _, _) = destCast sigma c' in
      decompose_evar sigma (t, l' @ l)
    else
      (c', l' @ l)
*)
