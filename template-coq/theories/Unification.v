(* Distributed under the terms of the MIT license. *)

(** This file defines a unification algorithm. It is intended for practical use 
    and is not verified. *)

From Coq.FSets Require Import FMapAVL.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import BasicAst uGraph config.
From MetaCoq.Template Require Import Ast AstUtils Checker.
Import MCMonadNotation.

Unset Guard Checking.

(** A convenient notation for function application, which saves many parentheses. *)
Notation "f $ x" := (f x) 
  (at level 10, x at level 100, right associativity, only parsing).

(** Right-to-left function composition. *)
Notation "f <<< g" := (fun x => f (g x)) (at level 40, left associativity).

(** Left-to-right function composition. *)
Notation "f >>> g" := (fun x => g (f x)) (at level 40, left associativity).

(** Unification flags. *)
(** TODO : document them. *)
Record unif_flags :=
  { uf_beta_reduce_type : bool
  ; uf_unify_types : bool 
  ; uf_aggressive : bool
  ; uf_super_aggressive : bool 
  ; uf_try_solving_eqn : bool }.

(** * Evar map. *)

(** [sort_leq_constraints s1 s2] returns a set of universe constraints that encode 
    the inequality [s1 <= s2], or [None] if [s1 <= s2] is trivially unsatisfiable. *)
Definition sort_leq_constraints (s1 s2 : Sort.t) : option ConstraintSet.t := 
  (* Make a constraint between two [LevelExpr.t]. *)
  let lexpr_edge (l r : LevelExpr.t) : UnivConstraint.t :=
    let diff := (Z.of_nat l.2 - Z.of_nat r.2)%Z in (l.1, ConstraintType.Le diff, r.1)
  in
  match s1, s2 with
  (* Trivial constraints. *)
  | sSProp, sSProp
  | sProp, sProp 
  | sSProp, sType _
  | sProp, sType _ => Some ConstraintSet.empty
  (* Type <= Type *)
  | sType l, sType r =>
    match Universe.exprs l, Universe.exprs r with
    (* No algebraics : add a single constraint. *)
    | (l, []), (r, []) => Some $ ConstraintSet.singleton $ lexpr_edge l r
    (* Algebraic on the left-hand side : add multiple constraints. *)
    | (l, ls), (r, []) =>
      Some $ List.fold_left 
        (fun acc l' => ConstraintSet.add (lexpr_edge l' r) acc) 
        (l :: ls) 
        ConstraintSet.empty
    (* Algebraics on the right-hand side are not supported. *) 
    | _, _ => None
    end
  (* Everything else is unsatisfiable. *)
  | _, _ => None
  end.

(** [eq_constraints s1 s2] returns a set of constraints that encode 
    the equality [s1 = s2], or [None] if [s1 = s2] is trivially unsatisfiable. *)
Definition sort_eq_constraints (s1 s2 : Sort.t) : option ConstraintSet.t := 
  (* Make an equality constraint between two [LevelExpr.t]. *)
  let lexpr_cstr (l r : LevelExpr.t) : ConstraintSet.t :=
    let diff := (Z.of_nat l.2 - Z.of_nat r.2)%Z in
    if diff == 0%Z
    then ConstraintSet.singleton (l.1, ConstraintType.Eq, r.1) 
    else ConstraintSet.add (l.1, ConstraintType.Le diff, r.1) $
         ConstraintSet.singleton (r.1, ConstraintType.Le $ Z.opp diff, l.1)
  in
  match s1, s2 with
  (* Trivial constraints. *)
  | sSProp, sSProp
  | sProp, sProp => Some ConstraintSet.empty
  (* Type = Type *)
  | sType l, sType r =>
    match Universe.exprs l, Universe.exprs r with
    (* No algebraics. *)
    | (l, []), (r, []) => Some $ lexpr_cstr l r
    (* Algebraics are not supported yet. *) 
    | _, _ => None
    end
  (* Everything else is unsatisfiable. *)
  | _, _ => None
  end.
      
(** Evar identifiers. *)
Definition evar := nat.

(** An evar entry in the evar map. *)
Record evar_entry := 
  { (** The evar's name. For printing only. *)
    ev_name : name 
  ; (** The evars' named context. The declarations in this context
        should contain no loose de Bruijn index (tRels). *)
    ev_nctx : named_context
  ; (** The evar's conclusion. It should be well-typed in the evar's context. *)
    ev_concl : term 
  ; (** If evar's definition (or None if the evar is undefined).
        It should be well-typed in the evar's context. *)
    ev_def : option term }.

(** Maps indexed by evars. *)
Module EvarOT := OrderedTypeEx.Nat_as_OT.
Module EMap := FMapAVL.Make EvarOT.

Module EvarMap.

(** The type of evar maps. *)
Record t := 
  { (** A map from evars to evar entries. *)
    evm_map : EMap.t evar_entry
  ; (** A counter used to generate fresh evars. *)
    evm_counter : nat
  ; (** The universe graph. *)
    evm_universes : universes_graph }.

(** The empty evar map. *)
Definition empty : t := 
  {| evm_map := @EMap.empty evar_entry 
  ;  evm_counter := 0
  ;  evm_universes := uGraph.init_graph |}.

(** Lookup the entry of an evar in the evar map. *)
Definition lookup (evm : t) (ev : evar) : option evar_entry :=
  EMap.find ev evm.(evm_map).

(** [evar_concl evm ev] retrieves the conclusion of evar [ev] in the evar map [evm]. *)
Definition evar_concl (evm : t) (ev : evar) : option term := 
  option_map ev_concl $ lookup evm ev.

(** [evar_def evm ev] retrieves the definition of evar [ev] in the evar map [evm]. *)
Definition evar_def (evm : t) (ev : evar) : option term :=
  match EMap.find ev evm.(evm_map) with 
  | None => None 
  | Some entry => entry.(ev_def)
  end.
  
(** [is_defined evm ev] checks if [ev] is present in [evm] and is defined. *)
Definition is_defined (evm : t) (ev : evar) : bool :=
  match evar_def evm ev with 
  | Some _ => true 
  | None => false 
  end.

(** [define evm ev def] assignes [ev := def] in the evar map [evm].
    This assumes : 
    - [ev] is present in [evm] but not defined.
    - [def] is well-type in the context of [ev]. *)
Definition define (evm : t) (ev : evar) (def : term) : t :=
  match EMap.find ev evm.(evm_map) with 
  | None => evm 
  | Some e => 
    let e : evar_entry := 
      {| ev_name := e.(ev_name)
      ;  ev_nctx := e.(ev_nctx) 
      ;  ev_concl := e.(ev_concl)
      ;  ev_def  := Some def |}
    in
    {| evm_map := EMap.add ev e evm.(evm_map) 
    ;  evm_counter := evm.(evm_counter)
    ;  evm_universes := evm.(evm_universes) |}
  end.

Definition new_evar (evm : t) (nctx : named_context) (concl : term) : (t * evar) :=
  let entry := 
    {| ev_name := nNamed "x"%bs 
    ;  ev_nctx := nctx 
    ;  ev_concl := concl 
    ;  ev_def := None |}
  in 
  let ev := evm.(evm_counter) in
  (* Don't forget to increment the evar counter. *)
  let evm := 
    {| evm_map := EMap.add ev entry evm.(evm_map) 
    ;  evm_counter := S evm.(evm_counter)
    ;  evm_universes := evm.(evm_universes) |}
  in
  (evm, ev).

(** [add_univ_constraints evm cstrs] adds universe constraints [cstrs] to the evar map [evm].
    It returns [None] if the added constraints are inconsistent. *)
Definition add_univ_constraints `{cf : checker_flags} (evm : EvarMap.t) 
  (cstrs : ConstraintSet.t) : option EvarMap.t :=
  let universes :=
    ConstraintSet.fold 
      (fun cstr ugraph => 
        match cstr with 
        | (l, ConstraintType.Le n, r) => 
          wGraph.add_edge ugraph (l, n, r)
        | (l, ConstraintType.Eq, r) =>
          let ugraph := wGraph.add_edge ugraph (l, 0%Z, r) in 
          wGraph.add_edge ugraph (r, 0%Z, l)
        end)
      cstrs
      evm.(evm_universes)
  in
  (* Check the new constraints are still consistent. *)
  if wGraph.is_acyclic universes then 
    Some {| evm_map := evm.(evm_map)
         ;  evm_counter := evm.(evm_counter)
         ;  evm_universes := universes |}
  else None.

(** [set_eq_sort evm s1 s2] adds constraints to [evm] to enforce [s1 = s1].
    It returns [None] if the added constraints are inconsistent. *)
Definition set_eq_sort `{cf : checker_flags} (evm : EvarMap.t) (s1 s2 : Sort.t) : option EvarMap.t :=
  add_univ_constraints evm =<< sort_eq_constraints s1 s2.

(** [set_leq_sort evm s1 s2] adds constraints to [evm] to enforce [s1 <= s1].
    It returns [None] if the added constraints are inconsistent. *)
Definition set_leq_sort `{cf : checker_flags} (evm : EvarMap.t) (s1 s2 : Sort.t) : option EvarMap.t :=
    add_univ_constraints evm =<< sort_leq_constraints s1 s2.

End EvarMap.


(** [subst_var v t u] replaces all occurences of [v] by [t] in [u].
    It assumes [t] contains no loose tRel (i.e. it does not perform lifting). *)
Fixpoint subst_var (v : ident) (t u : term) : term :=
  match u with 
  | tVar v' => if v == v' then t else tVar v'
  | _ => map_term (subst_var v t) u
  end.

(** [instantiate_evar ctx subs def] instantiates an evar. 
    - [ctx] is the named context of the evar. 
    - [def] is the definition of the evar (also works with the conclusion of the evar).
    - [subs] is the list of terms which are substituted for the variables in [ctx].
    TODO : make this more efficient. *)
Fixpoint instantiate_evar (ctx : named_context) (subs : list term) (def : term) : term :=
  match ctx, subs with 
  | (id, _) :: ctx, s :: subs =>
    instantiate_evar ctx subs (subst_var id s def)
  | _, _ => def 
  end.

(** [nf_evars evm t] replaces all defined evars that appear in [t] 
    by their body. *)
Fixpoint nf_evars (evm : EvarMap.t) (t : term) {struct t} : term :=
  match t with 
  | tEvar ev subs =>
    match EvarMap.lookup evm ev with 
    | Some {| ev_name := _ ; ev_nctx := ctx ; ev_concl := _ ; ev_def := Some def |} =>
      nf_evars evm $ instantiate_evar ctx subs def 
    | _ => t 
    end 
  | _ => map_term (nf_evars evm) t
  end.

(** [whd_evars evm t] expands evars just enough to expose the first 
    constructor which is not [tEvar] in [t]. *)
Fixpoint whd_evars (evm : EvarMap.t) (t : term) {struct t} : term :=
  match t with 
  | tEvar ev subs =>
    match EvarMap.lookup evm ev with 
    | Some {| ev_name := _ ; ev_nctx := ctx ; ev_concl := _ ; ev_def := Some def |} =>
      whd_evars evm $ instantiate_evar ctx subs def 
    | _ => t 
    end 
  | t => t 
  end.

(** * Unification errors. *)

(* TODO : document this. *)
Inductive unif_error := 
  | NotSameHead : unif_error
  | NotSameArgSize : unif_error
  | OccurCheck : evar -> term -> unif_error
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

(** Monadic bind. *)
Definition bind_ {A} {B} (ma : unif_result A) (mf : A -> unif_result B) : unif_result B :=
  match ma with 
  | Success a => mf a 
  | UnifError err => UnifError err
  end.
Notation "'let*' x := c1 'in' c2" := (bind_ c1 (fun x => c2))
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
  | Some x => Success x
  | None => UnifError (InternalError "lift_option")
  end.

(*Definition assert (msg : string) s (cond : bool) : state :=
  if cond then s 
  else (s.1, UnifFailure (AssertionFailure msg)).*)

(** * Unification algorithm. *)

(** [is_evar evm t] checks if [t] is an evar. *)
Definition is_evar evm t : bool :=
  match whd_evars evm t with 
  | tEvar _ _ => true 
  | _ => false 
  end.

Fixpoint ise_list2 {A B} (f : A -> B -> EvarMap.t -> unif_result EvarMap.t) 
  (xs : list A) (ys : list B) (evm : EvarMap.t) : unif_result EvarMap.t :=
  match xs, ys with 
  | [], [] => Success evm 
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

(** [find_unique cond xs] checks if there is exactly one element in [xs] that satisfies
    the condition [cond], and if so returns its index. *)
Definition find_unique {A} (cond : A -> bool) (xs : list A) : option nat :=
  (* Loop over elements of [xs] from first to last. 
     - [i] is the index of the current element.
     - [res] is [None] if we have not yet found an element satisfying [cond],
       otherwise it is [Some idx] where [idx] is the position of the element. *)
  let fix loop res i xs :=
    match xs with 
    | [] => res 
    | x :: xs =>
      if cond x then 
        match res with 
        (* We found a first element satisfying [cond]. *)
        | None => loop (Some i) (S i) xs 
        (* We found two elements satisfying [cond] : return [None]. *)
        | Some _ => None 
        end
      else loop res (S i) xs
    end 
  in 
  loop None 0 xs.
  
(** Specialization of [find_unique] to named variables (tVars). *)
Definition find_unique_var evm (id : ident) (ts : list term) :=
  find_unique (fun t => whd_evars evm t == tVar id) ts.

(** Specialization of [find_unique] to de Bruijn variables (tRels). *)
Definition find_unique_rel evm (n : nat) (ts : list term) :=
  find_unique (fun t => whd_evars evm t == tRel n) ts.

(** [evar_occurs evm ev t] checks if evar [ev] occurs in term [t]. *)
Fixpoint evar_occurs (evm : EvarMap.t) (ev : evar) (t : term) : bool :=
  match whd_evars evm t with 
  | tEvar ev' _ => if ev == ev' then true else false 
  | t => fold_term (fun acc subt => acc || evar_occurs evm ev subt) false t
  end.

(** [term_fvars evm t] computes the set of free variables (tVars) in the term [t]. *)
Definition term_fvars (evm : EvarMap.t) (t : term) : IdentSet.t := 
  let fix aux acc t :=
    match whd_evars evm t with 
    | tVar v => IdentSet.add v acc 
    | t => fold_term aux acc t 
    end 
  in 
  aux IdentSet.empty t.

(** [has_free_var evm vars t] checks if [t] has a free variable which is in [vars]. *)
Definition has_free_var (evm : EvarMap.t) (vars : list ident) (t : term) : bool :=
  let fvars := term_fvars evm t in 
  List.existsb (fun v => IdentSet.mem v fvars) vars.

(** [remove_with_deps evm nctx pos] removes the declarations at positions [pos] in named context [nctx].
    Declarations which depend on removed ones are removed as well. *)
Definition remove_with_deps (evm : EvarMap.t) (nctx : named_context) (pos : list nat) : named_context :=
  (* We process declarations in [nctx] from last to first (i.e. outermost to innermost).
     - [i] is the index of the current declaration.
     - [removed] contains the identifiers of the variables which were removed so far. *)
  let fix loop i nctx removed :=
    match nctx with
    | [] => []
    | (id, d) :: nctx =>
      if List.existsb (eqb i) pos
         || has_free_var evm removed d.(decl_type) 
         || option_default (has_free_var evm removed) d.(decl_body) false
      (* Remove [d]. *)
      then loop (pred i) nctx (id :: removed)
      (* Keep [d]. *)
      else (id, d) :: loop (pred i) nctx removed
    end
  in
  rev $ loop (pred #|nctx|) (rev nctx) [].

Module Invert.

(** We need a state-option monad in this section. *)
Local Definition M A := EMap.t (list nat) -> option (EMap.t (list nat) * A).

#[local] Instance : Monad M :=
{ 
  ret _ a s := Some (s, a) ;
  bind _ _ ma mf s := 
    match ma s with 
    | None => None
    | Some (s, a) => mf a s
    end
}.

(** Monadic alternative. *)
Definition msum {A} (mx my : M A) : M A :=
  fun s =>
  match mx s with 
  | None => my s 
  | Some (s, x) => Some (s, x)
  end.
#[local] Notation "x <|> y" := (msum x y) 
  (at level 85, right associativity).
   
Local Definition fail {A} : M A := fun s => None.
  
Definition invert (evm : EvarMap.t) (map : EMap.t (list nat)) (nctx : named_context) 
  (ev0 : evar) (subs : list term) (args : list term) (t : term) : option (EMap.t (list nat) * term) :=
  let subs_args := subs ++ args in
  let var_or_rel depth k :=
    if k <? #|subs| 
    then option_map (tVar <<< fst) $ List.nth_error nctx k
    else Some $ tRel $ #|subs_args| - k - 1 + depth
  in 
  let fix invert_aux (inside_evar : bool) (depth : nat) (t : term) : M term :=
    match whd_evars evm t with
    | tVar id =>
      match var_or_rel depth =<< find_unique_var evm id subs_args with
      | None => fail 
      | Some t => ret t
      end
    | tRel j =>
      if depth <? j then 
        match var_or_rel depth =<< find_unique_rel evm (j - depth) subs_args with 
        | None => fail 
        | Some t => ret t
        end
      else ret $ tRel j
    | tEvar ev args =>
      if ev == ev0 then fail else 
	  (*let evargs' := Evd.expand_existential sigma (ev', evargs') in*)
	  let on_arg arg_idx arg := 
        (* First try to invert the argument. *)
        invert_aux true depth arg <|>
        (* We could not invert this argument : we have to prune it. *)
		(* Pruning can not happen inside an evar's suspended substitution. *)
        if inside_evar then fail else 
        (* Extend the pruning map : we have to prune the declaration 
           at position [arg_idx] of evar [ev]. *)
        (fun map => 
		  let prev_idxs := option_get [] (EMap.find ev map) in
          let map := EMap.add ev (arg_idx :: prev_idxs) map in 
          Some (map, arg))
	  in
      (* Invert each argument. *)
      mlet args <- monad_map_i on_arg args ;;
      ret $ tEvar ev args
	| t =>
      map_term_with_bindersM depth (fun _ depth => ret $ S depth) (invert_aux inside_evar) t
    end
  in
  invert_aux false 0 t map.

End Invert.

Section Algorithm.
Context `{uf : unif_flags} `{cf : checker_flags} (Σ : global_env) (Δ : named_context).

Implicit Types (pb : conv_pb) (Γ : context).
Existing Instance default_fuel.

(** [invert evm map nctx ev subs args t] inverts the equation [?ev[subst] args := t]
    (where [nctx] is the named context of the evar, thus #|nctx| = #|subs|).
    
    More precisely it builds a term t' equal to t, except that every free variable 
    (tVar or tRel) x in t is replaced by :
    - if x appears does not appear _uniquely_ in [subs ++ args], then we fail.
    - if x appears in [subs] at index [i], then x is replaced by [tVar n]
      where [n] is the name of the variable in [nctx] at index [i].
    - If x appears in [args] at index [i] (starting from the end), 
      then x is replaced by [tRel i].
    It fails if [ev] appears inside [t]. 
    
    This function implements a heuristic which helps in some cases : it tries to 
    prune evars appearing in [t] (see also the [prune] function). 
    [map] is the initial pruning map (which assign to every evar a list of argument
    positions to prune), which [invert] extends as needed. *)
Definition invert := Invert.invert.

(** [invert_lambdas evm map nctx ev subst args body] computes the term 
    [fun x1 : A1{subs}^-1 => ... => fun xn : An{subs}^-1 => body], where :
    - [ev] is an evar with named context [nctx].
    - [subs] is a suspended substitution compatible with [nctx] (thus #|subs| = #|nctx|).
    - [args] = [x1 ... xn] are the arguments of the evar.
    - [body] is a term with free de Bruijn indices (tRels) [0 ... n-1].
    - Each [xi] has type [Ai].

    See [invert] for an explanation of [map].
*)
Definition invert_lambdas (evm : EvarMap.t) (Γ : context) (map : EMap.t (list nat)) 
  (nctx : named_context) (ev : evar) (subs args : list term) (body : term) : option (EMap.t (list nat) * term) :=
  (* We process the arguments from last to first. *)
  let fix loop acc args : option (EMap.t (list nat) * term) :=
    match args with 
    | [] => ret acc 
    | arg :: args => 
      (* TODO : remove [nf_evars] and add evar handling to the checker. *)
      (* TODO : use retyping instead of full typing here. *)
      mlet ty <-
        match Checker.infer Σ (EvarMap.evm_universes evm) Δ Γ $ nf_evars evm arg with 
        | Checked ty => Some ty 
        | TypeError _ => None
        end
      ;;
      mlet '(map, ty) <- invert evm map nctx ev subs (rev args) ty ;;
      let binder := {| binder_name := nAnon ; binder_relevance := Relevant |} in
      loop (map, tLambda binder ty body) args
    end 
  in 
  loop (map, body) $ rev args.
      
(** [prune evm ev pos] prunes the declarations at positions [pos] in the context of the evar [ev].
    More precisely :
    - if [ev] is defined in [evm] it does nothing.
    - if [ev] is undefined in [evm], it assigns [ev := ev'] where [ev'] has the same conclusion
      as [ev] but lives in a context which has been pruned. 
    It returns [None] if prunning failed. *)
Fixpoint prune (evm : EvarMap.t) (ev : nat) (pos : list nat) {struct ev} : option EvarMap.t :=
  if EvarMap.is_defined evm ev then Some evm else
  mlet entry <- EvarMap.lookup evm ev ;; 
  (* Remove the required positions from the local context of the evar. *)
  let new_ctx := remove_with_deps evm entry.(ev_nctx) pos in 
  (* Make sure the conclusion of the evar does not contain any removed variables.
     This might require pruning other evars which appear in the conclusion. *)
  let concl := entry.(ev_concl) in
  let new_ctx_vars := List.map (tVar <<< fst) new_ctx in
  mlet '(map, _) <- invert evm (EMap.empty (list nat)) new_ctx ev new_ctx_vars [] concl ;;
  (* Prune other evars as needed. *)
  mlet evm <- prune_all evm map tt ;;
  (* Create a fresh evar [ev'] in the new context. *)
  let (evm, ev') := EvarMap.new_evar evm new_ctx concl in
  (* Assign [ev := ev']. *)
  Some $ EvarMap.define evm ev' (tEvar ev new_ctx_vars)

(** [prune_all evm map tt] prunes all the evars in [evm] according to [map].
    Unfortunately for technical reasons we have to pass a useless [tt] argument to [prune_all]. *)
with prune_all (evm : EvarMap.t) (map : EMap.t (list nat)) (dummy : unit) {struct dummy} : option EvarMap.t :=
  monad_fold_left (fun evm '(ev, pos) => prune evm ev pos) (EMap.elements map) evm. 

(** [intersect evm xs ys] computes the list of positions where the terms in [xs] and [ys] 
    are not equal. By default only disagreements on positions where both are variables 
    (tVar or tRel) are accepted, and we return None otherwse.
    The unification flag [uf_aggressive] bypasses this behaviour, making [intersect] always succeed. *)
Definition intersect evm (xs ys : list term) : option (list nat) :=
  let is_var t := 
    match whd_evars evm t with tVar _ | tRel _ => true | _ => false end 
  in  
  let fix loop i xs ys diff :=
    match xs, ys with 
    | [], [] => Some diff
    | x :: xs, y :: ys =>
      (* TODO : push evar handling in [eq_term]. *)
      if eq_term (EvarMap.evm_universes evm) (nf_evars evm x) (nf_evars evm y) then loop (S i) xs ys diff 
      else if is_var x && is_var y then loop (S i) xs ys (i :: diff)
      else if uf.(uf_aggressive) then loop (S i) xs ys (i :: diff)
      else None
    | _, _ => None 
    end 
  in 
  loop 0 xs ys [].
          
(** [meta_same evm ev subs1 subs2] implements the Meta-Same rule to unify [ev[subs1] =?= ev[subs2]]. *)
Definition meta_same evm (ev : evar) (subs1 subs2 : list term) : unif_result EvarMap.t :=
  (* Prune the evar on the positions where [subs1] and [subs2] disagree. *)
  match intersect evm subs1 subs2 with
  | Some [] => 
    (* Fast path to avoid pruning if unnecessary. *) 
    Success evm
  | Some pos =>
    match prune evm ev pos with 
    | Some evm => Success evm 
    | None => UnifError NotSameHead
    end
  | None => UnifError NotSameHead
  end.

(** Helper function used to implement [meta_inst]. 
    It inverts the equation [ev[subs] args =?= t] and returns :
    - the updated evar map (after pruning).
    - the term [t'] that [ev] will get instantiated with, which lives in the local context of [ev]. *)
Definition meta_inst_solution Γ (ev : evar) (subs args : list term) (t : term) evm :=
  (* TODO : remove equal tails. *)
  (* TODO : beta-reduce to remove dependencies. *)
  mlet entry <- EvarMap.lookup evm ev ;;
  mlet '(map, t0) <- invert evm (EMap.empty (list nat)) entry.(ev_nctx) ev subs args t ;;
  mlet '(map, t1) <- invert_lambdas evm Γ map entry.(ev_nctx) ev subs args t0 ;;
  (* Prune the evar map as required by [map]. *)
  mlet evm <- prune_all evm map tt ;;
  (* TODO : refresh universes. *)
  ret (evm, t1).

(** [tapp f args] represents the application of a term [f] to arguments [args].
    The list of arguments can be empty. *)
Definition tapp := term * list term.

(** [whd_tapp evm t] expands evars and removes casts in the head of [t]. *)
Fixpoint whd_tapp evm (t : tapp) {struct t} : tapp :=
  let (f, args) := t in
  match whd_evars evm f with 
  | tApp f' args' => whd_tapp evm (f', args' ++ args)
  | tCast f' _ _ => whd_tapp evm (f', args)
  | f' => (f', args)
  end.

(** Main unification function(s). *)
Fixpoint unify pb Γ (t t' : term) evm {struct pb} : unif_result EvarMap.t :=
  let t := whd_tapp evm (t, []) in 
  let t' := whd_tapp evm (t', []) in 
  if is_evar evm t.1 || is_evar evm t'.1 then 
    try_instantiate pb Γ t t' evm
  else 
    try_canonical_structures pb Γ t t' evm <|> 
    try_app_fo pb Γ t t' evm <|>
    try_reduce pb Γ t t' evm

(** [try_instantiate] is called when either [t] or [t'] is an evar (possible applied
    to a suspended subsitution and arguments), and tries to apply rules which instantiate evars. *)
with try_instantiate pb Γ t t' evm {struct pb} : unif_result EvarMap.t :=
  let t := whd_tapp evm t in 
  let t' := whd_tapp evm t' in
  match t.1, t'.1 with 
  | tEvar ev subs, tEvar ev' subs' => 
    if ev == ev' 
    (* Meta-Same *)
    then 
      let* evm := meta_same evm ev subs subs' in 
      ise_list2 (unify Conv Γ) t.2 t'.2 evm
    (* Meta-Meta *)
    else
      (* We try both directions, but first the one with the longest substitution. *)
      let '(ev1, ev2, subs1, subs2, args1, args2, t1, t2) := 
        if #|subs| <? #|subs'|
        then (ev', ev, subs', subs, t'.2, t.2, t, t')
        else (ev, ev', subs, subs', t.2, t'.2, t', t)
      in 
      meta_inst pb Γ ev1 subs1 args1 t1 evm <|> 
      meta_inst pb Γ ev2 subs2 args2 t2 evm
  (* Meta-InstL *)
  | tEvar ev subs, _ => meta_inst pb Γ ev subs t.2 t' evm
  (* Meta-InstR *)
  | _, tEvar ev' subs' => meta_inst pb Γ ev' subs' t'.2 t evm
  | _, _ => UnifError (InternalError "try_instantiate : expected an evar")
  end

(** [meta_inst pb Γ ev subs t evm] implements the Meta-Inst rule to instantiate [ev[subs] args := t]. *)
with meta_inst pb Γ ev subs args (t : tapp) evm {struct pb} : unif_result EvarMap.t :=
  let t := 
    (* TODO : beta reduce if the configuration option is set. *)
    tApp t.1 t.2 
  in
  let is_var t := 
    match whd_evars evm t with tVar _ | tRel _ => true | _ => false end 
  in
  (* Check the substitution and arguments contain only variables (tVars and tRels). *)
  if List.forallb is_var (subs ++ args) then 
    (* Compute the solution [sol]. *)
    let* (evm, sol) := lift_option $ meta_inst_solution Γ ev subs args t evm in
    (* Unify the type of the evar with the type of the solution (if the required flag is set). *)
    let* evm :=
      if uf.(uf_unify_types)
      then 
        let* entry := lift_option $ EvarMap.lookup evm ev in
        let* sol_ty := 
          (* TODO : this should be retyping. *)
          match Checker.infer Σ (EvarMap.evm_universes evm) entry.(ev_nctx) [] sol with 
          | Checked ty => Success ty
          | TypeError _ => UnifError (InternalError "meta_inst : typecheck error")
          end 
        in
        let* entry := lift_option $ EvarMap.lookup evm ev in
        let ev_ty := instantiate_evar entry.(ev_nctx) subs entry.(ev_concl) in
        unify Cumul Γ sol_ty ev_ty evm
      else Success evm
    in 
    (* Check the evar does not occur in the solution. *)
    if evar_occurs evm ev sol then UnifError (OccurCheck ev sol) else 
    (* Finally define the evar. *)
    Success (EvarMap.define evm ev sol)
  else UnifError NotSameHead

with try_canonical_structures pb Γ (t t' : tapp) evm {struct pb} : unif_result EvarMap.t :=
  UnifError (InternalError "try_canonical_structures : not implemented yet")

with try_app_fo pb Γ (t t' : tapp) evm {struct pb} : unif_result EvarMap.t :=
  let (f, args) := whd_tapp evm t in 
  let (f', args') := whd_tapp evm t' in
  if #|args| == #|args'| then 
    (* Unify the heads. *)
    let* evm := unify_head pb Γ f f' evm in 
    (* Unify the arguments. *)
    ise_list2 (unify Conv Γ) args args' evm
  else 
    UnifError NotSameArgSize

with try_reduce pb Γ (t t' : tapp) evm {struct pb} : unif_result EvarMap.t :=
  UnifError (InternalError "try_reduce : not implemented yet")

with unify_head pb Γ t t' evm {struct pb} : unif_result EvarMap.t :=
  match whd_evars evm t, whd_evars evm t' with 
  (* Type-Same *)
  | tSort s, tSort s' =>
    (* Enforce the new universe constraints. *)
    let evm :=
      match pb with 
      | Conv => EvarMap.set_eq_sort evm s s' 
      | Cumul => EvarMap.set_eq_sort evm s s'
      end
    in 
    (* Check the universe graph is still consistent. *)
    match evm with
    | Some evm => Success evm 
    | None => UnifError UnivInconsistency
    end
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
    if n == n' then Success evm else UnifError NotSameHead
  | tVar v, tVar v' => 
    if v == v' then Success evm else UnifError NotSameHead
  | tConst c _, tConst c' _ =>
    if c == c' then Success evm else UnifError NotSameHead
  | tInd ind _, tInd ind' _ =>
    if ind == ind' then Success evm else UnifError NotSameHead
  | tConstruct ind n _, tConstruct ind' n' _ =>
    if (ind == ind') && (n == n') then Success evm else UnifError NotSameHead  
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

End Algorithm.

(****************************)
(** Testing *)

From MetaCoq.Template Require Import All.

(** Run a template program. *)
Notation "'$run' f" :=
  ltac:(
    let p y := exact y in
    run_template_program f p
  ) (at level 0, only parsing).

Definition t1 := $run (tmQuote (fun x => S x + 1)).
Definition t2 := $run (tmQuote (fun y => S y + 1)).

Definition Σ := fst ($run (tmQuoteRec (fun x => S x + 1))).


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
