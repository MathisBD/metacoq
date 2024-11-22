(* Distributed under the terms of the MIT license. *)

(** This module defines evar maps and associated utility functions
    (most notably [whd_evars] and [nf_evars]), which are used for unification. 
    The current definition are meant for execution (not for proofs), and thus
    we disable the guard checker for simplicity. *)

From Coq.FSets Require Import FMapAVL.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import BasicAst Environment uGraph config.
From MetaCoq.Template Require Import Ast AstUtils Typing.
Import MCMonadNotation.
    
Unset Guard Checking.

(** A convenient notation for function application, which saves many parentheses. *)
#[local]
Notation "f $ x" := (f x) 
  (at level 10, x at level 100, right associativity, only parsing).

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

(** [new_evar evm nctx concl] creates a new evar with conclusion [concl] in named context [nctx],
    and adds it to the evar map [evm]. *)
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

(** [nf_evars evm t] replaces all defined evars that appear in [t] by their body. *)
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
    constructor which is not [tEvar] in [t]. This should be used liberally : 
    it is essentially free when [t] is not an evar. *)
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

