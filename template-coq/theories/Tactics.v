(* Distributed under the terms of the MIT license. *)

From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import BasicAst.
From MetaCoq.Template Require Import Ast AstUtils Typing Checker Evars Unification Pretty.
Import MCMonadNotation.

Local Set Universe Polymorphism.

Inductive tactic_result A : Type :=
  | TacticSuccess : A -> tactic_result A 
  | TacticError : tactic_result A.
Arguments TacticSuccess {A}%_type_scope a.
Arguments TacticError {A}%_type_scope.

(** The tactic monad. It contains the following effects : 
    - Read access to the environment and named context.
    - Read-write access to the evar map.
    - Read-write access to a list of goals. 
      The order of goals matters : the main goal is at the head of the list.
    - The possibility to fail (non-catchable exceptions). *)
Definition TacticM@{u} (A : Type@{u}) : Type@{u} := 
  global_env -> 
  named_context -> 
  EvarMap.t ->
  list evar ->
  tactic_result (A * EvarMap.t * list evar).

(** The tactic monad instance. This is just a standard state-reader-option monad. *)
Instance monad_TacticM : Monad TacticM :=
{
  ret _ a := fun _ _ evm goals => TacticSuccess (a, evm, goals) ;
  bind _ _ mx mf :=
    fun env nctx evm goals =>
      match mx env nctx evm goals with 
      | TacticSuccess (x, evm, goals) => mf x env nctx evm goals
      | TacticError => TacticError
      end
}.

(** * Basic TacticM bookkeeping. *)

(** Fetch the global environment. *)
Definition get_global_env : TacticM global_env :=
  fun env nctx evm goals => TacticSuccess (env, evm, goals).

(** Fetch the current named context. *)
Definition get_named_context : TacticM named_context :=
  fun env nctx evm goals => TacticSuccess (nctx, evm, goals).

(** Locally modify the named context. *)
Definition with_named_context {A} (nctx0 : named_context) (m : TacticM A) : TacticM A :=
  fun env _ evm goals => m env nctx0 evm goals.

(** Fetch the current evar map. *)
Definition get_evar_map : TacticM EvarMap.t :=
  fun env nctx evm goals => TacticSuccess (evm, evm, goals).

(** Set (override) the evar map. *)
Definition set_evar_map (evm : EvarMap.t) : TacticM unit :=
  fun env nctx _ goals => TacticSuccess (tt, evm, goals).

(** Get the list of goals. Order matters. *)
Definition get_goals : TacticM (list evar) :=
  fun env nctx evm goals => TacticSuccess (goals, evm, goals).

(** Set (override) the list of goals. *)
Definition set_goals (goals : list evar) : TacticM unit :=
  fun env nctx evm _ => TacticSuccess (tt, evm, goals).

(** Fetch the main goal (and fail if there are no goals). *)
Definition get_main_goal : TacticM evar :=
  fun env nctx evm goals => 
    match goals with
    | [] => TacticError 
    | g :: goals => TacticSuccess (g, evm, g :: goals)
    end.

(** [fail_tac] is a tactic which always fails. *)
Definition fail_tac {A} : TacticM A :=
  fun _ _ _ _ => TacticError.

(** [with_evar_context ev t] executes tactic [t] in the context of evar [ev]. *)
Definition with_evar_context {A} (ev : evar) (t : TacticM A) : TacticM A :=
  mlet evm <- get_evar_map ;;
  match EvarMap.lookup evm ev with 
  | None => fail_tac 
  | Some entry => with_named_context entry.(ev_nctx) t
  end.

(** Tactics which don't require a goal. *)

(** [fresh_univ_level] creates a fresh universe level and adds it to the evar map. *)
Definition fresh_univ_level : TacticM Level.t :=
  mlet evm <- get_evar_map ;;
  let (evm, lvl) := EvarMap.fresh_level evm in
  set_evar_map evm ;;
  ret lvl.

(** Helper function to create a fresh evar with a given type. *)
Definition fresh_evar_aux (ty : term) : TacticM term :=
  (* Create the evar. *)
  mlet evm <- get_evar_map ;;
  mlet nctx <- get_named_context ;;
  let (evm, ev) := EvarMap.fresh_evar evm "x" nctx ty in
  set_evar_map evm ;;
  (* Apply the evar to an instance of the local context. *)
  let inst : list term := List.map (tVar <<< fst) nctx in
  ret $ tEvar ev inst.

(** [fresh_evar basename ty_opt] creates a fresh evar ?x in the current named context.
    - [basename] is the name of the evar, which might be modified to ensure freshness.
    - [ty_opt] is the (optional) type of ?x :
      + if it is [Some ty] then it is used as the type of ?x, i.e. [?x : ty]. 
      + if it is [None], then another fresh evar ?y is created such that [?x : ?y : Type].
    This function returns the evar ?x applied to an instance of the current named context. *)
Definition fresh_evar (basename : ident) (ty_opt : option term) : TacticM term :=
  (* Create the type of ?x. *)
  mlet ty <-
    match ty_opt with 
    | Some ty => ret ty
    | None => 
      (* Create an evar ?y : Type. *)
      mlet lvl <- fresh_univ_level ;;
      fresh_evar_aux (tSort $ sType $ Universe.make' lvl) 
    end
  ;;
  (* Create ?x. *)
  fresh_evar_aux ty.
  
(** [unify_tac flags pb t1 t2] unifies [t1] and [t2] using unification flags [flags]
    and conversion relation [pb], in the current named context.  *)
Definition unify_tac (flags : UnifFlags.t) (pb : conv_pb) (t1 t2 : term) : TacticM (unif_result unit) :=
  mlet env <- get_global_env ;;
  mlet nctx <- get_named_context ;;
  mlet evm <- get_evar_map ;;
  match @Unification.unify PrettyFlags.default env nctx [] pb t1 t2 evm flags with
  | (_, UnifSuccess evm) => set_evar_map evm ;; ret (UnifSuccess tt)
  | (_, UnifError) => fail_tac
  end.

(** [assign_tac ev t] assigns [t] to evar [ev]. *)
Definition assign_tac (ev : evar) (t : term) : TacticM unit :=
  mlet evm <- get_evar_map ;; 
  set_evar_map $ EvarMap.define evm ev t.

(** * Tactics which work on a goal. *)

(** [simple_tactic t] is a tactic which applies [t] on the main goal (the first in the list).
    [t] returns a list of new goals, which replace the main goal.
    It assumes [t] does not modify the list of goals. *)
Definition simple_tactic {A} (t : evar -> TacticM (A * list evar)) : TacticM A :=
  mlet goals <- get_goals ;;
  match goals with 
  | [] => fail_tac 
  | g :: goals => 
    mlet (a, new_goals) <- with_evar_context g (t g) ;;
    set_goals (new_goals ++ goals) ;;
    ret a
  end.

(* ?goal[nctx] : forall x, P *)
(* intro y. *)
(* unify (forall x0 : ?x[nctx], ?y[nctx,,tRel 0]) (forall x, P) *)
(* ?x:[nctx]  ?y:[nctx,,x0] *)
(* set ?goal := fun x0 : ?x[nctx] => ?y[nctx,,tRel 0] *)

(** [abstract x t] replaces all occurences of [tVar x] by [tRel 0] (modulo lifting) in [t]. *)
Definition abstract (x : ident) (t : term) : term :=
  let fix aux depth t :=
    match t with 
    | tVar x' => if x == x' then tRel depth else tVar x'
    | _ => map_term_with_binders 0 (fun _ => S) aux t
    end
  in 
  aux 0 t.

(** Get the evar id in a term of the form [tEvar _ _]. *)
Definition get_evar_id (t : term) : evar :=
  match t with 
  | tEvar ev _ => ev 
  | _ => 0
  end.

(** [intro x] works on the main goal : it unifies the goal with a product type 
    and introduces a single local variable. [x] can be modified to ensure freshness :
    the fresh name is returned by [intro]. 
    This tactic should work even if the goal is itself an evar (and in this case will instantiate the evar). *)
Definition intro_tac (basename : ident) : TacticM ident := 
  simple_tactic $ fun goal =>
  (* Ensure the introduced indentifier is fresh. *)
  mlet nctx <- get_named_context ;;
  let name := fresh_ident basename $ IdentSetProp.of_list $ map fst nctx in   
  (* Create evars for the type of the binder and for the body of the function. *)
  let binder := {| binder_name := nNamed name ; binder_relevance := Relevant |} in
  mlet a <- fresh_evar "a" None ;;
  let body_nctx := nctx ,, (name, vass binder a) in
  mlet b <- with_named_context body_nctx (fresh_evar "b" None) ;;
  (* Unify [forall x : ?a, ?b <=? goal]. *)
  unify_tac UnifFlags.default Cumul 
    (tProd binder a $ abstract name b)
    (tEvar goal $ List.map (tVar <<< fst) nctx) ;;
  (* Set [?goal := fun x : ?a, ?body] *)
  mlet body <- with_named_context body_nctx (fresh_evar "goal" (Some b)) ;;
  assign_tac goal (tLambda binder a $ abstract name body) ;;
  (* Return the name of the introduced variable and the new goal. *)
  ret (name, [get_evar_id body]).