(* Distributed under the terms of the MIT license. *)

From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import BasicAst.
From MetaCoq.Template Require Import Ast AstUtils Typing Checker Evars Unification Pretty.
Import MCMonadNotation.

Local Set Universe Polymorphism.
Unset Guard Checking.

Inductive tactic_result A : Type :=
  (** A successful tactic. *)
  | TacticSuccess : A -> tactic_result A
  (** A failing tactic, with an error message. *) 
  | TacticError : doc unit -> tactic_result A.
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
      | TacticError err => TacticError err
      end
}.

(** * Basic TacticM bookkeeping. *)

(** [fail_tac] is a tactic which always fails. *)
Definition fail_tac {A} (err : doc unit) : TacticM A :=
  fun _ _ _ _ => TacticError err.

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

(** Fetch the main goal (and fail if there are no goals). *)
Definition get_main_goal : TacticM evar :=
  fun env nctx evm goals => 
    match goals with
    | [] => TacticError $ str "get_main_goal : no goals"
    | g :: goals => TacticSuccess (g, evm, g :: goals)
    end.

(** [with_evar_context ev t] executes tactic [t] in the context of evar [ev]. *)
Definition with_evar_context {A} (ev : evar) (t : TacticM A) : TacticM A :=
  mlet evm <- get_evar_map ;;
  match EvarMap.lookup evm ev with 
  | None => fail_tac $ str "with_evar_context : undeclared evar"
  | Some entry => with_named_context entry.(ev_nctx) t
  end.

(** [with_main_context t] executes tactic [t] in the context of the main goal. *)
Definition with_main_context {A} (t : TacticM A) : TacticM A :=
  mlet goals <- get_goals ;;
  match goals with 
  | goal :: _ => with_evar_context goal t
  | [] => fail_tac $ str "with_main_context : no goals"
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

(** [typeof_tac t] computes the type of [t] in the current context, assuming it is well-typed.
    If [t] is not well-typed, it might (but won't necessarily) fail. *)
Definition typeof_tac (t : term) : TacticM term :=
  mlet env <- get_global_env ;;
  mlet nctx <- get_named_context ;;
  mlet evm <- get_evar_map ;;
  match retype evm env nctx [] t with 
  | Checked ty => ret ty 
  | TypeError _ => fail_tac $ str "typeof_tac : type error"
  end.

(** [whnf_tac flags t] computes the weak-head normal form of [t] 
    with reduction flags [flags]. *)
Definition whnf_tac (flags : RedFlags.t) (t : term) : TacticM term :=
  mlet env <- get_global_env ;;
  mlet nctx <- get_named_context ;;
  mlet evm <- get_evar_map ;;
  ret $ weak_head_reduce flags evm env nctx [] t.

(** [unify_tac flags pb t1 t2] unifies [t1] and [t2] using unification flags [flags]
    and conversion relation [pb], in the current named context.
    It unification is successful it returns [true] and updates the evar map,
    otherwise it returns [false] and leaves the evar map unchanged.  *)
Definition unify_tac (flags : UnifFlags.t) (pb : conv_pb) (t1 t2 : term) : TacticM bool :=
  mlet env <- get_global_env ;;
  mlet nctx <- get_named_context ;;
  mlet evm <- get_evar_map ;;
  match @Unification.unify PrettyFlags.default env nctx [] pb t1 t2 evm flags with
  | (_, UnifSuccess evm) => set_evar_map evm ;; ret true
  | (_, UnifError) => ret false
  end.

(** [assign_tac ev t] assigns [t] to evar [ev].
    It fails if [ev] is already assigned. *)
Definition assign_tac (ev : evar) (t : term) : TacticM unit :=
  mlet evm <- get_evar_map ;; 
  if EvarMap.is_defined evm ev 
  then fail_tac $ str "assign_tac : evar is already assigned"
  else set_evar_map $ EvarMap.define evm ev t.

(** * Tactics which work on a goal. *)

(** [main_concl] returns the conclusion of the main goal,
    and fails if there are no goals. *)
Definition main_concl : TacticM term :=
  mlet evm <- get_evar_map ;;
  mlet goal <- get_main_goal ;;
  match EvarMap.lookup evm goal with 
  | None => fail_tac $ str "main_concl : undefined evar"
  | Some entry => typeof_tac =<< tEvar goal $ map (tVar <<< fst) entry.(ev_nctx)
  end.

(** [simple_tactic t] is a tactic which applies [t] on the main goal (the first in the list).
    [t] returns a list of new goals, which replace the main goal.
    It assumes [t] does not modify the list of goals. *)
Definition simple_tactic {A} (t : evar -> TacticM (A * list evar)) : TacticM A :=
  mlet goals <- get_goals ;;
  match goals with 
  | [] => fail_tac $ str "simple_tactic : no goals"
  | g :: goals => 
    mlet (a, new_goals) <- with_evar_context g (t g) ;;
    set_goals (new_goals ++ goals) ;;
    ret a
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
  (* Unify [forall x : ?a, ?b <=? typeof(goal)]. *)
  mlet concl <- main_concl ;;
  mlet unified <- unify_tac UnifFlags.default Cumul (tProd binder a $ abstract name b) concl ;;
  (if unified then ret tt else fail_tac $ str "intro_tac : goal is not a product") ;;
  (* Set [?goal := fun x : ?a, ?body] *)
  mlet body <- with_named_context body_nctx (fresh_evar "goal" (Some b)) ;;
  assign_tac goal (tLambda binder a $ abstract name body) ;;
  (* Return the name of the introduced variable and the new goal. *)
  ret (name, [get_evar_id body]).

(** [apply_tac t] works on the main goal : it applies the function [t]
    and creates a new goal for each argument of [t]. *)
Definition apply_tac (t : term) : TacticM unit :=
  (* Create an evar for each argument of [t], until [t] applied to the arguments matches the conclusion.
     [args] contains the evars created so far, most recent first.
     [t_ty] is the type of [t] applied to the arguments. *)
  let fix loop (args : list term) (t_ty : term) {struct t_ty} : TacticM (list term) :=
    (* Check if we can apply [t] with the evars created so far. *)
    mlet can_apply <- unify_tac UnifFlags.default Cumul t_ty =<< main_concl ;;
    if can_apply then ret $ rev args else 
    (* Otherwise, create an evar for the next argument of [t] and recurse. *)
    mlet t_ty <- whnf_tac RedFlags.all t_ty ;;
    match t_ty with 
    | tProd x x_ty t_ty =>
      let ev_name := 
        match x.(binder_name) with 
        | nNamed n => n
        | nAnon => "x"
        end 
      in 
      mlet ev <- fresh_evar ev_name (Some $ subst0 args x_ty) ;;
      loop (ev :: args) (subst0 [ev] t_ty)
    (* No more arguments : the application has failed. *)
    | _ => fail_tac $ str "apply_tac : application failed"
    end 
  in 
  simple_tactic $ fun goal => 
  (* Create the arguments. *)
  mlet t_ty <- typeof_tac t ;;
  mlet args <- loop [] t_ty ;;
  (* Apply [t] to the evar arguments and refine the goal. *)
  assign_tac goal (mkApps t args) ;;
  ret (tt, map get_evar_id args).

(** [dest_ind_tac t] checks that [t] is a (declared) inductive applied to _all_ of its 
    parameters and indices, and returns the various components of [t] :
    [(mbody, ibody, ind, uinst, params, indices)]. *)
Definition dest_ind_tac (t : term) : 
  TacticM (mutual_inductive_body * one_inductive_body * inductive * 
           Instance.t * list term * list term) :=
  (* Don't forget to weak head normalize [t]. *)
  mlet t <- whnf_tac RedFlags.all t ;;
  match t with 
  | tApp (tInd ind uinst) args =>
    (* Lookup the inductive. *)
    mlet env <- get_global_env ;;
    match lookup_inductive env ind with 
    | Some (mbody, ibody) => 
      (* Extract the parameters and indices. *)
      if context_assumptions mbody.(ind_params) + context_assumptions ibody.(ind_indices) <=? #|args| 
      then 
        let (params, indices) := chop mbody.(ind_npars) args in
        ret (mbody, ibody, ind, uinst, params, indices)
      else fail_tac $ str "dest_ind_tac : inductive is not fully applied"
    | None => fail_tac $ str "dest_ind_tac : inductive is not declared"
    end
  | _ => fail_tac $ str "dest_ind_tac : not an inductive"
  end.
  
(** [constructor_tac n] works on the main goal : if it is an inductive,
    it applies the [n]-th constructor of this inductive. *)
Definition constructor_tac (n : nat) : TacticM unit :=
  with_main_context $
  (* Check the goal is an inductive fully applied to its parameters and indices. *)
  mlet (mbody, ibody, ind, uinst, _, _) <- dest_ind_tac =<< main_concl ;;
  (* Check the constructor index is valid. *)
  (if n <? #|ibody.(ind_ctors)| then ret tt 
  else fail_tac $ str "constructor_tac : invalid constructor index") ;;
  (* Apply the constructor, with the same universe instance as the goal. *)
  apply_tac (tConstruct ind n uinst).

(** [destruct_tac t] works on the main goal : if [t] is of inductive type,
    it inserts a case expression on [t]. It creates a subgoal for each
    branch. It does not handle dependent elimination (yet). *)
Definition destruct_tac (t : term) : TacticM unit :=
  mlet concl <- main_concl ;;
  simple_tactic $ fun goal =>
  (* Check the type of [t] is an inductive applied to its parameters and indices. *)
  mlet (mbody, ibody, ind, uinst, params, indices) <- dest_ind_tac =<< typeof_tac t ;;
  (* Create a subgoal for each branch. *)
  mlet subgoals <- 
    monad_map 
      (fun ctor => 
        (* The subgoal is a product, i.e. we don't prematurely introduce variables. *)
        let ctx := smash_context [] ctor.(cstr_args) in
        fresh_evar "u" $ Some $ it_mkLambda_or_LetIn ctx concl)
      ibody.(ind_ctors)
  ;;
  (* Assign a case expression to the current goal. *)
  let ci := 
    {| ci_ind := ind 
    ;  ci_npar := mbody.(ind_npars)
    ;  ci_relevance := ibody.(ind_relevance) |}
  in
  (* The return type of the match is simply the conclusion of the main goal. *)
  let pred := 
    {| puinst := uinst 
    ;  pparams := params 
    ;  pcontext := map decl_name ibody.(ind_indices)
    ;  preturn := concl |}
  in
  let branches :=
    map2 
      (fun sg ctor => 
        (* Don't forget to apply each branch evar to the arguments of the constructor. *)
        {| bcontext := map decl_name ctor.(cstr_args) 
        ;  bbody := mkApps sg $ rev $ mapi (fun i _ => tRel i) ctor.(cstr_args) |}) 
      subgoals 
      ibody.(ind_ctors)
  in
  assign_tac goal (tCase ci pred t branches) ;;
  (* Return the list of new goals. *)
  ret (tt, map get_evar_id subgoals).