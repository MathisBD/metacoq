(* Distributed under the terms of the MIT license. *)
(** This defines relation operators in Type *)
From Equations.Type Require Import Relation.
From Equations Require Import Equations.
From Coq Require Import ssreflect Wellfounded Relation_Operators CRelationClasses.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config Environment Primitive EnvironmentTyping Reflect.
From MetaCoq.Template Require Import Ast AstUtils LiftSubst UnivSubst ReflectAst TermEquality WfAst.

Import MCMonadNotation.

(** * Typing derivations

  Inductive relations for reduction, conversion and typing of CIC terms.

 *)

Definition isSort T :=
  match T with
  | tSort u => true
  | _ => false
  end.

Fixpoint isArity T :=
  match T with
  | tSort u => true
  | tProd _ _ codom => isArity codom
  | tLetIn _ _ _ codom => isArity codom
  | _ => false
  end.

Definition type_of_constructor mdecl cdecl (c : inductive * nat) (u : list Level.t) :=
  let mind := inductive_mind (fst c) in
  subst0 (inds mind u mdecl.(ind_bodies)) (subst_instance u cdecl.(cstr_type)).

(** ** Reduction *)

(** *** Helper functions for reduction *)

Definition fix_subst (l : mfixpoint term) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tFix l n :: aux n
      end
  in aux (List.length l).

Definition unfold_fix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d => Some (d.(rarg), subst0 (fix_subst mfix) d.(dbody))
  | None => None
  end.

Definition cofix_subst (l : mfixpoint term) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tCoFix l n :: aux n
      end
  in aux (List.length l).

Definition unfold_cofix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d => Some (d.(rarg), subst0 (cofix_subst mfix) d.(dbody))
  | None => None
  end.

Definition is_constructor n ts :=
  match List.nth_error ts n with
  | Some a => isConstruct_app a
  | None => false
  end.

Lemma fix_subst_length mfix : #|fix_subst mfix| = #|mfix|.
Proof.
  unfold fix_subst. generalize (tFix mfix). intros.
  induction mfix; simpl; auto.
Qed.

Lemma cofix_subst_length mfix : #|cofix_subst mfix| = #|mfix|.
Proof.
  unfold cofix_subst. generalize (tCoFix mfix). intros.
  induction mfix; simpl; auto.
Qed.

Definition fix_context (m : mfixpoint term) : context :=
  List.rev (mapi (fun i d => vass d.(dname) (lift0 i d.(dtype))) m).

Lemma fix_context_length mfix : #|fix_context mfix| = #|mfix|.
Proof. unfold fix_context. now rewrite List.length_rev mapi_length. Qed.

Definition dummy_branch : branch term := mk_branch [] tDummy.

Definition iota_red npar args bctx br :=
  subst (List.rev (List.skipn npar args)) 0 (expand_lets bctx br.(bbody)).

(** For cases typing *)

Inductive instantiate_params_subst_spec : context -> list term -> list term -> term -> list term -> term -> Prop :=
| instantiate_params_subst_nil s ty : instantiate_params_subst_spec [] [] s ty s ty
| instantiate_params_subst_vass na ty params pari pars s na' ty' pty s' pty' :
  instantiate_params_subst_spec params pars (pari :: s) pty s' pty' ->
  instantiate_params_subst_spec (vass na ty :: params) (pari :: pars) s (tProd na' ty' pty) s' pty'
| instantiate_params_subst_vdef na b ty params pars s na' b' ty' pty s' pty' :
  instantiate_params_subst_spec params pars (subst s 0 b :: s) pty s' pty' ->
  instantiate_params_subst_spec (vdef na b ty :: params) pars s (tLetIn na' b' ty' pty) s' pty'.
Derive Signature for instantiate_params_subst_spec.


(** Compute the type of a case from the predicate [p], actual parameters [pars] and
    an inductive declaration. *)

Fixpoint instantiate_params_subst
         (params : context)
         (pars s : list term)
         (ty : term) : option (list term × term) :=
  match params with
  | [] => match pars with
          | [] => Some (s, ty)
          | _ :: _ => None (* Too many arguments to substitute *)
          end
  | d :: params =>
    match d.(decl_body), ty with
    | None, tProd _ _ B =>
      match pars with
      | hd :: tl => instantiate_params_subst params tl (hd :: s) B
      | [] => None (* Not enough arguments to substitute *)
      end
    | Some b, tLetIn _ _ _ b' => instantiate_params_subst params pars (subst0 s b :: s) b'
    | _, _ => None (* Not enough products in the type *)
    end
  end.

Lemma instantiate_params_substP params pars s ty s' ty' :
  instantiate_params_subst params pars s ty = Some (s', ty') <->
  instantiate_params_subst_spec params pars s ty s' ty'.
Proof.
  induction params in pars, s, ty |- *.
  - split. destruct pars => /= // => [= -> ->].
    constructor.
    intros. depelim H. reflexivity.
  - split.
    * destruct a as [na [b|] ?] => /=.
      destruct ty => //.
      move/IHparams.
      intros. now constructor.
      destruct ty => //.
      destruct pars => //.
      move/IHparams.
      now constructor.
    * intros H; depelim H; simpl.
      now apply IHparams.
      now apply IHparams.
Qed.

(** *** One step strong beta-zeta-iota-fix-delta reduction

  Inspired by the reduction relation from Coq in Coq [Barras'99].
*)

Fixpoint nctx_lookup (Δ : named_context) (id : ident) : option context_decl :=
  match Δ with 
  | (id', decl) :: Δ => if id == id' then Some decl else nctx_lookup Δ id
  | [] => None
  end.

Local Open Scope type_scope.
Arguments OnOne2 {A} P%_type l l'.

(* NOTE: SPROP: we ignore relevance in the reduction  for now *)
Inductive red1 (Σ : global_env) (Δ : named_context) (Γ : context) : term -> term -> Type :=
(** Reductions *)
(** Beta *)
| red_beta na t b a l :
    red1 Σ Δ Γ (tApp (tLambda na t b) (a :: l)) (mkApps (subst10 a b) l)

(** Let *)
| red_zeta na b t b' :
    red1 Σ Δ Γ (tLetIn na b t b') (subst10 b b')

(** Rel *)

| red_rel i body :
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    red1 Σ Δ Γ (tRel i) (lift0 (S i) body)

(** Var *)

| red_var id body :
    option_map decl_body (nctx_lookup Δ id) = Some (Some body) ->
    (* The body should not contain any unbound Rel. *)
    red1 Σ Δ Γ (tVar id) body

(** Case *)
| red_iota ci mdecl idecl cdecl c u args p brs br :
    nth_error brs c = Some br ->
    (* In the compact representation, reduction must fetch the
       global declaration of the constructor to gather the let-bindings
       in its argument context. Implementations can be more clever
       in the common case where no let-binding appears to avoid this. *)
    declared_constructor Σ (ci.(ci_ind), c) mdecl idecl cdecl ->
    let bctx := case_branch_context ci.(ci_ind) mdecl cdecl p br in
    #|args| = (ci.(ci_npar) + context_assumptions bctx)%nat ->
    red1 Σ Δ Γ (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
         (iota_red ci.(ci_npar) args bctx br)

(** Fix unfolding, with guard *)
| red_fix mfix idx args narg fn :
    unfold_fix mfix idx = Some (narg, fn) ->
    is_constructor narg args = true ->
    red1 Σ Δ Γ (tApp (tFix mfix idx) args) (mkApps fn args)

(** CoFix-case unfolding *)
| red_cofix_case ip p mfix idx args narg fn brs :
    unfold_cofix mfix idx = Some (narg, fn) ->
    red1 Σ Δ Γ (tCase ip p (mkApps (tCoFix mfix idx) args) brs)
         (tCase ip p (mkApps fn args) brs)

(** CoFix-proj unfolding *)
| red_cofix_proj p mfix idx args narg fn :
    unfold_cofix mfix idx = Some (narg, fn) ->
    red1 Σ Δ Γ (tProj p (mkApps (tCoFix mfix idx) args))
         (tProj p (mkApps fn args))

(** Constant unfolding *)
| red_delta c decl body (isdecl : declared_constant Σ c decl) u :
    decl.(cst_body) = Some body ->
    red1 Σ Δ Γ (tConst c u) (subst_instance u body)

(** Proj *)
| red_proj p u args arg:
    nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
    red1 Σ Δ Γ (tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args)) arg


| abs_red_l na M M' N : red1 Σ Δ Γ M M' -> red1 Σ Δ Γ (tLambda na M N) (tLambda na M' N)
| abs_red_r na M M' N : red1 Σ Δ (Γ ,, vass na N) M M' -> red1 Σ Δ Γ (tLambda na N M) (tLambda na N M')

| letin_red_def na b t b' r : red1 Σ Δ Γ b r -> red1 Σ Δ Γ (tLetIn na b t b') (tLetIn na r t b')
| letin_red_ty na b t b' r : red1 Σ Δ Γ t r -> red1 Σ Δ Γ (tLetIn na b t b') (tLetIn na b r b')
| letin_red_body na b t b' r : red1 Σ Δ (Γ ,, vdef na b t) b' r -> red1 Σ Δ Γ (tLetIn na b t b') (tLetIn na b t r)

| case_red_pred_param ind params params' puinst pcontext preturn c brs :
    OnOne2 (red1 Σ Δ Γ) params params' ->
    red1 Σ Δ Γ (tCase ind (mk_predicate puinst params pcontext preturn) c brs)
               (tCase ind (mk_predicate puinst params' pcontext preturn) c brs)

| case_red_pred_return ind mdecl idecl (isdecl : declared_inductive Σ ind.(ci_ind) mdecl idecl)
                       params puinst pcontext preturn preturn' c brs :
    let p := {| pparams := params; puinst := puinst; pcontext := pcontext; preturn := preturn |} in
    let p' := {| pparams := params; puinst := puinst; pcontext := pcontext; preturn := preturn' |} in
    red1 Σ Δ (Γ ,,, case_predicate_context ind.(ci_ind) mdecl idecl p) preturn preturn' ->
    red1 Σ Δ Γ (tCase ind p c brs)
               (tCase ind p' c brs)

| case_red_discr ind p c c' brs : red1 Σ Δ Γ c c' -> red1 Σ Δ Γ (tCase ind p c brs) (tCase ind p c' brs)

| case_red_brs ind mdecl idecl (isdecl : declared_inductive Σ ind.(ci_ind) mdecl idecl) p c brs brs' :
    OnOne2All (fun brctx br br' =>
      on_Trel_eq (red1 Σ Δ (Γ ,,, brctx)) bbody bcontext br br')
      (case_branches_contexts ind.(ci_ind) mdecl idecl p brs) brs brs' ->
    red1 Σ Δ Γ (tCase ind p c brs) (tCase ind p c brs')

| proj_red p c c' : red1 Σ Δ Γ c c' -> red1 Σ Δ Γ (tProj p c) (tProj p c')

| app_red_l M1 N1 M2 : red1 Σ Δ Γ M1 N1 -> red1 Σ Δ Γ (tApp M1 M2) (mkApps N1 M2)
| app_red_r M2 N2 M1 : OnOne2 (red1 Σ Δ Γ) M2 N2 -> red1 Σ Δ Γ (tApp M1 M2) (tApp M1 N2)

| prod_red_l na M1 M2 N1 : red1 Σ Δ Γ M1 N1 -> red1 Σ Δ Γ (tProd na M1 M2) (tProd na N1 M2)
| prod_red_r na M2 N2 M1 : red1 Σ Δ (Γ ,, vass na M1) M2 N2 ->
                               red1 Σ Δ Γ (tProd na M1 M2) (tProd na M1 N2)

| evar_red ev l l' : OnOne2 (red1 Σ Δ Γ) l l' -> red1 Σ Δ Γ (tEvar ev l) (tEvar ev l')

| cast_red_l M1 k M2 N1 : red1 Σ Δ Γ M1 N1 -> red1 Σ Δ Γ (tCast M1 k M2) (tCast N1 k M2)
| cast_red_r M2 k N2 M1 : red1 Σ Δ Γ M2 N2 -> red1 Σ Δ Γ (tCast M1 k M2) (tCast M1 k N2)
| cast_red M1 k M2 : red1 Σ Δ Γ (tCast M1 k M2) M1

| fix_red_ty mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (red1 Σ Δ Γ) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
    red1 Σ Δ Γ (tFix mfix0 idx) (tFix mfix1 idx)

| fix_red_body mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (red1 Σ Δ (Γ ,,, fix_context mfix0)) dbody (fun x => (dname x, dtype x, rarg x)))
      mfix0 mfix1 ->
    red1 Σ Δ Γ (tFix mfix0 idx) (tFix mfix1 idx)

| cofix_red_ty mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (red1 Σ Δ Γ) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
    red1 Σ Δ Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)

| cofix_red_body mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (red1 Σ Δ (Γ ,,, fix_context mfix0)) dbody (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
    red1 Σ Δ Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)

| array_red_val l v v' d ty :
    OnOne2 (fun t u => red1 Σ Δ Γ t u) v v' ->
    red1 Σ Δ Γ (tArray l v d ty) (tArray l v' d ty)

| array_red_def l v d d' ty :
    red1 Σ Δ Γ d d' ->
    red1 Σ Δ Γ (tArray l v d ty) (tArray l v d' ty)

| array_red_type l v d ty ty' :
    red1 Σ Δ Γ ty ty' ->
    red1 Σ Δ Γ (tArray l v d ty) (tArray l v d ty').

Lemma red1_ind_all :
  forall (Σ : global_env) (Δ : named_context) (P : context -> term -> term -> Type),
       (forall (Γ : context) (na : aname) (t b a : term) (l : list term),
        P Γ (tApp (tLambda na t b) (a :: l)) (mkApps (b {0 := a}) l)) ->
       (forall (Γ : context) (na : aname) (b t b' : term), P Γ (tLetIn na b t b') (b' {0 := b})) ->

       (forall (Γ : context) (i : nat) (body : term),
        option_map decl_body (nth_error Γ i) = Some (Some body) -> P Γ (tRel i) ((lift0 (S i)) body)) ->

       (forall (Γ : context) (id : ident) (body : term),
        option_map decl_body (nctx_lookup Δ id) = Some (Some body) -> P Γ (tVar id) body) ->

       (forall (Γ : context) (ci : case_info) mdecl idecl cdecl (c : nat) (u : Instance.t) (args : list term)
          (p : predicate term) (brs : list (branch term)) br,
          nth_error brs c = Some br ->
          declared_constructor Σ (ci.(ci_ind), c) mdecl idecl cdecl ->
          let bctx := case_branch_context ci.(ci_ind) mdecl cdecl p br in
          #|args| = (ci.(ci_npar) + context_assumptions bctx)%nat ->
          P Γ (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
                (iota_red ci.(ci_npar) args bctx br)) ->

       (forall (Γ : context) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn : term),
        unfold_fix mfix idx = Some (narg, fn) ->
        is_constructor narg args = true -> P Γ (tApp (tFix mfix idx) args) (mkApps fn args)) ->

       (forall (Γ : context) (ip : case_info) (p : predicate term) (mfix : mfixpoint term) (idx : nat)
          (args : list term) (narg : nat) (fn : term) (brs : list (branch term)),
        unfold_cofix mfix idx = Some (narg, fn) ->
        P Γ (tCase ip p (mkApps (tCoFix mfix idx) args) brs) (tCase ip p (mkApps fn args) brs)) ->

       (forall (Γ : context) (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term)
          (narg : nat) (fn : term),
        unfold_cofix mfix idx = Some (narg, fn) -> P Γ (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args))) ->

       (forall (Γ : context) c (decl : constant_body) (body : term),
        declared_constant Σ c decl ->
        forall u : Instance.t, cst_body decl = Some body -> P Γ (tConst c u) (subst_instance u body)) ->

       (forall (Γ : context) p (args : list term) (u : Instance.t) (arg : term),
           nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
           P Γ (tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args)) arg) ->

       (forall (Γ : context) (na : aname) (M M' N : term),
        red1 Σ Δ Γ M M' -> P Γ M M' -> P Γ (tLambda na M N) (tLambda na M' N)) ->

       (forall (Γ : context) (na : aname) (M M' N : term),
        red1 Σ Δ (Γ,, vass na N) M M' -> P (Γ,, vass na N) M M' -> P Γ (tLambda na N M) (tLambda na N M')) ->

       (forall (Γ : context) (na : aname) (b t b' r : term),
        red1 Σ Δ Γ b r -> P Γ b r -> P Γ (tLetIn na b t b') (tLetIn na r t b')) ->

       (forall (Γ : context) (na : aname) (b t b' r : term),
        red1 Σ Δ Γ t r -> P Γ t r -> P Γ (tLetIn na b t b') (tLetIn na b r b')) ->

       (forall (Γ : context) (na : aname) (b t b' r : term),
        red1 Σ Δ (Γ,, vdef na b t) b' r -> P (Γ,, vdef na b t) b' r -> P Γ (tLetIn na b t b') (tLetIn na b t r)) ->

       (forall (Γ : context) (ind : case_info) params params' puinst pcontext preturn c brs,
           OnOne2 (Trel_conj (red1 Σ Δ Γ) (P Γ)) params params' ->
           P Γ (tCase ind (mk_predicate puinst params pcontext preturn) c brs)
               (tCase ind (mk_predicate puinst params' pcontext preturn) c brs)) ->

       (forall (Γ : context) (ci : case_info)
               idecl mdecl (isdecl : declared_inductive Σ ci.(ci_ind) mdecl idecl)
               params puinst pcontext preturn preturn' c brs,
          let p := (mk_predicate puinst params pcontext preturn) in
           red1 Σ Δ (Γ ,,, case_predicate_context ci.(ci_ind) mdecl idecl p) preturn preturn' ->
           P (Γ ,,, case_predicate_context ci.(ci_ind) mdecl idecl p) preturn preturn' ->
           P Γ (tCase ci p c brs)
               (tCase ci (mk_predicate puinst params pcontext preturn') c brs)) ->

       (forall (Γ : context) (ind : case_info) (p : predicate term) (c c' : term) (brs : list (branch term)),
        red1 Σ Δ Γ c c' -> P Γ c c' -> P Γ (tCase ind p c brs) (tCase ind p c' brs)) ->

       (forall (Γ : context) ind mdecl idecl (isdecl : declared_inductive Σ ind.(ci_ind) mdecl idecl) p c brs brs',
          OnOne2All (fun brctx br br' =>
            on_Trel_eq (Trel_conj (red1 Σ Δ (Γ ,,, brctx)) (P (Γ ,,, brctx))) bbody bcontext br br')
              (case_branches_contexts ind.(ci_ind) mdecl idecl p brs) brs brs' ->
          P Γ (tCase ind p c brs) (tCase ind p c brs')) ->

       (forall (Γ : context) (p : projection) (c c' : term), red1 Σ Δ Γ c c' -> P Γ c c' -> P Γ (tProj p c) (tProj p c')) ->

       (forall (Γ : context) (M1 N1 : term) (M2 : list term), red1 Σ Δ Γ M1 N1 -> P Γ M1 N1 -> P Γ (tApp M1 M2) (mkApps N1 M2)) ->

       (forall (Γ : context) (M2 N2 : list term) (M1 : term), OnOne2 (fun x y => red1 Σ Δ Γ x y * P Γ x y)%type M2 N2 -> P Γ (tApp M1 M2) (tApp M1 N2)) ->

       (forall (Γ : context) (na : aname) (M1 M2 N1 : term),
        red1 Σ Δ Γ M1 N1 -> P Γ M1 N1 -> P Γ (tProd na M1 M2) (tProd na N1 M2)) ->

       (forall (Γ : context) (na : aname) (M2 N2 M1 : term),
        red1 Σ Δ (Γ,, vass na M1) M2 N2 -> P (Γ,, vass na M1) M2 N2 -> P Γ (tProd na M1 M2) (tProd na M1 N2)) ->

       (forall (Γ : context) (ev : nat) (l l' : list term), OnOne2 (fun x y => red1 Σ Δ Γ x y * P Γ x y) l l' -> P Γ (tEvar ev l) (tEvar ev l')) ->

       (forall (Γ : context) (M1 : term) (k : cast_kind) (M2 N1 : term),
        red1 Σ Δ Γ M1 N1 -> P Γ M1 N1 -> P Γ (tCast M1 k M2) (tCast N1 k M2)) ->

       (forall (Γ : context) (M2 : term) (k : cast_kind) (N2 M1 : term),
        red1 Σ Δ Γ M2 N2 -> P Γ M2 N2 -> P Γ (tCast M1 k M2) (tCast M1 k N2)) ->

       (forall (Γ : context) (M1 : term) (k : cast_kind) (M2 : term),
           P Γ (tCast M1 k M2) M1) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
          OnOne2 (on_Trel_eq (Trel_conj (red1 Σ Δ Γ) (P Γ)) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
          P Γ (tFix mfix0 idx) (tFix mfix1 idx)) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
          OnOne2 (on_Trel_eq (Trel_conj (red1 Σ Δ (Γ ,,, fix_context mfix0))
          (P (Γ ,,, fix_context mfix0))) dbody
            (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
          P Γ (tFix mfix0 idx) (tFix mfix1 idx)) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ Δ Γ) (P Γ)) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
        P Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
          OnOne2 (on_Trel_eq (Trel_conj (red1 Σ Δ (Γ ,,, fix_context mfix0))
          (P (Γ ,,, fix_context mfix0))) dbody
         (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
        P Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->

      (forall Γ l v v' d ty,
         OnOne2 (fun t u => Trel_conj (red1 Σ Δ Γ) (P Γ) t u) v v' ->
         P Γ (tArray l v d ty) (tArray l v' d ty)) ->

      (forall Γ l v d d' ty,
      red1 Σ Δ Γ d d' -> P Γ d d' -> P Γ (tArray l v d ty) (tArray l v d' ty)) ->

      (forall Γ l v d ty ty',
        red1 Σ Δ Γ ty ty' -> P Γ ty ty' -> P Γ (tArray l v d ty) (tArray l v d ty')) ->

       forall (Γ : context) (t t0 : term), red1 Σ Δ Γ t t0 -> P Γ t t0.
Proof.
  intros. rename X34 into Xlast. revert Γ t t0 Xlast.
  fix aux 4. intros Γ t T.
  move aux at top.
  destruct 1;
    try solve [
          match goal with
          | H : _ |- _ => eapply H; eauto; fail
          end].
 
  - apply X14.
    revert params params' o.
    fix auxl 3.
    intros params params' [].
    + constructor. split; auto.
    + constructor. auto.

  - eapply X17; eauto.
    revert brs brs' o.
    intros brs.
    generalize (case_branches_contexts (ci_ind ind) mdecl idecl p brs).
    revert brs.
    fix auxl 4.
    intros i l l' Hl. destruct Hl.
    + constructor; intros.
      intuition auto. auto.
    + constructor. eapply auxl. apply Hl.

  - apply X20.
    revert M2 N2 o.
    fix auxl 3.
    intros l l' Hl. destruct Hl.
    + constructor. split; auto.
    + constructor. auto.

  - apply X23.
    revert l l' o.
    fix auxl 3.
    intros l l' Hl. destruct Hl.
    constructor. split; auto.
    constructor. auto.

  - apply X27.
    revert mfix0 mfix1 o; fix auxl 3; intros l l' Hl; destruct Hl;
      constructor; try split; auto; intuition.

  - apply X28.
    revert o. generalize (fix_context mfix0). intros c H28.
    revert mfix0 mfix1 H28; fix auxl 3; intros l l' Hl;
    destruct Hl; constructor; try split; auto; intuition.

  - eapply X29.
    revert mfix0 mfix1 o; fix auxl 3; intros l l' Hl; destruct Hl;
      constructor; try split; auto; intuition.

  - eapply X30.
    revert o. generalize (fix_context mfix0). intros c H28.
    revert mfix0 mfix1 H28; fix auxl 3; intros l l' Hl; destruct Hl;
      constructor; try split; auto; intuition.

  - eapply X31.
    revert v v' o. fix auxl 3; intros ? ? Hl; destruct Hl;
      constructor; try split; auto; intuition.
Defined.

(** *** Reduction

  The reflexive-transitive closure of 1-step reduction. *)

Inductive red Σ Δ Γ M : term -> Type :=
| refl_red : red Σ Δ Γ M M
| trans_red : forall (P : term) N, red Σ Δ Γ M P -> red1 Σ Δ Γ P N -> red Σ Δ Γ M N.

(** ** Term equality and cumulativity *)

(* ** Syntactic equality up-to universes

  We shouldn't look at printing annotations nor casts.
  It is however not possible to write a structurally recursive definition
  for syntactic equality up-to casts due to the [tApp (tCast f _ _) args] case.
  We hence implement first an equality which considers casts and do a stripping
  phase of casts before checking equality. *)

Definition eq_term_nocast `{checker_flags} (Σ : global_env) (φ : ConstraintSet.t) (t u : term) :=
  eq_term Σ φ (strip_casts t) (strip_casts u).

Definition leq_term_nocast `{checker_flags} (Σ : global_env) (φ : ConstraintSet.t) (t u : term) :=
  leq_term Σ φ (strip_casts t) (strip_casts u).

Reserved Notation " Σ ;;; Δ ;;; Γ |- t : T " (at level 50, Δ, Γ, t, T at next level).
Reserved Notation " Σ ;;; Δ ;;; Γ |- t <=[ pb ] u " (at level 50, Δ, Γ, t, u at next level).

(** ** Cumulativity:

  Reduction to terms in the cumulativity relation. In PCUIC we show that
  this is equivalent to the reflexive-transitive closure or reduction + leq_term
  on well-typed terms.
*)

Inductive cumul_gen `{checker_flags} (Σ : global_env_ext) (Δ : named_context) (Γ : context) (pb : conv_pb) : term -> term -> Type :=
 | cumul_refl t u : compare_term Σ (global_ext_constraints Σ) pb t u -> Σ ;;; Δ ;;; Γ |- t <=[pb] u
 | cumul_red_l t u v : red1 Σ.1 Δ Γ t v -> Σ ;;; Δ ;;; Γ |- v <=[pb] u -> Σ ;;; Δ ;;; Γ |- t <=[pb] u
 | cumul_red_r t u v : Σ ;;; Δ ;;; Γ |- t <=[pb] v -> red1 Σ.1 Δ Γ u v -> Σ ;;; Δ ;;; Γ |- t <=[pb] u
  where "Σ ;;; Δ ;;; Γ |- t <=[ pb ] u " := (cumul_gen Σ Δ Γ pb t u).

(** *** Conversion

  Reduction to terms in the eq_term relation
 *)

Notation " Σ ;;; Δ ;;; Γ |- t = u "  := (cumul_gen Σ Δ Γ Conv t u)  (at level 50, Δ, Γ, t, u at next level) : type_scope.
Notation " Σ ;;; Δ ;;; Γ |- t <= u " := (cumul_gen Σ Δ Γ Cumul t u) (at level 50, Δ, Γ, t, u at next level) : type_scope.

Lemma conv_refl' `{checker_flags} : forall Σ Δ Γ t, Σ ;;; Δ ;;; Γ |- t = t.
  intros. constructor. apply eq_term_refl.
Defined.

Lemma cumul_refl' `{checker_flags} : forall Σ Δ Γ t, Σ ;;; Δ ;;; Γ |- t <= t.
  intros. constructor. apply leq_term_refl.
Defined.

Definition eq_opt_term `{checker_flags} Σ φ (t u : option term) :=
  match t, u with
  | Some t, Some u => eq_term Σ φ t u
  | None, None => True
  | _, _ => False
  end.

Definition eq_decl `{checker_flags} Σ φ (d d' : context_decl) :=
  eq_opt_term Σ φ d.(decl_body) d'.(decl_body) * eq_term Σ φ d.(decl_type) d'.(decl_type).

Definition eq_context `{checker_flags} Σ φ (Γ Γ' : context) :=
  All2 (eq_decl Σ φ) Γ Γ'.

Definition eq_nctx `{checker_flags} Σ φ (Δ Δ' : named_context) :=
  All2 (fun '(id, d) '(id', d') => (id = id') * eq_decl Σ φ d d') Δ Δ'.

(** ** Typing relation *)

Module TemplateEnvTyping := EnvTyping TemplateTerm Env TemplateTermUtils.
Include TemplateEnvTyping.

Module TemplateConversion := Conversion TemplateTerm Env TemplateTermUtils TemplateEnvTyping.
Include TemplateConversion.

Module TemplateGlobalMaps := GlobalMaps TemplateTerm Env TemplateTermUtils TemplateEnvTyping TemplateConversion TemplateLookup.
Include TemplateGlobalMaps.

Module TemplateConversionPar <: ConversionParSig TemplateTerm Env TemplateTermUtils TemplateEnvTyping.
  Definition cumul_gen := @cumul_gen.
End TemplateConversionPar.

(* TODO : add rules for named contexts. *)
Class GuardChecker :=
{ (* Structural recursion check *)
  fix_guard : global_env_ext -> named_context -> context -> mfixpoint term -> bool ;
  (* Guarded by destructors check *)
  cofix_guard : global_env_ext -> named_context -> context -> mfixpoint term -> bool ;

  fix_guard_red1 Σ Δ Γ mfix mfix' idx :
      fix_guard Σ Δ Γ mfix ->
      red1 Σ Δ Γ (tFix mfix idx) (tFix mfix' idx) ->
      fix_guard Σ Δ Γ mfix' ;

  fix_guard_lift Σ Δ Γ Γ' Γ'' mfix :
    let k' := (#|mfix| + #|Γ'|)%nat in
    let mfix' := map (map_def (lift #|Γ''| #|Γ'|) (lift #|Γ''| k')) mfix in
    fix_guard Σ Δ (Γ ,,, Γ') mfix ->
    fix_guard Σ Δ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') mfix' ;

  (*
  fix_guard_lift' Σ Δ Δ' Δ'' Γ mfix :
    fix_guard Σ (Δ ,,, Δ') Γ mfix ->
    fix_guard Σ (Δ ,,, Δ'' ,,, Δ') Γ mfix ;*)

  fix_guard_subst Σ Δ Γ Γ' Γ0 mfix s k :
    let k' := (#|mfix| + k)%nat in
    let mfix' := map (map_def (subst s k) (subst s k')) mfix in
    fix_guard Σ Δ (Γ ,,, Γ' ,,, Γ0) mfix ->
    fix_guard Σ Δ (Γ ,,, subst_context s 0 Γ0) mfix' ;

  fix_guard_subst_instance {cf:checker_flags} Σ Δ Γ mfix u univs :
    consistent_instance_ext (Σ.1, univs) Σ.2 u ->
    fix_guard Σ Δ Γ mfix ->
    fix_guard (Σ.1, univs) Δ (subst_instance u Γ) (map (map_def (subst_instance u) (subst_instance u))
                    mfix) ;

  fix_guard_extends Σ Δ Γ mfix (Σ' : global_env_ext) :
    fix_guard Σ Δ Γ mfix ->
    extends Σ.1 Σ' ->
    fix_guard Σ' Δ Γ mfix ;

  cofix_guard_red1 Σ Δ Γ mfix mfix' idx :
    cofix_guard Σ Δ Γ mfix ->
    red1 Σ Δ Γ (tCoFix mfix idx) (tCoFix mfix' idx) ->
    cofix_guard Σ Δ Γ mfix' ;

  cofix_guard_lift Σ Δ Γ Γ' Γ'' mfix :
    let k' := (#|mfix| + #|Γ'|)%nat in
    let mfix' := map (map_def (lift #|Γ''| #|Γ'|) (lift #|Γ''| k')) mfix in
    cofix_guard Σ Δ (Γ ,,, Γ') mfix ->
    cofix_guard Σ Δ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') mfix' ;

  cofix_guard_subst Σ Δ Γ Γ' Γ0 mfix s k :
    let k' := (#|mfix| + k)%nat in
    let mfix' := map (map_def (subst s k) (subst s k')) mfix in
    cofix_guard Σ Δ (Γ ,,, Γ' ,,, Γ0) mfix ->
    cofix_guard Σ Δ (Γ ,,, subst_context s 0 Γ0) mfix' ;

  cofix_guard_subst_instance {cf:checker_flags} Σ Δ Γ mfix u univs :
    consistent_instance_ext (Σ.1, univs) Σ.2 u ->
    cofix_guard Σ Δ Γ mfix ->
    cofix_guard (Σ.1, univs) Δ (subst_instance u Γ) (map (map_def (subst_instance u) (subst_instance u))
                    mfix) ;

  cofix_guard_extends Σ Δ Γ mfix (Σ' : global_env_ext) :
    cofix_guard Σ Δ Γ mfix ->
    extends Σ.1 Σ' ->
    cofix_guard Σ' Δ Γ mfix }.

(* AXIOM GUARD CONDITION *)
Axiom guard_checking : GuardChecker.
Global Existing Instance guard_checking.

(*
Definition build_branch_context ind mdecl (cty: term) p : option context :=
  let inds := inds ind.(inductive_mind) p.(puinst) mdecl.(ind_bodies) in
  let ty := subst0 inds (subst_instance p.(puinst) cty) in
  match instantiate_params (subst_instance p.(puinst) mdecl.(ind_params)) p.(pparams) ty with
  | Some ty =>
    let '(sign, ccl) := decompose_prod_assum [] ty in
    Some sign
  | None => None
  end.

(* [params], [p] and output are already instanciated by [u] *)
Definition build_branches_type ind mdecl idecl params u p : list (option (nat * context * term)) :=
  let inds := inds ind.(inductive_mind) u mdecl.(ind_bodies) in
  let branch_type i '(id, t, ar) :=
    let ty := subst0 inds (subst_instance u t) in
    match instantiate_params (subst_instance u mdecl.(ind_params)) params ty with
    | Some ty =>
      let '(sign, ccl) := decompose_prod_assum [] ty in
      let nargs := List.length sign in
      let allargs := snd (decompose_app ccl) in
      let '(paramrels, args) := chop mdecl.(ind_npars) allargs in
      let cstr := tConstruct ind i u in
      let args := (args ++ [mkApps cstr (paramrels ++ to_extended_list sign)]) in
      Some (ar, sign, mkApps (lift0 nargs p) args)
    | None => None
    end
  in mapi branch_type idecl.(ind_ctors).

Lemma build_branches_type_ ind mdecl idecl params u p :
  build_branches_type ind mdecl idecl params u p
  = let inds := inds ind.(inductive_mind) u mdecl.(ind_bodies) in
    let branch_type i '(id, t, ar) :=
        let ty := subst0 inds (subst_instance u t) in
        option_map (fun ty =>
         let '(sign, ccl) := decompose_prod_assum [] ty in
         let nargs := List.length sign in
         let allargs := snd (decompose_app ccl) in
         let '(paramrels, args) := chop mdecl.(ind_npars) allargs in
         let cstr := tConstruct ind i u in
         let args := (args ++ [mkApps cstr (paramrels ++ to_extended_list sign)]) in
         (ar, sign, (mkApps (lift0 nargs p) args)))
                  (instantiate_params (subst_instance u mdecl.(ind_params))
                                      params ty)
    in mapi branch_type idecl.(ind_ctors).
Proof.
  apply mapi_ext. intros ? [[? ?] ?]; cbnr.
  repeat (destruct ?; cbnr).
Qed.
*)
Definition destInd (t : term) :=
  match t with
  | tInd ind u => Some (ind, u)
  | _ => None
  end.

Definition isFinite (r : recursivity_kind) :=
  match r with
  | Finite => true
  | _ => false
  end.

Definition isCoFinite (r : recursivity_kind) :=
  match r with
  | CoFinite => true
  | _ => false
  end.

Definition check_recursivity_kind (Σ : global_env) ind r :=
  match lookup_env Σ ind with
  | Some (InductiveDecl mib) => eqb mib.(ind_finite) r
  | _ => false
  end.

Definition check_one_fix d :=
  let '{| dname := na;
          dtype := ty;
          dbody := b;
          rarg := arg |} := d in
  let '(ctx, ty) := decompose_prod_assum [] ty in
  match nth_error (List.rev (smash_context [] ctx)) arg with
  | Some argd =>
    let (hd, args) := decompose_app argd.(decl_type) in
    match destInd hd with
    | Some (mkInd mind _, u) => Some mind
    | None => None (* Not recursive on an inductive type *)
    end
  | None => None (* Recursive argument not found *)
  end.

Definition wf_fixpoint (Σ : global_env) mfix :=
  forallb (isLambda ∘ dbody) mfix &&
  let checks := map check_one_fix mfix in
  match map_option_out checks with
  | Some (ind :: inds) =>
    (* Check that mutually recursive fixpoints are all on the same mututal
        inductive block *)
    forallb (eqb ind) inds &&
    check_recursivity_kind Σ ind Finite
  | _ => false
  end.

Definition check_one_cofix d :=
  let '{| dname := na;
          dtype := ty;
          dbody := b;
          rarg := arg |} := d in
  let '(ctx, ty) := decompose_prod_assum [] ty in
  let (hd, args) := decompose_app ty in
  match destInd hd with
  | Some (mkInd ind _, u) => Some ind
  | None => None (* Not recursive on an inductive type *)
  end.

Definition wf_cofixpoint (Σ : global_env) mfix :=
  let checks := map check_one_cofix mfix in
  match map_option_out checks with
  | Some (ind :: inds) =>
    (* Check that mutually recursive cofixpoints are all producing
        coinductives in the same mututal coinductive block *)
    forallb (eqb ind) inds &&
    check_recursivity_kind Σ ind CoFinite
  | _ => false
  end.

Reserved Notation "'wf_named' Σ Δ " (at level 9, Σ, Δ at next level).
Reserved Notation "'wf_local' Σ Δ Γ " (at level 9, Σ, Δ, Γ at next level).

Inductive typing `{checker_flags} (Σ : global_env_ext) (Δ : named_context) (Γ : context) : term -> term -> Type :=
| type_Rel n decl :
    wf_named Σ Δ -> wf_local Σ Δ Γ ->
    nth_error Γ n = Some decl ->
    Σ ;;; Δ ;;; Γ |- tRel n : lift0 (S n) decl.(decl_type)

| type_Var id decl : 
    wf_named Σ Δ -> wf_local Σ Δ Γ ->
    nctx_lookup Δ id = Some decl ->
    Σ ;;; Δ ;;; Γ |- tVar id : decl.(decl_type)

| type_Sort s :
    wf_named Σ Δ -> wf_local Σ Δ Γ ->
    wf_sort Σ s ->
    Σ ;;; Δ ;;; Γ |- tSort s : tSort (Sort.super s)

| type_Cast c k t s :
    Σ ;;; Δ ;;; Γ |- t : tSort s ->
    Σ ;;; Δ ;;; Γ |- c : t ->
    Σ ;;; Δ ;;; Γ |- tCast c k t : t

| type_Prod na t b s1 s2 :
    lift_typing3 typing Σ Δ Γ (j_vass_s na t s1) ->
    Σ ;;; Δ ;;; Γ ,, vass na t |- b : tSort s2 ->
    Σ ;;; Δ ;;; Γ |- tProd na t b : tSort (Sort.sort_of_product s1 s2)

| type_Lambda na t b bty :
    lift_typing3 typing Σ Δ Γ (j_vass na t) ->
    Σ ;;; Δ ;;; Γ ,, vass na t |- b : bty ->
    Σ ;;; Δ ;;; Γ |- tLambda na t b : tProd na t bty

| type_LetIn na b b_ty b' b'_ty :
    lift_typing3 typing Σ Δ Γ (j_vdef na b b_ty) ->
    Σ ;;; Δ ;;; Γ ,, vdef na b b_ty |- b' : b'_ty ->
    Σ ;;; Δ ;;; Γ |- tLetIn na b b_ty b' : tLetIn na b b_ty b'_ty

| type_App t l t_ty t' :
    Σ ;;; Δ ;;; Γ |- t : t_ty ->
    isApp t = false -> l <> [] -> (* Well-formed application *)
    typing_spine Σ Δ Γ t_ty l t' ->
    Σ ;;; Δ ;;; Γ |- tApp t l : t'

| type_Const cst u :
    wf_named Σ Δ -> wf_local Σ Δ Γ ->
    forall decl (isdecl : declared_constant Σ.1 cst decl),
    consistent_instance_ext Σ decl.(cst_universes) u ->
    Σ ;;; Δ ;;; Γ |- (tConst cst u) : subst_instance u decl.(cst_type)

| type_Ind ind u :
    wf_named Σ Δ -> wf_local Σ Δ Γ ->
    forall mdecl idecl (isdecl : declared_inductive Σ.1 ind mdecl idecl),
    consistent_instance_ext Σ mdecl.(ind_universes) u ->
    Σ ;;; Δ ;;; Γ |- (tInd ind u) : subst_instance u idecl.(ind_type)

| type_Construct ind i u :
    wf_named Σ Δ -> wf_local Σ Δ Γ ->
    forall mdecl idecl cdecl (isdecl : declared_constructor Σ.1 (ind, i) mdecl idecl cdecl),
    consistent_instance_ext Σ mdecl.(ind_universes) u ->
    Σ ;;; Δ ;;; Γ |- (tConstruct ind i u) : type_of_constructor mdecl cdecl (ind, i) u

| type_Case (ci : case_info) p c brs indices ps :
    forall mdecl idecl (isdecl : declared_inductive Σ.1 ci.(ci_ind) mdecl idecl),
    mdecl.(ind_npars) = ci.(ci_npar) ->
    wf_nactx p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
    context_assumptions mdecl.(ind_params) = #|p.(pparams)| ->
    consistent_instance_ext Σ (ind_universes mdecl) p.(puinst) ->
    let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
    ctx_inst (typing Σ Δ) Γ (p.(pparams) ++ indices)
      (List.rev (ind_params mdecl ,,, ind_indices idecl : context)@[p.(puinst)]) ->
    Σ ;;; Δ ;;; Γ ,,, predctx |- p.(preturn) : tSort ps ->
    is_allowed_elimination Σ idecl.(ind_kelim) ps ->
    Σ ;;; Δ ;;; Γ |- c : mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices) ->
    isCoFinite mdecl.(ind_finite) = false ->
    let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
    All2i (fun i cdecl br =>
      let brctxty := case_branch_type ci.(ci_ind) mdecl p ptm i cdecl br in
      (wf_nactx br.(bcontext) (cstr_branch_context ci.(ci_ind) mdecl cdecl)) *
      (Σ ;;; Δ ;;; Γ ,,, brctxty.1 |- br.(bbody) : brctxty.2) *
      (Σ ;;; Δ ;;; Γ ,,, brctxty.1 |- brctxty.2 : tSort ps))
      0 idecl.(ind_ctors) brs ->
    Σ ;;; Δ ;;; Γ |- tCase ci p c brs : mkApps ptm (indices ++ [c])

| type_Proj p c u :
    forall mdecl idecl cdecl pdecl (isdecl : declared_projection Σ.1 p mdecl idecl cdecl pdecl) args,
    Σ ;;; Δ ;;; Γ |- c : mkApps (tInd p.(proj_ind) u) args ->
    #|args| = ind_npars mdecl ->
    Σ ;;; Δ ;;; Γ |- tProj p c : subst0 (c :: List.rev args) (subst_instance u pdecl.(proj_type))

| type_Fix mfix n decl :
    fix_guard Σ Δ Γ mfix ->
    nth_error mfix n = Some decl ->
    wf_named Σ Δ -> wf_local Σ Δ Γ ->
    All (on_def_type (lift_typing1 (typing Σ Δ)) Γ) mfix ->
    All (on_def_body (lift_typing1 (typing Σ Δ)) (fix_context mfix) Γ) mfix ->
    wf_fixpoint Σ mfix ->
      Σ ;;; Δ ;;; Γ |- tFix mfix n : decl.(dtype)

| type_CoFix mfix n decl :
    cofix_guard Σ Δ Γ mfix ->
    nth_error mfix n = Some decl ->
    wf_named Σ Δ -> wf_local Σ Δ Γ ->
    All (on_def_type (lift_typing1 (typing Σ Δ)) Γ) mfix ->
    All (on_def_body (lift_typing1 (typing Σ Δ)) (fix_context mfix) Γ) mfix ->
    wf_cofixpoint Σ mfix ->
    Σ ;;; Δ ;;; Γ |- tCoFix mfix n : decl.(dtype)

| type_Int p prim_ty cdecl :
    wf_named Σ Δ -> wf_local Σ Δ Γ ->
    primitive_constant Σ primInt = Some prim_ty ->
    declared_constant Σ prim_ty cdecl ->
    primitive_invariants primInt cdecl ->
    Σ ;;; Δ ;;; Γ |- tInt p : tConst prim_ty []

| type_Float p prim_ty cdecl :
    wf_named Σ Δ -> wf_local Σ Δ Γ ->
    primitive_constant Σ primFloat = Some prim_ty ->
    declared_constant Σ prim_ty cdecl ->
    primitive_invariants primFloat cdecl ->
    Σ ;;; Δ ;;; Γ |- tFloat p : tConst prim_ty []

| type_String p prim_ty cdecl :
    wf_named Σ Δ -> wf_local Σ Δ Γ ->
    primitive_constant Σ primString = Some prim_ty ->
    declared_constant Σ prim_ty cdecl ->
    primitive_invariants primString cdecl ->
    Σ ;;; Δ ;;; Γ |- tString p : tConst prim_ty []

| type_Array prim_ty cdecl u arr def ty :
    wf_named Σ Δ -> wf_local Σ Δ Γ ->
    primitive_constant Σ primArray = Some prim_ty ->
    declared_constant Σ prim_ty cdecl ->
    primitive_invariants primArray cdecl ->
    let s := sType (Universe.make' u) in
    Σ ;;; Δ ;;; Γ |- ty : tSort s ->
    Σ ;;; Δ ;;; Γ |- def : ty ->
    All (fun t => Σ ;;; Δ ;;; Γ |- t : ty) arr ->
    Σ ;;; Δ ;;; Γ |- tArray u arr def ty : tApp (tConst prim_ty [u]) [ty]

| type_Conv t A B s :
    Σ ;;; Δ ;;; Γ |- t : A ->
    Σ ;;; Δ ;;; Γ |- B : tSort s ->
    Σ ;;; Δ ;;; Γ |- A <= B -> 
    Σ ;;; Δ ;;; Γ |- t : B

where " Σ ;;; Δ ;;; Γ |- t : T " := (typing Σ Δ Γ t T) : type_scope
  and "'wf_named' Σ Δ " := (All_named_env (lift_typing2 (typing Σ)) Δ) : type_scope
  and "'wf_local' Σ Δ Γ " := (All_local_env (lift_typing1 (typing Σ Δ)) Γ) : type_scope

(* Typing of "spines", currently just the arguments of applications *)

with typing_spine `{checker_flags} (Σ : global_env_ext) (Δ : named_context) (Γ : context) : term -> list term -> term -> Type :=
| type_spine_nil ty : typing_spine Σ Δ Γ ty [] ty
| type_spine_cons hd tl na A B s T B' :
    Σ ;;; Δ ;;; Γ |- tProd na A B : tSort s ->
    Σ ;;; Δ ;;; Γ |- T <= tProd na A B ->
    Σ ;;; Δ ;;; Γ |- hd : A ->
    typing_spine Σ Δ Γ (subst10 hd B) tl B' ->
    typing_spine Σ Δ Γ T (cons hd tl) B'.

Derive Signature for typing typing_spine.

(** ** Typechecking of global environments *)

Definition has_nparams npars ty :=
  decompose_prod_n_assum [] npars ty <> None.

Definition unlift_opt_pred (P : global_env_ext -> context -> option term -> term -> Type) :
  (global_env_ext -> context -> term -> term -> Type) :=
  fun Σ Γ t T => P Σ Γ (Some t) T.

Module TemplateTyping <: Typing TemplateTerm Env TemplateTermUtils TemplateEnvTyping
  TemplateConversion TemplateConversionPar.

  Definition typing := @typing.

End TemplateTyping.

Module TemplateDeclarationTyping :=
  DeclarationTyping
    TemplateTerm
    Env
    TemplateTermUtils
    TemplateEnvTyping
    TemplateConversion
    TemplateConversionPar
    TemplateTyping
    TemplateLookup
    TemplateGlobalMaps.
Include TemplateDeclarationTyping.


Section Typing_Spine_size.
  Context `{checker_flags}.
  Context (fn : forall (Σ : global_env_ext) (Δ : named_context) (Γ : context) (t T : term), typing Σ Δ Γ t T -> size).
  Context (Σ : global_env_ext) (Δ : named_context) (Γ : context).

  Fixpoint typing_spine_size t T U (s : typing_spine Σ Δ Γ t T U) : size :=
  match s with
  | type_spine_nil _ => 0
  | type_spine_cons hd tl na A B s T B' typrod cumul ty s' =>
    (fn _ _ _ _ _ ty + fn _ _ _ _ _ typrod + typing_spine_size _ _ _ s')%nat
  end.
End Typing_Spine_size.

Section CtxInstSize.
  Context (typing : global_env_ext -> named_context -> context -> term -> term -> Type)
  (typing_size : forall {Σ Δ Γ t T}, typing Σ Δ Γ t T -> size).

  Fixpoint ctx_inst_size {Σ Δ Γ args Γ0} (c : ctx_inst (typing Σ Δ) Γ args Γ0) : size :=
  match c with
  | ctx_inst_nil => 0
  | ctx_inst_ass na t i inst Γ0 ty ctxi => ((typing_size _ _ _ _ _ ty) + (ctx_inst_size ctxi))%nat
  | ctx_inst_def na b t inst Γ0 ctxi => S (ctx_inst_size ctxi)
  end.

End CtxInstSize.

Definition typing_size `{checker_flags} {Σ Δ Γ t T} (d : Σ ;;; Δ ;;; Γ |- t : T) : size.
Proof.
  revert Σ Δ Γ t T d.
  fix typing_size 6.
  pose (wf_size Σ Δ Γ (w : wf_named Σ Δ) (w' : wf_local Σ Δ Γ) := 
    Nat.max (All_named_env_size (typing_size Σ) Δ w)
            (All_local_env_size (typing_size Σ Δ) Γ w')).
  destruct 1;
    repeat match goal with
           | H : typing _ _ _ _ _ |- _ => apply typing_size in H
           end.
  - exact (S (wf_size Σ Δ Γ a a0)).
  - exact (S (wf_size Σ Δ Γ a a0)).
  - exact (S (wf_size Σ Δ Γ a a0)). 
  - exact (S (Nat.max d1 d2)).
  - exact (S (Nat.max d (lift_typing_size (typing_size _ _ _) _ l))).
  - exact (S (Nat.max d (lift_typing_size (typing_size _ _ _) _ l))).
  - exact (S (Nat.max d (lift_typing_size (typing_size _ _ _) _ l))).
  - exact (S (Nat.max d (typing_spine_size typing_size _ _ _ _ _ _ t0))).
  - exact (S (S (wf_size Σ Δ Γ a a0))).
  - exact (S (S (wf_size Σ Δ Γ a a0))).
  - exact (S (S (wf_size Σ Δ Γ a a0))).
  - exact (S (Nat.max d1 (Nat.max d2
    (Nat.max (ctx_inst_size _ typing_size c1)
      (all2i_size _ (fun _ x y p => Nat.max (typing_size _ _ _ _ _ p.1.2) (typing_size _ _ _ _ _ p.2)) a0))))).
  - exact (S d). 
  - exact (S (Nat.max
      (Nat.max (wf_size Σ Δ Γ a a0) (all_size _ (fun x p => on_def_type_size (typing_size Σ _) _ _ p) a1))
      (all_size (on_def_body (lift_typing1 (typing Σ Δ)) _ _) (fun x p => on_def_body_size (typing_size Σ Δ) _ _ _ p) a2))).
  - exact (S (Nat.max
      (Nat.max (wf_size Σ Δ Γ a a0) (all_size _ (fun x p => on_def_type_size (typing_size Σ _) _ _ p) a1))
      (all_size (on_def_body (lift_typing1 (typing Σ Δ)) _ _) (fun x p => on_def_body_size (typing_size Σ Δ) _ _ _ p) a2))).
  - exact (S (wf_size Σ Δ Γ a a0)).
  - exact (S (wf_size Σ Δ Γ a a0)).
  - exact (S (wf_size Σ Δ Γ a a0)).
  - exact (S (Nat.max (wf_size Σ Δ Γ a a0) (Nat.max d2 (Nat.max d3 (all_size _ (fun t p => typing_size Σ Δ Γ t ty p) a1))))).
  - exact (S (Nat.max d1 d2)).  
Defined.

Lemma typing_size_pos `{checker_flags} {Σ Δ Γ t T} (d : Σ ;;; Δ ;;; Γ |- t : T) : typing_size d > 0.
Proof.
  induction d; simpl; try lia.
Qed.

Fixpoint globdecls_size (Σ : global_declarations) : size :=
  match Σ with
  | [] => 1
  | d :: Σ => S (globdecls_size Σ)
  end.

Definition globenv_size (Σ : global_env) : size :=
  globdecls_size Σ.(declarations).


(** To get a good induction principle for typing derivations,
     we need:
    - size of the global_env_ext, including size of the global declarations in it
    - size of the derivation. *)

Arguments lexprod [A B].

Definition wf `{checker_flags} Σ := on_global_env cumul_gen (lift_typing3 typing) Σ.
Definition wf_ext `{checker_flags} := on_global_env_ext cumul_gen (lift_typing3 typing).

Lemma typing_wf_local `{cf : checker_flags} {Σ} {Δ Γ t T} :
  Σ ;;; Δ ;;; Γ |- t : T -> wf_local Σ Δ Γ.
Proof.
  revert Σ Δ Γ t T.
  fix f 6.
  destruct 1; eauto.
  all: exact (f _ _ _ _ _ l.2.π2.1).
Defined.
#[global] Hint Resolve typing_wf_local : wf.

Lemma typing_wf_named `{cf : checker_flags} {Σ} {Δ Γ t T} :
  Σ ;;; Δ ;;; Γ |- t : T -> wf_named Σ Δ.
Proof.
  revert Σ Δ Γ t T.
  fix f 6.
  destruct 1; eauto.
  all: exact (f _ _ _ _ _ l.2.π2.1).
Defined.
#[global] Hint Resolve typing_wf_named : wf.

Lemma type_Prop `{checker_flags} Σ :
  Σ ;;; [] ;;; [] |- tSort sProp : tSort Sort.type1.
  change (  Σ ;;; [] ;;; [] |- tSort (sProp) : tSort Sort.type1);
  constructor ; auto ; constructor.
Defined.

Lemma typing_size_Prop `{checker_flags} Σ :
  typing_size (type_Prop Σ) = 1.
Proof.
  simpl. unfold All_local_env_size. simpl. reflexivity.
Qed.

Lemma type_Prop_wf `{checker_flags} Σ Δ Γ :
  wf_named Σ Δ ->
  wf_local Σ Δ Γ ->
  Σ ;;; Δ ;;; Γ |- tSort sProp : tSort Sort.type1.
Proof.
  constructor ; auto ; constructor.
Defined.

Definition env_prop `{checker_flags} (P : forall Σ Δ Γ t T, Type) (Pj : forall Σ Δ Γ j, Type) 
  (PΔ : forall Σ Δ (wfΔ : wf_named Σ Δ), Type)  (PΓ : forall Σ Δ (wfΔ : wf_named Σ Δ) Γ (wfΓ : wf_local Σ Δ Γ), Type) :=
  forall (Σ : global_env_ext) (wfΣ : wf Σ) Δ Γ t T (ty : Σ ;;; Δ ;;; Γ |- t : T),
    on_global_env cumul_gen Pj Σ * (PΔ Σ Δ (typing_wf_named ty) * PΓ Σ Δ (typing_wf_named ty) Γ (typing_wf_local ty) * P Σ Δ Γ t T).

Lemma env_prop_typing `{checker_flags} {P Pj PΔ PΓ} : env_prop P Pj PΔ PΓ ->
  forall (Σ : global_env_ext) (wfΣ : wf Σ) (Δ : named_context) (Γ : context) (t T : term),
    Σ ;;; Δ ;;; Γ |- t : T -> P Σ Δ Γ t T.
Proof. intros. now apply X. Qed.

Lemma env_prop_wf_local `{checker_flags} {P Pj PΔ PΓ} : env_prop P Pj PΔ PΓ ->
  forall (Σ : global_env_ext) (wfΣ : wf Σ) (Δ : named_context) (wfΔ : wf_named Σ Δ) 
    (Γ : context) (wfΓ : wf_local Σ Δ Γ), PΓ Σ Δ wfΔ Γ wfΓ.
Proof. intros. red in X. now apply (X Σ wfΣ Δ Γ _ _ (type_Prop_wf Σ Δ Γ _ _)). Qed.

Lemma env_prop_sigma `{checker_flags} {P Pj PΔ PΓ} : env_prop P Pj PΔ PΓ ->
  forall Σ (wfΣ : wf Σ), on_global_env cumul_gen Pj Σ.
Proof.
  intros. eapply (X (empty_ext Σ)).
  - apply wfΣ.
  - apply type_Prop.
Defined.

Lemma wf_local_app_l `{checker_flags} Σ Δ (Γ Γ' : context) : wf_local Σ Δ (Γ ,,, Γ') -> wf_local Σ Δ Γ.
Proof.
  induction Γ'.
  - auto.
  - simpl. intros H'. apply IHΓ'. now inv H'.
Defined.
#[global] Hint Immediate wf_local_app_l : wf.

Lemma wf_named_app_l `{checker_flags} Σ Δ Δ' : wf_named Σ (Δ ,,, Δ') -> wf_named Σ Δ.
Proof.
  induction Δ'.
  - auto.
  - simpl. intros H'. apply IHΔ'. now inv H'.
Defined.
#[global] Hint Immediate wf_named_app_l : wf.  

Lemma typing_wf_local_size `{cf : checker_flags} {Σ} {Δ Γ t T}
      (d : Σ ;;; Δ ;;; Γ |- t : T) :
  All_local_env_size (@typing_size cf Σ Δ) Γ (typing_wf_local d) < typing_size d.
Proof.
  revert Σ Δ Γ t T d. fix f 6.
  induction d; simpl;
  change (fun Γ t T (Hty : Σ ;;; Δ ;;; Γ |- t : T) => typing_size Hty) with (@typing_size cf Σ); try lia.
  1-3: pose proof (f _ _ _ _ _ l.2.π2.1); unfold lift_sorting_size; cbn in *; try lia.
Qed.

Lemma typing_wf_named_size `{cf : checker_flags} {Σ} {Δ Γ t T}
      (d : Σ ;;; Δ ;;; Γ |- t : T) :
  All_named_env_size (@typing_size cf Σ) Δ (typing_wf_named d) < typing_size d.
Proof.
  revert Σ Δ Γ t T d. fix f 6.
  induction d; simpl;
  change (fun Γ t T (Hty : Σ ;;; Δ ;;; Γ |- t : T) => typing_size Hty) with (@typing_size cf Σ); try lia.
Qed.

Lemma wf_local_inv `{checker_flags} {Σ Δ Γ'} (w : wf_local Σ Δ Γ') :
  forall d Γ,
    Γ' = d :: Γ ->
    ∑ (w' : wf_local Σ Δ Γ) u,
      { ty : lift_typing1 (typing Σ Δ) Γ (Judge d.(decl_body) d.(decl_type) (Some u)) |
            All_local_env_size (@typing_size _ Σ Δ) _ w' <
            All_local_env_size (@typing_size _ Σ Δ) _ w /\
            lift_typing_size (@typing_size _ Σ Δ Γ) _ ty <= All_local_env_size (@typing_size _ _ _) _ w }.
Proof.
  intros d Γ ->.
  depelim w; cbn.
  all: exists w, l.2.π1, (lift_sorting_extract l).
  all: pose proof (typing_size_pos l.2.π2.1).
  2: pose proof (typing_size_pos l.1).
  all: simpl in *.
  all: simpl; split.
  all: try lia.
Qed.

Lemma wf_named_inv `{checker_flags} {Σ Δ' id} (w : wf_named Σ Δ') :
  forall d Δ,
    Δ' = (id, d) :: Δ ->
    ∑ (w' : wf_named Σ Δ) u,
      { ty : lift_typing0 (typing Σ Δ []) (Judge d.(decl_body) d.(decl_type) (Some u)) |
            All_named_env_size (@typing_size _ Σ) _ w' <
            All_named_env_size (@typing_size _ Σ) _ w /\
            lift_typing_size (@typing_size _ Σ Δ []) _ ty <= All_named_env_size (@typing_size _ _) _ w }.
Proof.
  intros d Δ ->.
  depelim w; cbn.
  all: exists w, l.2.π1, (lift_sorting_extract l).
  all: pose proof (typing_size_pos l.2.π2.1).
  2: pose proof (typing_size_pos l.1).
  all: simpl in *.
  all: simpl; split.
  all: try lia.
Qed.

(*Lemma typing_nctx_inv Σ Δ Γ id na ta t T :
  Σ ;;; Δ ,, (id, vass na ta) ;;; Γ |- t : T ->
  Σ ;;; Δ *)

(** *** An induction principle ensuring the Σ declarations enjoy the same properties.
    Also theads the well-formedness of the local context and the induction principle for it,
    and gives the right induction hypothesis
    on typing judgments in application spines, fix and cofix blocks.
 *)

Inductive Forall_typing_spine `{checker_flags} Σ Δ Γ (P : term -> term -> Type) :
  forall (T : term) (t : list term) (U : term), typing_spine Σ Δ Γ T t U -> Type :=
| Forall_type_spine_nil T : Forall_typing_spine Σ Δ Γ P T [] T (type_spine_nil Σ Δ Γ T)
| Forall_type_spine_cons hd tl na A B s T B' tls
   (typrod : Σ ;;; Δ ;;; Γ |- tProd na A B : tSort s)
   (cumul : Σ ;;; Δ ;;; Γ |- T <= tProd na A B) (ty : Σ ;;; Δ ;;; Γ |- hd : A) :
    P (tProd na A B) (tSort s) -> P hd A -> Forall_typing_spine Σ Δ Γ P (B {0 := hd}) tl B' tls ->
    Forall_typing_spine Σ Δ Γ P T (hd :: tl) B'
      (type_spine_cons Σ Δ Γ hd tl na A B s T B' typrod cumul ty tls).

Implicit Types (Σ : global_env_ext).

Lemma typing_ind_env `{cf : checker_flags} :
  forall (P : global_env_ext -> named_context -> context -> term -> term -> Type)
         (Pj : global_env_ext -> named_context -> context -> judgment -> Type)
         (Pdecl := fun Σ Δ (wfΔ : wf_named Σ Δ) Γ (wfΓ : wf_local Σ Δ Γ) t T tyT => P Σ Δ Γ t T)
         (PΔ : forall Σ Δ (_ : wf_named Σ Δ), Type)
         (PΓ : forall Σ Δ (_ : wf_named Σ Δ) Γ (_ : wf_local Σ Δ Γ), Type),

    (forall Σ (wfΣ : wf Σ) (Δ : named_context) (* (wfΔ : wf_named Σ Δ) *) (Γ : context) (* (wfΓ : wf_local Σ Δ Γ) *) j,
      lift_typing_conj1 (typing Σ Δ) (P Σ Δ) Γ j -> Pj Σ Δ Γ j) ->

    (forall Σ (wfΣ : wf Σ) (Δ : named_context) (wfΔ : wf_named Σ Δ),
      All_named_env_over (typing Σ) (fun Δ Γ wfΔ t T tyT => P Σ Δ Γ t T) Δ wfΔ -> 
      All_named_env (Pj Σ) Δ ->
      PΔ Σ Δ wfΔ) ->

    (forall Σ (wfΣ : wf Σ) (Δ : named_context) (wfΔ : wf_named Σ Δ) (Γ : context) (wfΓ : wf_local Σ Δ Γ),
      All_named_env_over (typing Σ) (fun Δ Γ wfΔ t T tyT => P Σ Δ Γ t T) Δ wfΔ -> All_named_env (Pj Σ) Δ ->
      All_local_env_over (typing Σ Δ) (Pdecl Σ Δ wfΔ) Γ wfΓ -> All_local_env (Pj Σ Δ) Γ -> PΓ Σ Δ wfΔ Γ wfΓ) ->

    (forall Σ (wfΣ : wf Σ) (Δ : named_context) (wfΔ : wf_named Σ Δ) (Γ : context) (wfΓ : wf_local Σ Δ Γ) (n : nat) decl,
      nth_error Γ n = Some decl ->
      PΔ Σ Δ wfΔ ->
      PΓ Σ Δ wfΔ Γ wfΓ ->
      P Σ Δ Γ (tRel n) (lift0 (S n) decl.(decl_type))) ->

    (forall Σ (wfΣ : wf Σ) (Δ : named_context) (wfΔ : wf_named Σ Δ) (Γ : context) (wfΓ : wf_local Σ Δ Γ) (id : ident) decl,
      nctx_lookup Δ id = Some decl ->
      PΔ Σ Δ wfΔ ->
      PΓ Σ Δ wfΔ Γ wfΓ ->
      P Σ Δ Γ (tVar id) decl.(decl_type)) ->

    (forall Σ (wfΣ : wf Σ) (Δ : named_context) (wfΔ : wf_named Σ Δ) (Γ : context) (wfΓ : wf_local Σ Δ Γ) (u : sort),
      PΔ Σ Δ wfΔ ->
      PΓ Σ Δ wfΔ Γ wfΓ ->
      wf_sort Σ u ->
      P Σ Δ Γ (tSort u) (tSort (Sort.super u))) ->

    (forall Σ (wfΣ : wf Σ) (Δ : named_context) (wfΔ : wf_named Σ Δ) (Γ : context) (wfΓ : wf_local Σ Δ Γ) 
            (c : term) (k : cast_kind) (t : term) (s : sort),
        Σ ;;; Δ ;;; Γ |- t : tSort s -> P Σ Δ Γ t (tSort s) -> 
        Σ ;;; Δ ;;; Γ |- c : t -> P Σ Δ Γ c t -> 
        P Σ Δ Γ (tCast c k t) t) ->

    (forall Σ (wfΣ : wf Σ) (Δ : named_context) (wfΔ : wf_named Σ Δ) (Γ : context) (wfΓ : wf_local Σ Δ Γ) (na : aname) 
            (t b : term) (s1 s2 : sort),
        PΔ Σ Δ wfΔ ->
        PΓ Σ Δ wfΔ Γ wfΓ ->
        lift_typing3 typing Σ Δ Γ (j_vass_s na t s1) ->
        Pj Σ Δ Γ (j_vass_s na t s1) ->
        Σ ;;; Δ ;;; Γ ,, vass na t |- b : tSort s2 ->
        P Σ Δ (Γ ,, vass na t) b (tSort s2) -> P Σ Δ Γ (tProd na t b) (tSort (Sort.sort_of_product s1 s2))) ->

    (forall Σ (wfΣ : wf Σ)(Δ : named_context) (wfΔ : wf_named Σ Δ) (Γ : context) (wfΓ : wf_local Σ Δ Γ) 
            (na : aname) (t b : term) (bty : term),
        PΔ Σ Δ wfΔ ->
        PΓ Σ Δ wfΔ Γ wfΓ ->
        lift_typing3 typing Σ Δ Γ (j_vass na t) ->
        Pj Σ Δ Γ (j_vass na t) ->
        Σ ;;; Δ ;;; Γ ,, vass na t |- b : bty -> P Σ Δ (Γ ,, vass na t) b bty -> P Σ Δ Γ (tLambda na t b) (tProd na t bty)) ->

    (forall Σ (wfΣ : wf Σ) (Δ : named_context) (wfΔ : wf_named Σ Δ) (Γ : context) (wfΓ : wf_local Σ Δ Γ) 
            (na : aname) (b b_ty b' b'_ty : term),
        PΔ Σ Δ wfΔ ->
        PΓ Σ Δ wfΔ Γ wfΓ ->
        lift_typing3 typing Σ Δ Γ (j_vdef na b b_ty) ->
        Pj Σ Δ Γ (j_vdef na b b_ty) ->
        Σ ;;; Δ ;;; Γ ,, vdef na b b_ty |- b' : b'_ty ->
        P Σ Δ (Γ ,, vdef na b b_ty) b' b'_ty -> P Σ Δ Γ (tLetIn na b b_ty b') (tLetIn na b b_ty b'_ty)) ->

    (forall Σ (wfΣ : wf Σ) (Δ : named_context) (wfΔ : wf_named Σ Δ) (Γ : context) (wfΓ : wf_local Σ Δ Γ) 
            (t : term) (l : list term) (t_ty t' : term),
        Σ ;;; Δ ;;; Γ |- t : t_ty -> P Σ Δ Γ t t_ty ->
        isApp t = false -> l <> [] ->
        forall (s : typing_spine Σ Δ Γ t_ty l t'),
        Forall_typing_spine Σ Δ Γ (fun t T => P Σ Δ Γ t T) t_ty l t' s ->
        P Σ Δ Γ (tApp t l) t') ->

    (forall Σ (wfΣ : wf Σ) (Δ : named_context) (wfΔ : wf_named Σ Δ) (Γ : context) (wfΓ : wf_local Σ Δ Γ) 
            cst u (decl : constant_body),
        on_global_env cumul_gen Pj Σ.1 ->
        PΔ Σ Δ wfΔ ->
        PΓ Σ Δ wfΔ Γ wfΓ ->
        declared_constant Σ.1 cst decl ->
        consistent_instance_ext Σ decl.(cst_universes) u ->
        P Σ Δ Γ (tConst cst u) (subst_instance u (cst_type decl))) ->

    (forall Σ (wfΣ : wf Σ) (Δ : named_context) (wfΔ : wf_named Σ Δ) (Γ : context) (wfΓ : wf_local Σ Δ Γ) (ind : inductive) u
          mdecl idecl (isdecl : declared_inductive Σ.1 ind mdecl idecl),
        on_global_env cumul_gen Pj Σ.1 ->
        PΔ Σ Δ wfΔ ->
        PΓ Σ Δ wfΔ Γ wfΓ ->
        consistent_instance_ext Σ mdecl.(ind_universes) u ->
        P Σ Δ Γ (tInd ind u) (subst_instance u (ind_type idecl))) ->

    (forall Σ (wfΣ : wf Σ) (Δ : named_context) (wfΔ : wf_named Σ Δ) (Γ : context) (wfΓ : wf_local Σ Δ Γ) (ind : inductive) (i : nat) u
            mdecl idecl cdecl (isdecl : declared_constructor Σ.1 (ind, i) mdecl idecl cdecl),
        on_global_env cumul_gen Pj Σ.1 ->
        PΔ Σ Δ wfΔ ->
        PΓ Σ Δ wfΔ Γ wfΓ ->
        consistent_instance_ext Σ mdecl.(ind_universes) u ->
        P Σ Δ Γ (tConstruct ind i u) (type_of_constructor mdecl cdecl (ind, i) u)) ->

     (forall (Σ : global_env_ext) (wfΣ : wf Σ) (Δ : named_context) (wfΔ : wf_named Σ Δ) (Γ : context) (wfΓ : wf_local Σ Δ Γ),
      forall (ci : case_info) p c brs indices ps mdecl idecl
        (isdecl : declared_inductive Σ.1 ci.(ci_ind) mdecl idecl),
        on_global_env cumul_gen Pj Σ.1 ->
        PΔ Σ Δ wfΔ ->
        PΓ Σ Δ wfΔ Γ wfΓ ->
        mdecl.(ind_npars) = ci.(ci_npar) ->
        wf_nactx p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
        context_assumptions mdecl.(ind_params) = #|p.(pparams)| ->
        consistent_instance_ext Σ (ind_universes mdecl) p.(puinst) ->
        let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
        ctx_inst ((Prop_conj typing P Σ) Δ) Γ (p.(pparams) ++ indices)
        (List.rev (ind_params mdecl ,,, ind_indices idecl : context)@[p.(puinst)]) ->
        forall pret : Σ ;;; Δ ;;; Γ ,,, predctx |- p.(preturn) : tSort ps,
        P Σ Δ (Γ ,,, predctx) p.(preturn) (tSort ps) ->
        PΓ Σ Δ (typing_wf_named pret) (Γ ,,, predctx) (typing_wf_local pret) ->
        is_allowed_elimination Σ idecl.(ind_kelim) ps ->
        Σ ;;; Δ ;;; Γ |- c : mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices) ->
        P Σ Δ Γ c (mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices)) ->
        isCoFinite mdecl.(ind_finite) = false ->
        let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
        All2i (fun i cdecl br =>
          let brctxty := case_branch_type ci.(ci_ind) mdecl p ptm i cdecl br in
          wf_nactx br.(bcontext) (cstr_branch_context ci.(ci_ind) mdecl cdecl) *
          Prop_conj typing P Σ Δ (Γ ,,, brctxty.1) br.(bbody) brctxty.2 *
          Prop_conj typing P Σ Δ (Γ ,,, brctxty.1) brctxty.2 (tSort ps))
          0 idecl.(ind_ctors) brs ->
        P Σ Δ Γ (tCase ci p c brs) (mkApps ptm (indices ++ [c]))) ->

    (forall Σ (wfΣ : wf Σ) (Δ : named_context) (wfΔ : wf_named Σ Δ) (Γ : context) (wfΓ : wf_local Σ Δ Γ) (p : projection) (c : term) u
          mdecl idecl cdecl pdecl (isdecl : declared_projection Σ.1 p mdecl idecl cdecl pdecl) args,
        on_global_env cumul_gen Pj Σ.1 ->
        PΔ Σ Δ wfΔ ->
        PΓ Σ Δ wfΔ Γ wfΓ ->
        Σ ;;; Δ ;;; Γ |- c : mkApps (tInd p.(proj_ind) u) args ->
        P Σ Δ Γ c (mkApps (tInd p.(proj_ind) u) args) ->
        #|args| = ind_npars mdecl ->
        P Σ Δ Γ (tProj p c) (subst0 (c :: List.rev args) (subst_instance u pdecl.(proj_type)))) ->

    (forall Σ (wfΣ : wf Σ) (Δ : named_context) (wfΔ : wf_named Σ Δ) (Γ : context) (wfΓ : wf_local Σ Δ Γ) 
            (mfix : list (def term)) (n : nat) decl,
        let types := fix_context mfix in
        fix_guard Σ Δ Γ mfix ->
        nth_error mfix n = Some decl ->
        PΔ Σ Δ wfΔ ->
        PΓ Σ Δ wfΔ Γ wfΓ ->
        All (on_def_type (lift_typing3 typing Σ Δ) Γ) mfix ->
        All (on_def_type (Pj Σ Δ) Γ) mfix ->
        All (on_def_body (lift_typing3 typing Σ Δ) types Γ) mfix ->
        All (on_def_body (Pj Σ Δ) types Γ) mfix ->
         wf_fixpoint Σ.1 mfix ->
        P Σ Δ Γ (tFix mfix n) decl.(dtype)) ->

    (forall Σ (wfΣ : wf Σ) (Δ : named_context) (wfΔ : wf_named Σ Δ) (Γ : context) (wfΓ : wf_local Σ Δ Γ) (mfix : list (def term)) (n : nat) decl,
        let types := fix_context mfix in
        cofix_guard Σ Δ Γ mfix ->
        nth_error mfix n = Some decl ->
        PΔ Σ Δ wfΔ ->
        PΓ Σ Δ wfΔ Γ wfΓ ->
        All (on_def_type (lift_typing3 typing Σ Δ) Γ) mfix ->
        All (on_def_type (Pj Σ Δ) Γ) mfix ->
        All (on_def_body (lift_typing3 typing Σ Δ) types Γ) mfix ->
        All (on_def_body (Pj Σ Δ) types Γ) mfix ->
         wf_cofixpoint Σ.1 mfix ->
        P Σ Δ Γ (tCoFix mfix n) decl.(dtype)) ->

    (forall Σ (wfΣ : wf Σ) (Δ : named_context) (wfΔ : wf_named Σ Δ) (Γ : context) (wfΓ : wf_local Σ Δ Γ) p prim_ty cdecl,
        PΔ Σ Δ wfΔ ->
        PΓ Σ Δ wfΔ Γ wfΓ ->
        primitive_constant Σ primInt = Some prim_ty ->
        declared_constant Σ prim_ty cdecl ->
        primitive_invariants primInt cdecl ->
        P Σ Δ Γ (tInt p) (tConst prim_ty [])) ->

    (forall Σ (wfΣ : wf Σ) (Δ : named_context) (wfΔ : wf_named Σ Δ) (Γ : context) (wfΓ : wf_local Σ Δ Γ) p prim_ty cdecl,
        PΔ Σ Δ wfΔ ->
        PΓ Σ Δ wfΔ Γ wfΓ ->
        primitive_constant Σ primFloat = Some prim_ty ->
        declared_constant Σ prim_ty cdecl ->
        primitive_invariants primFloat cdecl ->
        P Σ Δ Γ (tFloat p) (tConst prim_ty [])) ->

    (forall Σ (wfΣ : wf Σ) (Δ : named_context) (wfΔ : wf_named Σ Δ) (Γ : context) (wfΓ : wf_local Σ Δ Γ) p prim_ty cdecl,
        PΔ Σ Δ wfΔ ->
        PΓ Σ Δ wfΔ Γ wfΓ ->
        primitive_constant Σ primString = Some prim_ty ->
        declared_constant Σ prim_ty cdecl ->
        primitive_invariants primString cdecl ->
        P Σ Δ Γ (tString p) (tConst prim_ty [])) ->

    (forall Σ (wfΣ : wf Σ) (Δ : named_context) (wfΔ : wf_named Σ Δ) (Γ : context) (wfΓ : wf_local Σ Δ Γ) u arr def ty prim_ty cdecl,
        PΔ Σ Δ wfΔ ->
        PΓ Σ Δ wfΔ Γ wfΓ ->
        primitive_constant Σ primArray = Some prim_ty ->
        declared_constant Σ prim_ty cdecl ->
        primitive_invariants primArray cdecl ->
        let s := sType (Universe.make' u) in
        Σ ;;; Δ ;;; Γ |- ty : tSort s ->
        P Σ Δ Γ ty (tSort s) ->
        Σ ;;; Δ ;;; Γ |- def : ty ->
        P Σ Δ Γ def ty ->
        All (fun t => Σ ;;; Δ ;;; Γ |- t : ty × P Σ Δ Γ t ty) arr ->
        P Σ Δ Γ (tArray u arr def ty) (tApp (tConst prim_ty [u]) [ty])) ->

    (forall Σ (wfΣ : wf Σ) (Δ : named_context) (wfΔ : wf_named Σ Δ) (Γ : context) (wfΓ : wf_local Σ Δ Γ) (t A B : term) s,
        PΔ Σ Δ wfΔ ->
        PΓ Σ Δ wfΔ Γ wfΓ ->
        Σ ;;; Δ ;;; Γ |- t : A ->
        P Σ Δ Γ t A ->
        Σ ;;; Δ ;;; Γ |- B : tSort s ->
        P Σ Δ Γ B (tSort s) ->
        Σ ;;; Δ ;;; Γ |- A <= B ->
        P Σ Δ Γ t B) ->

       env_prop P Pj PΔ PΓ.
Proof.
  intros P Pj Pdecl PΔ PΓ. unfold env_prop.
  intros Xj XΔ XΓ Xrel Xvar Xsort Xcast Xprod Xlam Xlet Xapp Xconst Xind Xctor Xcase Xproj Xfix Xcofix Xint Xfloat Xstring Xarr Xconv.
  intros Σ wfΣ Δ Γ t T H.
  (* NOTE (Danil): while porting to 8.9, I had to split original "pose" into 2 pieces,
   otherwise it takes forever to execure the "pose", for some reason *)
  pose (@Fix_F ({ Σ : global_env_ext & { wfΣ : wf Σ & { Δ & { Γ & { t & { T & Σ ;;; Δ ;;; Γ |- t : T }}}}}})) as p0.
  specialize (p0 (lexprod (precompose lt (fun Σ => globenv_size (fst Σ)))
        (fun Σ => precompose lt (fun x => typing_size x.π2.π2.π2.π2.π2)))) as p.
  set (foo := (Σ; wfΣ; Δ; Γ; (t; T; H)) : { Σ : global_env_ext & { wfΣ : wf Σ & { Δ & { Γ & { t & { T & Σ ;;; Δ ;;; Γ |- t : T }}}}}}).
  change Σ with foo.π1.
  change Δ with foo.π2.π2.π1.
  change Γ with foo.π2.π2.π2.π1.
  change t with foo.π2.π2.π2.π2.π1.
  change T with foo.π2.π2.π2.π2.π2.π1.
  change H with foo.π2.π2.π2.π2.π2.π2.
  revert foo.
  match goal with
    |- let foo := _ in @?P foo => specialize (p (fun x => P x))
  end.
  forward p; [ | apply p; apply wf_lexprod; intros; apply wf_precompose; apply lt_wf].
  clear p. clear Σ wfΣ Δ Γ t T H.
  intros (Σ & wfΣ & Δ & Γ & t & t0 & H). simpl.
  intros IH. simpl in IH.
  split.
  destruct Σ as [Σ φ].
  red. cbn. do 2 red in wfΣ. cbn in wfΣ.
  destruct Σ as [univs Σ]; cbn in *.
  set (Σg:= {| universes := univs; declarations := Σ |}) in *.
  destruct wfΣ; split => //.
  rename o into ongu. rename o0 into o.
  destruct o. { constructor. }
  rename o0 into Xg. set (wfΣ := (ongu, o) : on_global_env cumul_gen (lift_typing3 typing) {| universes := univs; declarations := Σ |}).
  set (Σ':= {| universes := univs; declarations := Σ |}) in *.
  destruct Xg. rename udecl0 into udecl.
  rename on_global_decl_d0 into Xg.
  constructor; auto; try constructor; auto.
  - unshelve eset (IH' := IH ((Σ', udecl); wfΣ; []; ([]; tSort sProp; _; _))).
    shelve. simpl. apply type_Prop.
    forward IH'. constructor 1; cbn. lia.
    apply IH'; auto.
  - simpl. simpl in *.
    destruct d.
    + apply Xj; tas.
      apply lift_typing_impl with (1 := Xg); intros ?? Hs. split; tas.
      specialize (IH ((Σ', udecl); wfΣ; _; _; (_; _; Hs))).
      forward IH; [constructor 1; simpl; subst Σ' Σg; cbn; lia|].
      apply IH.
    + red in Xg.
      destruct Xg as [onI onP onNP onV]; constructor; eauto.
      * unshelve eset (IH' := fun p => IH ((Σ', udecl); wfΣ; p) _).
        constructor. cbn; subst Σ' Σg; lia. clearbody IH'. cbn in IH'.
        clear IH; rename IH' into IH.
        eapply Alli_impl; eauto. cbn in IH. clear onI onP onNP onV. intros n x Xg.
        refine {| ind_arity_eq := Xg.(ind_arity_eq);
                  ind_cunivs := Xg.(ind_cunivs) |}.
        -- apply onArity in Xg.
           apply Xj; tas.
           apply lift_typing_impl with (1 := Xg); intros ?? Hs. split; tas.
           apply (IH (_; _; _; _; Hs)).
        -- pose proof Xg.(onConstructors) as Xg'.
           eapply All2_impl; eauto.
           intros ? ? [cass tyeq onctyp oncargs oncind]; unshelve econstructor; eauto.
           { apply Xj; tas.
             apply lift_typing_impl with (1 := onctyp); intros ?? Hs. split; tas.
             apply (IH (_; _; _; _; Hs)). }
           { apply sorts_local_ctx_impl with (1 := oncargs); intros Γ' j' Hj'.
             apply Xj; tas.
             apply lift_typing_impl with (1 := Hj'); intros ?? Hs. split; tas.
             apply (IH (_; _; _; _; Hs)). }
           { eapply ctx_inst_impl with (1 := oncind); intros ?? Hj.
             apply Xj; tas.
             apply lift_typing_impl with (1 := Hj); intros ?? Hs. split; tas.
             apply (IH (_; _; _; _; Hs)). }
        -- pose proof (onProjections Xg); auto.
        -- pose proof (ind_sorts Xg) as Xg'. unfold check_ind_sorts in *.
           destruct Sort.to_family; auto.
           split. apply Xg'. destruct indices_matter; auto.
           eapply type_local_ctx_impl. eapply Xg'. auto. intros ?? Hj. apply Xj; tas.
           apply lift_typing_impl with (1 := Hj); intros ?? Hs. split; tas.
           apply (IH (_; _; _; _; Hs)).
        -- apply (onIndices Xg).
      * apply All_local_env_impl with (1 := onP); intros ?? Hj. apply Xj; tas.
        apply lift_typing_impl with (1 := Hj); intros ?? Hs. split; tas.
        apply (IH ((Σ', udecl); (wfΣ; _; _; _; _; Hs))).
        constructor 1. simpl. subst Σ' Σg; cbn; lia.

  - assert (forall Δ Γ t T (Hty : Σ ;;; Δ ;;; Γ |- t : T),
               typing_size Hty < typing_size H ->
               on_global_env cumul_gen Pj Σ.1 * P Σ Δ Γ t T) as X1.
    { intros.
      specialize (IH (Σ; wfΣ; _; _; (_; _; Hty))).
      simpl in IH.
      forward IH.
      constructor 2. simpl. apply H0.
      intuition. }

    assert (Xj' : forall Δ Γ j (Hj : lift_typing3 typing Σ Δ Γ j),
        lift_typing_size (fun t T H => @typing_size cf Σ Δ Γ t T H) _ Hj < typing_size H ->
        Pj Σ Δ Γ j).
    { intros ??? Hj Hlt.
      apply Xj; tas.
      eapply lift_typing_size_impl with (Psize := fun t T H => @typing_size _ _ _ _ t T H) (tu := Hj).
      intros ?? Hty Hlt'; split; tas.
      apply X1 with (Hty := Hty). set (size_mid := lift_typing_size _ _ Hj) in *. lia. }
    clear Xj; rename Xj' into Xj.

    assert (forall Γ' t T (Hty : Σ ;;; Δ ;;; Γ' |- t : T),
      typing_size Hty <= typing_size H ->
      PΔ Σ Δ (typing_wf_named Hty)) as X3.
    { intros. apply XΔ ; tea. admit. admit. }
    
    assert (forall Γ' t T (Hty : Σ ;;; Δ ;;; Γ' |- t : T),
      typing_size Hty <= typing_size H ->
      PΓ Σ Δ (typing_wf_named Hty) Γ' (typing_wf_local Hty)) as X2.
    { (*intros.
      clear - wfΣ X1 Xj XΓ.
      apply XΓ ; tas.
      - (*pose proof (typing_wf_named_size Hty) as H1.*)
        set (w := typing_wf_named Hty) in *. clearbody w.
        induction w ; [constructor|constructor|constructor].
        + apply IHw with Hty.   *) 
      
     admit. 
    }
    (*{ intros.
      pose proof (typing_wf_local_size Hty) as Hlt0.
      pose proof (typing_wf_named_size Hty) as Hlt1.
      set (foo := typing_wf_local Hty) in *.
      set (bar := typing_wf_named Hty) in *.
      assert (foo = typing_wf_local Hty) as Hfoo by auto.
      assert (bar = typing_wf_named Hty) as Hbar by auto. 
      assert (All_local_env_size (@typing_size cf Σ Δ) Γ' foo < typing_size H) as Hlt_foo by lia.
      assert (All_named_env_size (@typing_size cf Σ) Δ bar < typing_size H) as Hlt_bar by lia.
      clear - wfΣ X14 Xj Hbar Hfoo Hlt_bar Hlt_foo XΓ.
      apply XΓ; tas.  
    + admit.
    + admit. 
    (*+ revert bar Hlt_bar Hlt1 Eqn_bar.
      induction bar; simpl in *; cbn in *; constructor.
      - simpl in *. apply wf_named_inv in H. apply IHbar with (H) (Hty). ; tea.
        4: apply typing_wf_local_size.
        3: unfold bar. eapply (@typing_wf_named_size cf Σ Δ.
        * lia.
      - red. apply (X14 _ _ _ t2.2.π2.1). cbn. lia.
      - simpl in *. apply IHfoo. lia.
      - red. apply (X14 _ _ _ t2.1). cbn. lia.
      - red. apply (X14 _ _ _ t2.2.π2.1). cbn. lia.
    + revert foo Hlt.
      induction foo; cbn in *; constructor.
      1,3: apply IHfoo; lia.
      all: eapply Xj with (Hj := t2); simpl; cbn.
      all: lia.*)
    + revert foo Hfoo Hlt_foo.
      induction foo; simpl in *; cbn in *; constructor.
      - simpl in *. eapply IHfoo ; eauto. 3: lia. admit. admit.
      - red. apply (X14 _ _ _ _ t3.2.π2.1). cbn. lia.
      - simpl in *. eapply IHfoo ; eauto. 3: lia. admit. admit.
      - red. apply (X14 _ _ _ _ t3.1). cbn. lia.
      - red. apply (X14 _ _ _ _ t3.2.π2.1). cbn. lia.
    + revert foo Hfoo Hlt_foo.
      induction foo; cbn in *; constructor.
      - eapply IHfoo ; eauto. 3: lia. admit. admit.
      - admit. 
      - admit.
      - admit. 
      (*1,3: eapply IHfoo; eauto ; lia.
      all: eapply Xj with (Hj := t2); simpl; cbn.
      all: lia.*) }*)

    clear IH.
    assert (pΓ : PΓ Σ Δ (typing_wf_named H) Γ (typing_wf_local H)).
    { apply (X2 _ _ _ H). lia. }
    split; auto.
    set (wfΓ := typing_wf_local H); clearbody wfΓ.

    destruct H; simpl in pΓ;
      try solve [  match reverse goal with
                    H : _ |- _ => eapply H
                  end; eauto;
                  unshelve eapply X2; simpl; auto with arith].

    all: try solve [ match reverse goal with H : _ |- _ => eapply H end;
      eauto; [ unshelve eapply Xj | unshelve eapply X2 ]; simpl; auto with arith ].

    --clear p0 Xrel Xvar Xsort Xprod Xlam Xlet Xapp Xconst Xind Xctor Xcase Xproj Xfix Xcofix Xint Xfloat Xstring Xarr Xconv.
      unshelve eapply Xcast ; eauto.
      * apply (typing_wf_named H).  
      * unshelve eapply X1 ; simpl ; eauto with arith.
      * unshelve eapply X1 ; simpl ; eauto with arith.

    --clear p0 Xrel Xvar Xsort Xcast Xlam Xlet Xapp Xconst Xind Xctor Xcase Xproj Xfix Xcofix Xint Xfloat Xstring Xarr Xconv.
      eapply Xprod ; eauto.
      unshelve eapply Xj; simpl; auto with arith.
      simpl in X1. unshelve eapply X1 ; eauto with arith.
      
    --clear p0 Xrel Xvar Xsort Xcast Xprod Xlet Xapp Xconst Xind Xctor Xcase Xproj Xfix Xcofix Xint Xfloat Xstring Xarr Xconv.
      eapply Xlam ; eauto.
      unshelve eapply Xj ; simpl ; eauto with arith.
      simpl in X1. unshelve eapply X1 ; eauto with arith.
    
    --clear p0 Xrel Xvar Xsort Xcast Xprod Xlam Xapp Xconst Xind Xctor Xcase Xproj Xfix Xcofix Xint Xfloat Xstring Xarr Xconv.
      eapply Xlet ; eauto.
      unshelve eapply Xj ; simpl ; eauto with arith.
      simpl in X1. unshelve eapply X1 ; eauto with arith.
  
    --clear p0 Xrel Xvar Xsort Xcast Xprod Xlam Xlet Xconst Xind Xctor Xcase Xproj Xfix Xcofix Xint Xfloat Xstring Xarr Xconv.
      unshelve eapply (Xapp Σ wfΣ Δ _ Γ _ t l t_ty t' _ _ _ _ t0) ; eauto ; clear Xapp.
      eapply typing_wf_named ; tea.
      simpl in X1. eapply X1 ; eauto with arith.
      admit.
      (*simpl in X1 ; simpl in X2 ; clear Xj n. 
      generalize dependent t.
      induction t0.
      ++(*simpl in X1. unshelve eapply X1 ; eauto with arith.*) admit.
      ++(*simpl in X1. unshelve eapply X1 ; eauto with arith.*) admit.
      ++(*unshelve eapply (IHt0 wfΓ (mkApps t2 [hd])) ; eauto.
        About type_App.  
        Print typing_spine.*)*)

    --clear p0 Xrel Xvar Xsort Xcast Xprod Xlam Xlet Xapp Xind Xctor Xcase Xproj Xfix Xcofix Xint Xfloat Xstring Xarr Xconv.
      unshelve eapply (Xconst Σ wfΣ Δ (typing_wf_named _) Γ a0) ; eauto. 
      specialize (X1 [] [] _ _ (type_Prop Σ)). apply X1.
      rewrite typing_size_Prop. simpl ; lia.
      
    --clear p0 Xrel Xvar Xsort Xcast Xprod Xlam Xlet Xapp Xconst Xctor Xcase Xproj Xfix Xcofix Xint Xfloat Xstring Xarr Xconv.
      unshelve eapply (Xind Σ wfΣ Δ (typing_wf_named _) Γ a0) ; eauto. 
      specialize (X1 [] [] _ _ (type_Prop Σ)). apply X1.
      rewrite typing_size_Prop. simpl; lia.
      
    --clear p0 Xrel Xvar Xsort Xcast Xprod Xlam Xlet Xapp Xconst Xind Xcase Xproj Xfix Xcofix Xint Xfloat Xstring Xarr Xconv.
      unshelve eapply (Xctor Σ wfΣ Δ (typing_wf_named _) Γ a0) ; eauto. 
      specialize (X1 [] [] _ _ (type_Prop Σ)). apply X1.
      rewrite typing_size_Prop. simpl; lia.
    
    --clear p0 Xrel Xvar Xsort Xcast Xprod Xlam Xlet Xapp Xconst Xind Xctor Xproj Xfix Xcofix Xint Xfloat Xstring Xarr Xconv.
      simpl in pΓ.
      eapply (Xcase Σ wfΣ Δ (typing_wf_named _) Γ (typing_wf_local _) ci); eauto.
      ++specialize (X1 [] [] _ _ (type_Prop Σ)). apply X1.
        rewrite typing_size_Prop. simpl. rewrite <- Nat.succ_lt_mono.
        rewrite Nat.max_lt_iff ; left. apply typing_size_pos.
      ++assert (forall Γ' t T (Hty : Σ ;;; Δ ;;; Γ' |- t : T),
           typing_size Hty <= ctx_inst_size typing (@typing_size _) c1 ->
           P Σ Δ Γ' t T).
        { intros. eapply (X1 _ _ _ _ Hty). simpl.
          change (fun _ _ _ _ _ H => typing_size H) with (@typing_size cf).
          lia. }
        clear -X c1.
        revert c1 X.
        generalize (List.rev (subst_instance (puinst p) (ind_params mdecl ,,, ind_indices idecl : context))).
        generalize (pparams p ++ indices).
        intros l c ctxi IH; induction ctxi; constructor; eauto.
        * split; tas. eapply (IH _ _ _ t0); simpl; auto. lia.
        * eapply IHctxi. intros. eapply (IH _ _ _ Hty). simpl. lia.
        * eapply IHctxi. intros. eapply (IH _ _ _ Hty). simpl. lia.
        ++ simpl in X1. simpl in pΓ. auto. eapply (X1 _ _ _ _ H); eauto. simpl; auto with arith.
      ++ eapply (X2 _ _ _ H); eauto. simpl. subst predctx. lia.
      ++ eapply (X1 _ _ _ _ H0); simpl. lia.
      ++ clear X3 X2 Xj. revert a X1. clear. intros.
         subst ptm predctx.
         Opaque case_branch_type.
         simpl in X1.
         Transparent case_branch_type.
         induction a0; simpl in *.
         ** constructor.
         ** destruct r0 as [[? ?] ?]. constructor.
             --- intuition eauto.
                 +++ eapply (X1 _ _ _ _ t); eauto. clear -X1. simpl; auto with arith.
                     lia.
                 +++ eapply (X1 _ _ _ _ t0); eauto. simpl; auto with arith.
                     lia.
             --- apply IHa0. auto. intros.
                 eapply (X1 _ _ _ _ Hty). lia.

    --clear p0 Xrel Xvar Xsort Xcast Xprod Xlam Xlet Xapp Xconst Xind Xctor Xcase Xfix Xcofix Xint Xfloat Xstring Xarr Xconv.
      eapply Xproj; eauto; clear Xproj.
      ++specialize (X1 [] [] _ _ (type_Prop _)). apply X1. 
        rewrite typing_size_Prop. simpl. generalize (typing_size_pos H). lia.
      ++simpl in X1. admit.
      
    --clear p0 Xrel Xvar Xsort Xcast Xprod Xlam Xlet Xapp Xconst Xind Xctor Xcase Xproj Xcofix Xint Xfloat Xstring Xarr Xconv.
      eapply Xfix; eauto; clear Xfix.
      ++assert (forall j Hj, lift_typing_size (fun t T H => @typing_size cf Σ Δ Γ t T H) j Hj <
                  S (all_size _ (fun x p => on_def_type_size (@typing_size _ Σ Δ) _ _ p) a1) ->
                  Pj Σ Δ Γ j).
        { intros. eapply Xj with (Hj := Hj); eauto. simpl. lia. }
        clear -a1 X.
        induction a1; constructor.
        **eapply X with (Hj := p). cbn.
           unfold on_def_type_sorting_size, lift_sorting_size, option_default_size in *.
           cbn in *. lia.
        **apply IHa1. intros. eapply X with (Hj := Hj); eauto.
           simpl. lia.
      ++assert (forall Γ, wf_local Σ Δ Γ ->
                forall j Hj, lift_typing_size (fun t T H => @typing_size cf Σ Δ Γ t T H) j Hj <
                S (all_size (on_def_body (lift_typing3 typing Σ Δ) _ _) (fun x p => on_def_body_size (@typing_size cf Σ Δ) _ _ _ p) a2) ->
                Pj Σ Δ Γ j).
        { intros. eapply Xj with (Hj := Hj); eauto. simpl. lia. }
        clear -a2 X.
        remember (fix_context mfix) as mfixcontext eqn:e. clear e.
        induction a2; constructor.
        **eapply X with (Hj := p). 1: eapply typing_wf_local, p.1. cbn. lia.
        **apply IHa2. intros. eapply X with (Hj := Hj); eauto.
          simpl. lia.

    --clear p0 Xrel Xvar Xsort Xcast Xprod Xlam Xlet Xapp Xconst Xind Xctor Xcase Xproj Xfix Xint Xfloat Xstring Xarr Xconv.
      eapply Xcofix; eauto; clear Xcofix. simpl in *.
      ++assert (forall j Hj, lift_typing_size (fun t T H => @typing_size cf Σ Δ Γ t T H) j Hj <
                  S (all_size _ (fun x p => on_def_type_size (@typing_size _ Σ Δ) _ _ p) a1) ->
                  Pj Σ Δ Γ j).
        { intros. eapply Xj with (Hj := Hj); eauto. simpl. lia. }
        clear -a1 X.
        induction a1; constructor.
        **eapply X with (Hj := p). cbn.
          unfold on_def_type_sorting_size, lift_sorting_size, option_default_size in *.
          cbn in *. lia.
        **apply IHa1. intros. eapply X with (Hj := Hj); eauto.
          simpl. lia.
      ++assert (forall Γ, wf_local Σ Δ Γ ->
                forall j Hj, lift_typing_size (fun t T H => @typing_size cf Σ Δ Γ t T H) j Hj <
                S (all_size (on_def_body (lift_typing3 typing Σ Δ) _ _) (fun x p => on_def_body_size (@typing_size cf Σ Δ) _ _ _ p) a2) ->
                Pj Σ Δ Γ j).
        { intros. eapply Xj with (Hj := Hj); eauto. simpl. lia. }
        clear -a2 X.
        remember (fix_context mfix) as mfixcontext eqn:e. clear e.
        induction a2; constructor.
        **eapply X with (Hj := p). 1: eapply typing_wf_local, p.1. cbn. lia.
        **apply IHa2. intros. eapply X with (Hj := Hj); eauto.
          simpl. lia.

    --clear p0 Xrel Xvar Xsort Xcast Xprod Xlam Xlet Xapp Xconst Xind Xctor Xcase Xproj Xfix Xcofix Xint Xstring Xfloat Xconv.
      eapply (Xarr Σ wfΣ Δ (typing_wf_named _) Γ); eauto ; clear Xarr.
      * eapply (X1 _ _ _ _ H). simpl. subst s; lia.
      * eapply (X1 _ _ _ _ H0). simpl. subst s; lia.
      * assert (Xi : forall t (Hty : Σ ;;; Δ ;;; Γ |- t : ty), typing_size Hty < S (all_size _ (fun t p => typing_size p) a1) ->
                  P Σ Δ Γ t ty).
        { intros ? Hty ?; eapply (X1 _ _ _ _ Hty). simpl. lia. }
        clear -Xi a1.
        induction a1; constructor; eauto.
        + split => //. eapply (Xi _ p). cbn. lia.
        + unshelve eapply IHa1. intros. eapply (Xi _ Hty). simpl. lia.
    
    --clear p0 Xrel Xvar Xsort Xcast Xprod Xlam Xlet Xapp Xconst Xind Xctor Xcase Xproj Xfix Xcofix Xint Xstring Xfloat Xarr.
      eapply Xconv ; eauto ; clear Xconv.
      ++unshelve eapply (X1 _ _ _ _ H). simpl. lia.
      ++unshelve eapply (X1 _ _ _ _ H0). simpl. lia.
Admitted.

Arguments on_global_env {cf} Pcmp P !g.

Definition wf_ext_wf `{checker_flags} Σ : wf_ext Σ -> wf Σ := fst.

#[global]
Hint Immediate wf_ext_wf : core.
