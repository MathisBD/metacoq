(* Distributed under the terms of the MIT license. *)
From Coq Require CMorphisms.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICSize PCUICLiftSubst
     PCUICSigmaCalculus PCUICUnivSubst PCUICTyping PCUICReduction PCUICSubstitution
     PCUICReflect PCUICInduction PCUICClosed PCUICDepth PCUICOnFreeVars
     PCUICRename PCUICInst PCUICParallelReduction PCUICWeakening.

Require Import ssreflect ssrbool.
Require Import Morphisms CRelationClasses.
From Equations Require Import Equations.

Add Search Blacklist "pred1_rect".
Add Search Blacklist "_equation_".

Derive Signature for pred1 All2_fold.

Local Open Scope sigma_scope.

Local Set Keyed Unification.

Ltac solve_discr := (try (progress (prepare_discr; finish_discr; cbn [mkApps] in * )));
  try discriminate.

Equations map_In {A B : Type} (l : list A) (f : forall (x : A), In x l -> B) : list B :=
map_In nil _ := nil;
map_In (cons x xs) f := cons (f x _) (map_In xs (fun x H => f x _)).

Lemma map_In_spec {A B : Type} (f : A -> B) (l : list A) :
  map_In l (fun (x : A) (_ : In x l) => f x) = List.map f l.
Proof.
  remember (fun (x : A) (_ : In x l) => f x) as g.
  funelim (map_In l g) => //; simpl; rewrite (H f0); trivial.
Qed.

Equations mapi_context_In (ctx : context) (f : nat -> forall (x : context_decl), In x ctx -> context_decl) : context :=
mapi_context_In nil _ := nil;
mapi_context_In (cons x xs) f := cons (f #|xs| x _) (mapi_context_In xs (fun n x H => f n x _)).

Lemma mapi_context_In_spec (f : nat -> term -> term) (ctx : context) :
  mapi_context_In ctx (fun n (x : context_decl) (_ : In x ctx) => map_decl (f n) x) = 
  mapi_context f ctx.
Proof.
  remember (fun n (x : context_decl) (_ : In x ctx) => map_decl (f n) x) as g.
  funelim (mapi_context_In ctx g) => //; simpl; rewrite (H f0); trivial.
Qed.

Equations fold_context_In (ctx : context) (f : context -> forall (x : context_decl), In x ctx -> context_decl) : context :=
fold_context_In nil _ := nil;
fold_context_In (cons x xs) f := 
  let xs' := fold_context_In xs (fun n x H => f n x _) in
  cons (f xs' x _) xs'.

Equations fold_context (f : context -> context_decl -> context_decl) (ctx : context) : context :=
  fold_context f nil := nil;
  fold_context f (cons x xs) := 
    let xs' := fold_context f xs in
    cons (f xs' x ) xs'.
  
Lemma fold_context_length f Γ : #|fold_context f Γ| = #|Γ|.
Proof.
  now apply_funelim (fold_context f Γ); intros; simpl; auto; f_equal.
Qed.
Hint Rewrite fold_context_length : len.

Lemma fold_context_In_spec (f : context -> context_decl -> context_decl) (ctx : context) :
  fold_context_In ctx (fun n (x : context_decl) (_ : In x ctx) => f n x) = 
  fold_context f ctx.
Proof.
  remember (fun n (x : context_decl) (_ : In x ctx) => f n x) as g.
  funelim (fold_context_In ctx g) => //; simpl; rewrite (H f0); trivial.
Qed.

Instance fold_context_Proper : Proper (`=2` ==> `=1`) fold_context.
Proof.
  intros f f' Hff' x.
  funelim (fold_context f x); simpl; auto. simp fold_context.
  now rewrite (H f' Hff').
Qed.

Section list_depth.
  Context {A : Type} (f : A -> nat).

  Lemma In_list_depth:
    forall x xs, In x xs -> f x < S (list_depth_gen f xs).
  Proof.
    intros. induction xs.
    destruct H.
    * destruct H. simpl; subst. lia.
      specialize (IHxs H). simpl. lia.
  Qed.

End list_depth.

Notation mfixpoint_depth := (mfixpoint_depth_gen depth).

Lemma mfixpoint_depth_In {mfix d} :
  In d mfix ->
  depth (dbody d) <= mfixpoint_depth mfix /\
  depth (dtype d) <= mfixpoint_depth mfix.
Proof.
  induction mfix in d |- *; simpl; auto.
  move=> [->|H]. unfold def_depth_gen. split; try lia.
  destruct (IHmfix d H). split; lia.
Qed.

Lemma mfixpoint_depth_nth_error {mfix i d} :
  nth_error mfix i = Some d ->
  depth (dbody d) <= mfixpoint_depth mfix.
Proof.
  induction mfix in i, d |- *; destruct i; simpl; try congruence.
  move=> [] ->. unfold def_depth_gen. lia.
  move/IHmfix. lia.
Qed.

Section FoldFix.
  Context (rho : context -> term -> term).
  Context (Γ : context).

  Fixpoint fold_fix_context acc m :=
    match m with
  | [] => acc
    | def :: fixd =>
      fold_fix_context (vass def.(dname) (lift0 #|acc| (rho Γ def.(dtype))) :: acc) fixd
    end.  
End FoldFix.

Lemma fold_fix_context_length f Γ l m : #|fold_fix_context f Γ l m| = #|m| + #|l|.
Proof.
  induction m in l |- *; simpl; auto. rewrite IHm. simpl. auto with arith.
Qed.

Fixpoint isFixLambda_app (t : term) : bool :=
match t with
| tApp (tFix _ _) _ => true
| tApp (tLambda _ _ _) _ => true 
| tApp f _ => isFixLambda_app f
| _ => false
end.

Inductive fix_lambda_app_view : term -> term -> Type :=
| fix_lambda_app_fix mfix i l a : fix_lambda_app_view (mkApps (tFix mfix i) l) a
| fix_lambda_app_lambda na ty b l a : fix_lambda_app_view (mkApps (tLambda na ty b) l) a
| fix_lambda_app_other t a : ~~ isFixLambda_app (tApp t a) -> fix_lambda_app_view t a.
Derive Signature for fix_lambda_app_view.

Lemma view_lambda_fix_app (t u : term) : fix_lambda_app_view t u.
Proof.
  induction t; try solve [apply fix_lambda_app_other; simpl; auto].
  apply (fix_lambda_app_lambda na t1 t2 [] u).
  destruct IHt1.
  pose proof (fix_lambda_app_fix mfix i (l ++ [t2]) a).
  change (tApp (mkApps (tFix mfix i) l) t2) with (mkApps (mkApps (tFix mfix i) l) [t2]).
  now rewrite mkApps_nested.
  pose proof (fix_lambda_app_lambda na ty b (l ++ [t2]) a).
  change (tApp (mkApps (tLambda na ty b) l) t2) with (mkApps (mkApps (tLambda na ty b) l) [t2]).
  now rewrite mkApps_nested.
  destruct t; try solve [apply fix_lambda_app_other; simpl; auto].
  apply (fix_lambda_app_fix mfix idx [] u).
Defined.

Lemma eq_pair_transport {A B} (x y : A) (t : B y) (eq : x = y) : 
  (x; eq_rect_r (fun x => B x) t eq) = (y; t) :> ∑ x, B x. 
Proof.
  destruct eq. unfold eq_rect_r. now simpl.
Qed.

Lemma view_lambda_fix_app_fix_app_sigma mfix idx l a : 
  ((mkApps (tFix mfix idx) l); view_lambda_fix_app (mkApps (tFix mfix idx) l) a) =   
  ((mkApps (tFix mfix idx) l); fix_lambda_app_fix mfix idx l a) :> ∑ t, fix_lambda_app_view t a.
Proof.
  induction l using rev_ind; simpl; auto.
  rewrite -{1 2}mkApps_nested.
  simpl. dependent rewrite IHl.
  change (tApp (mkApps (tFix mfix idx) l) x) with (mkApps (mkApps (tFix mfix idx) l) [x]).
  now rewrite eq_pair_transport.
Qed.

Lemma view_lambda_fix_app_lambda_app_sigma na ty b l a : 
  ((mkApps (tLambda na ty b) l); view_lambda_fix_app (mkApps (tLambda na ty b) l) a) =   
  ((mkApps (tLambda na ty b) l); fix_lambda_app_lambda na ty b l a) :> ∑ t, fix_lambda_app_view t a.
Proof.
  induction l using rev_ind; simpl; auto.
  rewrite -{1 2}mkApps_nested.
  simpl. dependent rewrite IHl.
  change (tApp (mkApps (tLambda na ty b) l) x) with (mkApps (mkApps (tLambda na ty b) l) [x]).
  now rewrite eq_pair_transport.
Qed.

Set Equations With UIP.

Lemma view_lambda_fix_app_fix_app mfix idx l a : 
  view_lambda_fix_app (mkApps (tFix mfix idx) l) a =   
  fix_lambda_app_fix mfix idx l a.
Proof.
  pose proof (view_lambda_fix_app_fix_app_sigma mfix idx l a).
  now noconf H.
Qed.

Lemma view_lambda_fix_app_lambda_app na ty b l a : 
  view_lambda_fix_app (mkApps (tLambda na ty b) l) a =   
  fix_lambda_app_lambda na ty b l a.
Proof.
  pose proof (view_lambda_fix_app_lambda_app_sigma na ty b l a).
  now noconf H.
Qed.

Hint Rewrite view_lambda_fix_app_fix_app view_lambda_fix_app_lambda_app : rho.

Equations construct_cofix_discr (t : term) : bool :=
construct_cofix_discr (tConstruct _ _ _) => true;
construct_cofix_discr (tCoFix _ _) => true;
construct_cofix_discr _ => false.
Transparent construct_cofix_discr.

Equations discr_construct_cofix (t : term) : Prop :=
  { | tConstruct _ _ _ => False;
    | tCoFix _ _ => False;
    | _ => True }.
Transparent discr_construct_cofix.

Inductive construct_cofix_view : term -> Type :=
| construct_cofix_construct ind u i : construct_cofix_view (tConstruct ind u i)
| construct_cofix_cofix mfix idx : construct_cofix_view (tCoFix mfix idx)
| construct_cofix_other t : discr_construct_cofix t -> construct_cofix_view t.

Equations view_construct_cofix (t : term) : construct_cofix_view t :=
{ | tConstruct ind u i => construct_cofix_construct ind u i;
  | tCoFix mfix idx => construct_cofix_cofix mfix idx;
  | t => construct_cofix_other t I }.

Equations discr_construct0_cofix (t : term) : Prop :=
  { | tConstruct _ u _ => u <> 0;
    | tCoFix _ _ => False;
    | _ => True }.
Transparent discr_construct0_cofix.
Inductive construct0_cofix_view : term -> Type :=
| construct0_cofix_construct ind i : construct0_cofix_view (tConstruct ind 0 i)
| construct0_cofix_cofix mfix idx : construct0_cofix_view (tCoFix mfix idx)
| construct0_cofix_other t : discr_construct0_cofix t -> construct0_cofix_view t.

Equations view_construct0_cofix (t : term) : construct0_cofix_view t :=
{ | tConstruct ind 0 i => construct0_cofix_construct ind i;
  | tCoFix mfix idx => construct0_cofix_cofix mfix idx;
  | t => construct0_cofix_other t _ }.

Lemma fix_context_gen_assumption_context k Γ : assumption_context (fix_context_gen k Γ).
Proof.
  rewrite /fix_context_gen. revert k.
  induction Γ using rev_ind.
  constructor. intros.
  rewrite mapi_rec_app /= List.rev_app_distr /=. constructor.
  apply IHΓ.
Qed.

Lemma fix_context_assumption_context m : assumption_context (fix_context m).
Proof. apply fix_context_gen_assumption_context. Qed.

Lemma nth_error_assumption_context Γ n d :
  assumption_context Γ -> nth_error Γ n = Some d ->
  decl_body d = None.
Proof.
  intros H; induction H in n, d |- * ; destruct n; simpl; try congruence; eauto.
  now move=> [<-] //.
Qed.

Lemma decompose_app_rec_rename r t l :
  forall hd args, 
  decompose_app_rec t l = (hd, args) ->
  decompose_app_rec (rename r t) (map (rename r) l) = (rename r hd, map (rename r) args).
Proof.
  induction t in l |- *; simpl; try intros hd args [= <- <-]; auto.
  intros hd args e. now apply (IHt1 _ _ _ e).
Qed.

Lemma decompose_app_rename {r t hd args} :
  decompose_app t = (hd, args) ->
  decompose_app (rename r t) = (rename r hd, map (rename r) args).
Proof. apply decompose_app_rec_rename. Qed.

Lemma mkApps_eq_decompose_app {t t' l l'} :
  mkApps t l = mkApps t' l' ->
  decompose_app_rec t l = decompose_app_rec t' l'.
Proof.
  induction l in t, t', l' |- *; simpl.
  - intros ->. rewrite !decompose_app_rec_mkApps.
    now rewrite app_nil_r.
  - intros H. apply (IHl _ _ _ H).
Qed.


Lemma atom_mkApps {t l} : atom (mkApps t l) -> atom t /\ l = [].
Proof.
  induction l in t |- *; simpl; auto.
  intros. destruct (IHl _ H). discriminate.
Qed.

Lemma pred_atom_mkApps {t l} : pred_atom (mkApps t l) -> pred_atom t /\ l = [].
Proof.
  induction l in t |- *; simpl; auto.
  intros. destruct (IHl _ H). discriminate.
Qed.

Ltac finish_discr :=
  repeat PCUICAstUtils.finish_discr ||
         match goal with
         | [ H : atom (mkApps _ _) |- _ ] => apply atom_mkApps in H; intuition subst
         | [ H : pred_atom (mkApps _ _) |- _ ] => apply pred_atom_mkApps in H; intuition subst
         end.

Ltac solve_discr ::=
  (try (progress (prepare_discr; finish_discr; cbn [mkApps] in * )));
  (try (match goal with
        | [ H : is_true (atom _) |- _ ] => discriminate
        | [ H : is_true (atom (mkApps _ _)) |- _ ] => destruct (atom_mkApps H); subst; try discriminate
        | [ H : is_true (pred_atom _) |- _ ] => discriminate
        | [ H : is_true (pred_atom (mkApps _ _)) |- _ ] => destruct (pred_atom_mkApps H); subst; try discriminate
        end)).

Lemma is_constructor_app_ge n l l' : is_constructor n l -> is_constructor n (l ++ l').
Proof.
  unfold is_constructor. destruct nth_error eqn:Heq.
  rewrite nth_error_app_lt ?Heq //; eauto using nth_error_Some_length.
  discriminate.
Qed.

Lemma is_constructor_prefix n args args' : 
  ~~ is_constructor n (args ++ args') ->
  ~~ is_constructor n args.
Proof.
  rewrite /is_constructor.
  elim: nth_error_spec. rewrite app_length.
  move=> i hi harg. elim: nth_error_spec.
  move=> i' hi' hrarg'.
  rewrite nth_error_app_lt in hi; eauto. congruence.
  auto.
  rewrite app_length. move=> ge _.
  elim: nth_error_spec; intros; try lia. auto.
Qed.
    

Section Pred1_inversion.
  
  Lemma pred_snd_nth:
    forall (Σ : global_env) (Γ Δ : context) (c : nat) (brs1 brs' : list (nat * term)),
      All2
        (on_Trel (pred1 Σ Γ Δ) snd) brs1
        brs' ->
        pred1_ctx Σ Γ Δ ->
      pred1 Σ Γ Δ
              (snd (nth c brs1 (0, tDummy)))
              (snd (nth c brs' (0, tDummy))).
  Proof.
    intros Σ Γ Δ c brs1 brs' brsl. intros.
    induction brsl in c |- *; simpl. destruct c; now apply pred1_refl_gen.
    destruct c; auto.
  Qed.

  Lemma pred_mkApps Σ Γ Δ M0 M1 N0 N1 :
    pred1 Σ Γ Δ M0 M1 ->
    All2 (pred1 Σ Γ Δ) N0 N1 ->
    pred1 Σ Γ Δ (mkApps M0 N0) (mkApps M1 N1).
  Proof.
    intros.
    induction X0 in M0, M1, X |- *. auto.
    simpl. eapply IHX0. now eapply pred_app.
  Qed.

  Lemma pred1_mkApps_tConstruct (Σ : global_env) (Γ Δ : context)
        ind pars k (args : list term) c :
    pred1 Σ Γ Δ (mkApps (tConstruct ind pars k) args) c ->
    {args' : list term & (c = mkApps (tConstruct ind pars k) args') * (All2 (pred1 Σ Γ Δ) args args') }%type.
  Proof with solve_discr.
    revert c. induction args using rev_ind; intros; simpl in *.
    depelim X... exists []. intuition auto.
    intros. rewrite <- mkApps_nested in X.
    depelim X... simpl in H; noconf H. solve_discr.
    prepare_discr. apply mkApps_eq_decompose_app in H.
    rewrite !decompose_app_rec_mkApps in H. noconf H.
    destruct (IHargs _ X1) as [args' [-> Hargs']].
    exists (args' ++ [N1]).
    rewrite <- mkApps_nested. intuition auto.
    eapply All2_app; auto.
  Qed.

  Lemma pred1_mkApps_refl_tConstruct (Σ : global_env) Γ Δ i k u l l' :
    pred1 Σ Γ Δ (mkApps (tConstruct i k u) l) (mkApps (tConstruct i k u) l') ->
    All2 (pred1 Σ Γ Δ) l l'.
  Proof.
    intros.
    eapply pred1_mkApps_tConstruct in X. destruct X.
    destruct p. now eapply mkApps_eq_inj in e as [_ <-].
  Qed.

  Lemma pred1_mkApps_tInd (Σ : global_env) (Γ Δ : context)
        ind u (args : list term) c :
    pred1 Σ Γ Δ (mkApps (tInd ind u) args) c ->
    {args' : list term & (c = mkApps (tInd ind u) args') * (All2 (pred1 Σ Γ Δ) args args') }%type.
  Proof with solve_discr.
    revert c. induction args using rev_ind; intros; simpl in *.
    depelim X... exists []. intuition auto.
    intros. rewrite <- mkApps_nested in X.
    depelim X... simpl in H; noconf H. solve_discr.
    prepare_discr. apply mkApps_eq_decompose_app in H.
    rewrite !decompose_app_rec_mkApps in H. noconf H.
    destruct (IHargs _ X1) as [args' [-> Hargs']].
    exists (args' ++ [N1]).
    rewrite <- mkApps_nested. intuition auto.
    eapply All2_app; auto.
  Qed.

  Lemma pred1_mkApps_tRel (Σ : global_env) (Γ Δ : context) k b (args : list term) c :
    nth_error Γ k = Some b -> decl_body b = None ->
    pred1 Σ Γ Δ (mkApps (tRel k) args) c ->
    {args' : list term & (c = mkApps (tRel k) args') * (All2 (pred1 Σ Γ Δ) args args') }%type.
  Proof with solve_discr.
    revert c. induction args using rev_ind; intros; simpl in *.
    - depelim X...
      * exists []. intuition auto.
        eapply nth_error_pred1_ctx in a; eauto.
        destruct a as [body' [eqopt _]]. rewrite H /= H0 in eqopt. discriminate.
      * exists []; intuition auto.
    - rewrite -mkApps_nested /= in X.
      depelim X; try (simpl in H1; noconf H1); solve_discr.
      * prepare_discr. apply mkApps_eq_decompose_app in H1.
        rewrite !decompose_app_rec_mkApps in H1. noconf H1.
      * destruct (IHargs _ H H0 X1) as [args' [-> Hargs']].
        exists (args' ++ [N1]).
        rewrite <- mkApps_nested. intuition auto.
        eapply All2_app; auto.
  Qed.

  Lemma pred1_mkApps_tConst_axiom (Σ : global_env) (Γ Δ : context)
        cst u (args : list term) cb c :
    declared_constant Σ cst cb -> cst_body cb = None ->
    pred1 Σ Γ Δ (mkApps (tConst cst u) args) c ->
    {args' : list term & (c = mkApps (tConst cst u) args') * (All2 (pred1 Σ Γ Δ) args args') }%type.
  Proof with solve_discr.
    revert c. induction args using rev_ind; intros; simpl in *.
    depelim X...
    - red in H, isdecl. rewrite isdecl in H; noconf H.
      congruence.
    - exists []. intuition auto.
    - rewrite <- mkApps_nested in X.
      depelim X...
      * prepare_discr. apply mkApps_eq_decompose_app in H1.
        rewrite !decompose_app_rec_mkApps in H1. noconf H1.
      * destruct (IHargs _ H H0 X1) as [args' [-> Hargs']].
        exists (args' ++ [N1]).
        rewrite <- mkApps_nested. intuition auto.
        eapply All2_app; auto.
  Qed.

  Lemma pred1_mkApps_tFix_inv Σ (Γ Δ : context)
        mfix0 idx (args0 : list term) c d :
    nth_error mfix0 idx = Some d ->
    ~~ is_constructor (rarg d) args0 ->
    pred1 Σ Γ Δ (mkApps (tFix mfix0 idx) args0) c ->
    ({ mfix1 & { args1 : list term &
                         (c = mkApps (tFix mfix1 idx) args1) *
                         All2_prop2_eq Γ Δ (Γ ,,, fix_context mfix0) (Δ ,,, fix_context mfix1)
                                       dtype dbody
                                    (fun x => (dname x, rarg x))
                                    (pred1 Σ) mfix0 mfix1 *
                         (All2 (pred1 Σ Γ Δ) ) args0 args1 } }%type).
  Proof with solve_discr.
    intros hnth isc pred. remember (mkApps _ _) as fixt.
    revert mfix0 idx args0 Heqfixt hnth isc.
    induction pred; intros; solve_discr.
    - unfold unfold_fix in e.
      red in a1.
      eapply All2_nth_error_Some in a1; eauto.
      destruct a1 as [t' [ht' [hds [hr [= eqna eqrarg]]]]].
      rewrite ht' in e => //. noconf e. rewrite -eqrarg in e0.
      rewrite e0 in isc => //.
    - destruct args0 using rev_ind. noconf Heqfixt. clear IHargs0.
      rewrite <- mkApps_nested in Heqfixt. noconf Heqfixt.
      clear IHpred2. specialize (IHpred1 _ _ _ eq_refl).
      specialize (IHpred1 hnth). apply is_constructor_prefix in isc.
      specialize (IHpred1 isc).
      destruct IHpred1 as [? [? [[? ?] ?]]].
      eexists _. eexists (_ ++ [N1]). rewrite <- mkApps_nested.
      intuition eauto. simpl. subst M1. reflexivity.
      eapply All2_app; eauto.
    - exists mfix1, []. intuition auto.
    - subst t. solve_discr.
  Qed.

  Lemma pred1_mkApps_tFix_refl_inv (Σ : global_env) (Γ Δ : context)
        mfix0 mfix1 idx0 idx1 (args0 args1 : list term) d :
    nth_error mfix0 idx0 = Some d ->
    is_constructor (rarg d) args0 = false ->
    pred1 Σ Γ Δ (mkApps (tFix mfix0 idx0) args0) (mkApps (tFix mfix1 idx1) args1) ->
    (All2_prop2_eq Γ Δ (Γ ,,, fix_context mfix0) (Δ ,,, fix_context mfix1)
                   dtype dbody
                   (fun x => (dname x, rarg x))
                   (pred1 Σ) mfix0 mfix1 *
     (All2 (pred1 Σ Γ Δ) ) args0 args1).
  Proof with solve_discr.
    intros Hnth Hisc.
    remember (mkApps _ _) as fixt.
    remember (mkApps _ args1) as fixt'.
    intros pred. revert mfix0 mfix1 idx0 args0 d Hnth Hisc idx1 args1 Heqfixt Heqfixt'.
    induction pred; intros; solve_discr.
    - (* Not reducible *)
      red in a1. eapply All2_nth_error_Some in a1; eauto.
      destruct a1 as [t' [Hnth' [Hty [Hpred Hann]]]].
      unfold unfold_fix in e. destruct (nth_error mfix1 idx) eqn:hfix1.
      noconf e. noconf Hnth'.
      move: Hann => [=] Hname Hrarg.
      all:congruence. 

    - destruct args0 using rev_ind; noconf Heqfixt. clear IHargs0.
      rewrite <- mkApps_nested in Heqfixt. noconf Heqfixt.
      destruct args1 using rev_ind; noconf Heqfixt'. clear IHargs1.
      rewrite <- mkApps_nested in Heqfixt'. noconf Heqfixt'.
      clear IHpred2.
      assert (is_constructor (rarg d) args0 = false).
      { move: Hisc. rewrite /is_constructor.
        elim: nth_error_spec. rewrite app_length.
        move=> i hi harg. elim: nth_error_spec.
        move=> i' hi' hrarg'.
        rewrite nth_error_app_lt in hi; eauto. congruence.
        auto.
        rewrite app_length. move=> ge _.
        elim: nth_error_spec; intros; try lia. auto.
      }
      specialize (IHpred1 _ _ _ _ _ Hnth H _ _ eq_refl eq_refl).
      destruct IHpred1 as [? ?]. red in a.
      unfold All2_prop2_eq. split. apply a. apply All2_app; auto.
    - constructor; auto.
    - subst. solve_discr.
  Qed.

  Lemma pred1_mkApps_tCoFix_inv (Σ : global_env) (Γ Δ : context)
        mfix0 idx (args0 : list term) c :
    pred1 Σ Γ Δ (mkApps (tCoFix mfix0 idx) args0) c ->
    ∑ mfix1 args1,
      (c = mkApps (tCoFix mfix1 idx) args1) *
      All2_prop2_eq Γ Δ (Γ ,,, fix_context mfix0) (Δ ,,, fix_context mfix1) dtype dbody
                    (fun x => (dname x, rarg x))
                    (pred1 Σ) mfix0 mfix1 *
      (All2 (pred1 Σ Γ Δ) ) args0 args1.
  Proof with solve_discr.
    intros pred. remember (mkApps _ _) as fixt. revert mfix0 idx args0 Heqfixt.
    induction pred; intros; solve_discr.
    - destruct args0 using rev_ind. noconf Heqfixt. clear IHargs0.
      rewrite <- mkApps_nested in Heqfixt. noconf Heqfixt.
      clear IHpred2. specialize (IHpred1 _ _ _ eq_refl).
      destruct IHpred1 as [? [? [[-> ?] ?]]].
      eexists x, (x0 ++ [N1]). intuition auto.
      now rewrite <- mkApps_nested.
      eapply All2_app; eauto.
    - exists mfix1, []; intuition (simpl; auto).
    - subst t; solve_discr.
  Qed.

  Lemma pred1_mkApps_tCoFix_refl_inv (Σ : global_env) (Γ Δ : context)
        mfix0 mfix1 idx (args0 args1 : list term) :
    pred1 Σ Γ Δ (mkApps (tCoFix mfix0 idx) args0) (mkApps (tCoFix mfix1 idx) args1) ->
      All2_prop2_eq Γ Δ (Γ ,,, fix_context mfix0) (Δ ,,, fix_context mfix1) dtype dbody
                    (fun x => (dname x, rarg x))
                    (pred1 Σ) mfix0 mfix1 *
      (All2 (pred1 Σ Γ Δ)) args0 args1.
  Proof with solve_discr.
    intros pred. remember (mkApps _ _) as fixt.
    remember (mkApps _ args1) as fixt'.
    revert mfix0 mfix1 idx args0 args1 Heqfixt Heqfixt'.
    induction pred; intros; symmetry in Heqfixt; solve_discr.
    - destruct args0 using rev_ind. noconf Heqfixt. clear IHargs0.
      rewrite <- mkApps_nested in Heqfixt. noconf Heqfixt.
      clear IHpred2.
      symmetry in Heqfixt'.
      destruct args1 using rev_ind. discriminate. rewrite <- mkApps_nested in Heqfixt'.
      noconf Heqfixt'.
      destruct (IHpred1 _ _ _ _ _ eq_refl eq_refl) as [H H'].
      unfold All2_prop2_eq. split. apply H. apply All2_app; auto.
    - repeat finish_discr.
      unfold All2_prop2_eq. intuition (simpl; auto).
    - subst t; solve_discr.
  Qed.

End Pred1_inversion.

Hint Constructors pred1 : pcuic.

Notation predicate_depth := (predicate_depth_gen depth).

Section Rho.
  Context {cf : checker_flags}.
  Context (Σ : global_env).
  Context (wfΣ : wf Σ).

  #[program] Definition map_fix_rho {t} (rho : context -> forall x, depth x < depth t -> term) Γ mfixctx (mfix : mfixpoint term)
    (H : mfixpoint_depth mfix < depth t) :=
    (map_In mfix (fun d (H : In d mfix) => {| dname := dname d; 
        dtype := rho Γ (dtype d) _;
        dbody := rho (Γ ,,, mfixctx) (dbody d) _; rarg := (rarg d) |})).
  Next Obligation.
    eapply (In_list_depth (def_depth_gen depth)) in H.
    eapply le_lt_trans with (def_depth_gen depth d).
    unfold def_depth_gen. lia.
    unfold mfixpoint_depth in H0.
    lia.
  Qed.
  Next Obligation.
    eapply (In_list_depth (def_depth_gen depth)) in H.
    eapply le_lt_trans with (def_depth_gen depth d).
    unfold def_depth_gen. lia.
    unfold mfixpoint_depth in H0.
    lia.
  Qed.

  Equations? fold_fix_context_wf mfix 
      (rho : context -> forall x, depth x <= (mfixpoint_depth mfix) -> term) 
      (Γ acc : context) : context :=
  fold_fix_context_wf [] rho Γ acc => acc ;
  fold_fix_context_wf (d :: mfix) rho Γ acc => 
    fold_fix_context_wf mfix (fun Γ x Hx => rho Γ x _) Γ (vass (dname d) (lift0 #|acc| (rho Γ (dtype d) _)) :: acc).
  Proof.
    lia. unfold def_depth_gen. lia.        
  Qed.
  Transparent fold_fix_context_wf.

  #[program] Definition map_terms {t} (rho : context -> forall x, depth x < depth t -> term) Γ (l : list term)
    (H : list_depth_gen depth l < depth t) :=
    (map_In l (fun t (H : In t l) => rho Γ t _)).
  Next Obligation.
    eapply (In_list_depth depth) in H. lia.
  Qed.

  Section rho_ctx.
    Context (Γ : context).
    Context (rho : context -> forall x, depth x <= context_depth Γ -> term).
    
    Program Definition rho_ctx_over_wf :=
      fold_context_In Γ (fun Γ' d hin => 
        match d with
        | {| decl_name := na; decl_body := None; decl_type := T |} =>
            vass na (rho Γ' T _)
        | {| decl_name := na; decl_body := Some b; decl_type := T |} =>
          vdef na (rho Γ' b _) (rho Γ' T _)
        end).

      Next Obligation.
        eapply (In_list_depth (decl_depth_gen depth)) in hin.
        unfold decl_depth_gen at 1 in hin. simpl in *. unfold context_depth. lia.
      Qed.
      Next Obligation.
        eapply (In_list_depth (decl_depth_gen depth)) in hin.
        unfold decl_depth_gen at 1 in hin. simpl in *. unfold context_depth. lia.
      Qed.
      Next Obligation.
        eapply (In_list_depth (decl_depth_gen depth)) in hin.
        unfold decl_depth_gen at 1 in hin. simpl in *. unfold context_depth. lia.
      Qed.
  End rho_ctx.

  Notation fold_context_term f := (fold_context (fun Γ' => map_decl (f Γ'))).

  Lemma rho_ctx_over_wf_eq (rho : context -> term -> term) (Γ : context) : 
    rho_ctx_over_wf Γ (fun Γ x hin => rho Γ x) =
    fold_context_term rho Γ.
  Proof.
    rewrite /rho_ctx_over_wf fold_context_In_spec.
    apply fold_context_Proper. intros n x.
    now destruct x as [na [b|] ty]; simpl.
  Qed.
  Hint Rewrite rho_ctx_over_wf_eq : rho.
   
  #[program]
  Definition map_br_wf {t} (rho : context -> forall x, depth x < depth t -> term)
    Γ (p : PCUICAst.predicate term)
    (br : branch term) (H : depth (bbody br) < depth t) :=
    let bcontext' := inst_case_branch_context p br in
    {| bcontext := br.(bcontext);
       bbody := rho (Γ ,,, bcontext') br.(bbody) _ |}.

  Definition map_br_gen (rho : context -> term -> term) Γ p (br : branch term) :=
    let bcontext' := inst_case_branch_context p br in
    {| bcontext := br.(bcontext);
       bbody := rho (Γ ,,, bcontext') br.(bbody) |}.

  Lemma map_br_map (rho : context -> term -> term) t Γ p l H : 
    @map_br_wf t (fun Γ x Hx => rho Γ x) Γ p l H = map_br_gen rho Γ p l. 
  Proof. 
    unfold map_br_wf, map_br_gen. now f_equal; autorewrite with rho.
  Qed. 
  Hint Rewrite map_br_map : rho.

  #[program] Definition map_brs_wf {t} (rho : context -> forall x, depth x < depth t -> term) Γ 
    p (l : list (branch term))
    (H : list_depth_gen (depth ∘ bbody) l < depth t) :=
    map_In l (fun br (H : In br l) => map_br_wf rho Γ p br _).
  Next Obligation.
    eapply (In_list_depth (depth ∘ bbody)) in H. lia.
  Qed.

  Lemma map_brs_map (rho : context -> term -> term) t Γ p l H : 
    @map_brs_wf t (fun Γ x Hx => rho Γ x) Γ p l H = map (map_br_gen rho Γ p) l. 
  Proof. 
    unfold map_brs_wf, map_br_wf. rewrite map_In_spec.
    apply map_ext => x. now autorewrite with rho.
  Qed. 
  Hint Rewrite map_brs_map : rho.

  #[program] Definition rho_predicate_wf {t} (rho : context -> forall x, depth x < depth t -> term) Γ 
    (p : PCUICAst.predicate term) (H : predicate_depth p < depth t) :=
    let params' := map_terms rho Γ p.(pparams) _ in
    let pcontext' := inst_case_context params' p.(puinst) p.(pcontext) in
    {| pparams := params';
     puinst := p.(puinst) ;
     pcontext := p.(pcontext) ;
     preturn := rho (Γ ,,, pcontext') p.(preturn) _ |}.
    Next Obligation.
      pose proof (context_depth_inst_case_context p.(pparams) p.(puinst) p.(pcontext)).
      rewrite /predicate_depth in H. lia.
    Qed.
    Next Obligation.
      rewrite /predicate_depth in H. lia.
    Qed.

  Definition rho_predicate_gen (rho : context -> term -> term) Γ
    (p : PCUICAst.predicate term) :=
    let params' := map (rho Γ) p.(pparams) in
    let pcontext' := inst_case_context params' p.(puinst) p.(pcontext) in
    {| pparams := params';
       puinst := p.(puinst) ;
       pcontext := p.(pcontext) ;
       preturn := rho (Γ ,,, pcontext') p.(preturn) |}.
  
  Lemma map_terms_map (rho : context -> term -> term) t Γ l H : 
    @map_terms t (fun Γ x Hx => rho Γ x) Γ l H = map (rho Γ) l. 
  Proof. 
    unfold map_terms. now rewrite map_In_spec.
  Qed. 
  Hint Rewrite map_terms_map : rho.
   
  Lemma rho_predicate_map_predicate {t} (rho : context -> term -> term) Γ p (H : predicate_depth p < depth t) :
    rho_predicate_wf (fun Γ x H => rho Γ x) Γ p H =
    rho_predicate_gen rho Γ p.
  Proof.
    rewrite /rho_predicate_gen /rho_predicate_wf.
    f_equal; simp rho => //.
  Qed.
  Hint Rewrite @rho_predicate_map_predicate : rho.

  Definition inspect {A} (x : A) : { y : A | x = y } := exist x eq_refl.

  Arguments Nat.max : simpl never.

  #[program]
  Definition rho_iota_red_wf {t} (rho : context -> forall x, depth x < depth t -> term) Γ 
    (p : PCUICAst.predicate term) npar (args : list term) (br : branch term)
    (H : depth (bbody br) < depth t) :=
    let bctx := inst_case_branch_context p br in
    (* let rhobctx := rho_ctx_over_wf bctx (fun Γ' x Hx => rho (Γ ,,, Γ') x _) in *)
    let br' := map_br_wf rho Γ p br _ in
    subst0 (List.rev (skipn npar args)) (expand_lets bctx (bbody br')).
    
  Definition rho_iota_red_gen (rho : context -> term -> term) Γ 
    (p : PCUICAst.predicate term) npar (args : list term) (br : branch term) :=
    let bctx := inst_case_branch_context p br in
    (* let rhobctx := fold_context_term (fun Γ' => rho (Γ ,,, Γ')) bctx in *)
    subst0 (List.rev (skipn npar args)) (expand_lets bctx (rho (Γ ,,, bctx) (bbody br))).

  Lemma rho_iota_red_wf_gen (rho : context -> term -> term) t Γ p npar args br H : 
    rho_iota_red_wf (t:=t) (fun Γ x H => rho Γ x) Γ p npar args br H =
    rho_iota_red_gen rho Γ p npar args br.
  Proof.
    rewrite /rho_iota_red_wf /rho_iota_red_gen. f_equal.
  Qed.
  Hint Rewrite @rho_iota_red_wf_gen : rho.

  Lemma bbody_branch_depth brs p :
    list_depth_gen (depth ∘ bbody) brs < 
    S (list_depth_gen (branch_depth_gen depth p) brs).
  Proof.
    rewrite /branch_depth_gen.
    induction brs; simpl; auto. lia.
  Qed.

  (** Needs well-founded recursion on the depth of terms as we should reduce 
      strings of applications in one go. *)
  Equations? rho (Γ : context) (t : term) : term by wf (depth t) := 
  rho Γ (tApp t u) with view_lambda_fix_app t u := 
    { | fix_lambda_app_lambda na T b [] u' := 
        (rho (vass na (rho Γ T) :: Γ) b) {0 := rho Γ u'};
      | fix_lambda_app_lambda na T b (a :: l) u' :=
        mkApps ((rho (vass na (rho Γ T) :: Γ) b) {0 := rho Γ a})
          (map_terms rho Γ (l ++ [u']) _);
      | fix_lambda_app_fix mfix idx l a :=
        let mfixctx := fold_fix_context_wf mfix (fun Γ x Hx => rho Γ x) Γ [] in 
        let mfix' := map_fix_rho (t:=tFix mfix idx) (fun Γ x Hx => rho Γ x) Γ mfixctx mfix _ in
        let args := map_terms rho Γ (l ++ [a]) _ in
        match unfold_fix mfix' idx with 
        | Some (rarg, fn) =>
          if is_constructor rarg (l ++ [a]) then
            mkApps fn args
          else mkApps (tFix mfix' idx) args
        | None => mkApps (tFix mfix' idx) args
        end ;
      | fix_lambda_app_other t' u' nisfixlam := tApp (rho Γ t') (rho Γ u') } ; 
  rho Γ (tLetIn na d t b) => (subst10 (rho Γ d) (rho (vdef na (rho Γ d) (rho Γ t) :: Γ) b)); 
  rho Γ (tRel i) with option_map decl_body (nth_error Γ i) := { 
    | Some (Some body) => (lift0 (S i) body); 
    | Some None => tRel i; 
    | None => tRel i }; 

  rho Γ (tCase ci p x brs) with inspect (decompose_app x) :=
  { | exist (f, args) eqx with view_construct_cofix f := 
  { | construct_cofix_construct ind' c u with eq_inductive ci.(ci_ind) ind' := 
    { | true with inspect (nth_error brs c) => 
        { | exist (Some br) eqbr =>
            if eqb #|skipn (ci_npar ci) args| 
              (context_assumptions (bcontext br)) then
              let p' := rho_predicate_wf rho Γ p _ in 
              let args' := map_terms rho Γ args _ in 
              rho_iota_red_wf rho Γ p' ci.(ci_npar) args' br _
            else 
              let p' := rho_predicate_wf rho Γ p _ in 
              let brs' := map_brs_wf rho Γ p' brs _ in
              let x' := rho Γ x in
              tCase ci p' x' brs';
          | exist None eqbr => 
            let p' := rho_predicate_wf rho Γ p _ in 
            let brs' := map_brs_wf rho Γ p' brs _ in
            let x' := rho Γ x in
            tCase ci p' x' brs' };
      | false => 
        let p' := rho_predicate_wf rho Γ p _ in 
        let x' := rho Γ x in 
        let brs' := map_brs_wf rho Γ p' brs _ in 
        tCase ci p' x' brs' }; 
    | construct_cofix_cofix mfix idx :=
      let p' := rho_predicate_wf rho Γ p _ in 
      let args' := map_terms rho Γ args _ in 
      let brs' := map_brs_wf rho Γ p' brs _ in 
      let mfixctx := fold_fix_context_wf mfix (fun Γ x Hx => rho Γ x) Γ [] in 
      let mfix' := map_fix_rho (t:=tCase ci p x brs) rho Γ mfixctx mfix _ in
        match nth_error mfix' idx with
        | Some d =>
          tCase ci p' (mkApps (subst0 (cofix_subst mfix') (dbody d)) args') brs'
        | None => tCase ci p' (rho Γ x) brs'
        end; 
    | construct_cofix_other t nconscof => 
      let p' := rho_predicate_wf rho Γ p _ in 
      let x' := rho Γ x in 
      let brs' := map_brs_wf rho Γ p' brs _ in 
        tCase ci p' x' brs' } };

  rho Γ (tProj (i, pars, narg) x) with inspect (decompose_app x) := {
    | exist (f, args) eqx with view_construct0_cofix f :=
    | construct0_cofix_construct ind u with inspect (nth_error (map_terms rho Γ args _) (pars + narg)) := { 
      | exist (Some arg1) eq => 
        if eq_inductive i ind then arg1
        else tProj (i, pars, narg) (rho Γ x);
      | exist None neq => tProj (i, pars, narg) (rho Γ x) }; 
    | construct0_cofix_cofix mfix idx := 
      let args' := map_terms rho Γ args _ in
      let mfixctx := fold_fix_context_wf mfix (fun Γ x Hx => rho Γ x) Γ [] in 
      let mfix' := map_fix_rho (t:=tProj (i, pars, narg) x) rho Γ mfixctx mfix _ in
      match nth_error mfix' idx with
      | Some d => tProj (i, pars, narg) (mkApps (subst0 (cofix_subst mfix') (dbody d)) args')
      | None =>  tProj (i, pars, narg) (rho Γ x)
      end;
    | construct0_cofix_other t nconscof => tProj (i, pars, narg) (rho Γ x) } ;
  rho Γ (tConst c u) with lookup_env Σ c := { 
    | Some (ConstantDecl decl) with decl.(cst_body) := { 
      | Some body => subst_instance u body; 
      | None => tConst c u }; 
    | _ => tConst c u }; 
  rho Γ (tLambda na t u) => tLambda na (rho Γ t) (rho (vass na (rho Γ t) :: Γ) u); 
  rho Γ (tProd na t u) => tProd na (rho Γ t) (rho (vass na (rho Γ t) :: Γ) u); 
  rho Γ (tVar i) => tVar i; 
  rho Γ (tEvar n l) => tEvar n (map_terms rho Γ l _); 
  rho Γ (tSort s) => tSort s; 
  rho Γ (tFix mfix idx) => 
    let mfixctx := fold_fix_context_wf mfix (fun Γ x Hx => rho Γ x) Γ [] in 
    tFix (map_fix_rho (t:=tFix mfix idx) (fun Γ x Hx => rho Γ x) Γ mfixctx mfix _) idx; 
  rho Γ (tCoFix mfix idx) => 
    let mfixctx := fold_fix_context_wf mfix (fun Γ x Hx => rho Γ x) Γ [] in 
    tCoFix (map_fix_rho (t:=tCoFix mfix idx) rho Γ mfixctx mfix _) idx; 
  rho Γ x => x.
  Proof.
    all:try abstract lia.
    Ltac d := 
      match goal with
      |- context [depth (mkApps ?f ?l)] =>
        move: (depth_mkApps f l); cbn -[Nat.max]; try lia
      end.
    Ltac invd :=
      match goal with
      [ H : decompose_app ?x = _ |- _ ] => 
        eapply decompose_app_inv in H; subst x
      end.
    all:try abstract (rewrite ?list_depth_app; d).
    all:try solve [clear -eqx; abstract (invd; d)].
    all:try solve [clear; move:(bbody_branch_depth brs p); lia].
    - clear -eqbr.
      abstract (eapply (nth_error_depth (branch_depth_gen depth p)) in eqbr;
      unfold branch_depth_gen in eqbr |- *; lia).
    - clear -eqx Hx. abstract (invd; d).
    - clear -eqx Hx. abstract (invd; d).
  Defined.

  Notation rho_predicate := (rho_predicate_gen rho).
  Notation rho_br := (map_br_gen rho).
  Notation rho_ctx_over Γ :=
    (fold_context (fun Δ => map_decl (rho (Γ ,,, Δ)))).
  Notation rho_ctx := (fold_context_term rho).
  Notation rho_iota_red := (rho_iota_red_gen rho).

  Lemma rho_ctx_over_length Δ Γ : #|rho_ctx_over Δ Γ| = #|Γ|.
  Proof.
    now len.
  Qed.

  Definition rho_fix_context Γ mfix :=
    fold_fix_context rho Γ [] mfix.

  Lemma rho_fix_context_length Γ mfix : #|rho_fix_context Γ mfix| = #|mfix|.
  Proof. now rewrite fold_fix_context_length Nat.add_0_r. Qed.

  (* Lemma map_terms_map t Γ l H : @map_terms t (fun Γ x Hx => rho Γ x) Γ l H = map (rho Γ) l. 
  Proof. 
    unfold map_terms. now rewrite map_In_spec.
  Qed. 
  Hint Rewrite map_terms_map : rho. *)

  (* Lemma map_brs_map t Γ l H : 
    @map_brs t (fun Γ x Hx => rho Γ x) Γ l H = map (fun x => (x.1, rho Γ x.2)) l. 
  Proof. 
    unfold map_brs. now rewrite map_In_spec.
  Qed. 
  Hint Rewrite map_brs_map : rho. *)

  Definition map_fix (rho : context -> term -> term) Γ mfixctx (mfix : mfixpoint term) :=
    (map (map_def (rho Γ) (rho (Γ ,,, mfixctx))) mfix).

  Lemma map_fix_rho_map t Γ mfix ctx H : 
    @map_fix_rho t (fun Γ x Hx => rho Γ x) Γ ctx mfix H = 
    map_fix rho Γ ctx mfix.
  Proof. 
    unfold map_fix_rho. now rewrite map_In_spec.
  Qed.

  Lemma fold_fix_context_wf_fold mfix Γ ctx :
    fold_fix_context_wf mfix (fun Γ x _ => rho Γ x) Γ ctx = 
    fold_fix_context rho Γ ctx mfix.
  Proof.
    induction mfix in ctx |- *; simpl; auto. 
  Qed.

  Hint Rewrite map_fix_rho_map fold_fix_context_wf_fold : rho.

  Lemma mkApps_tApp f a l : mkApps (tApp f a) l = mkApps f (a :: l).
  Proof. reflexivity. Qed.

  Lemma tApp_mkApps f a : tApp f a = mkApps f [a].
  Proof. reflexivity. Qed.

  Lemma isFixLambda_app_mkApps t l : isFixLambda_app t -> isFixLambda_app (mkApps t l).
  Proof. 
    induction l using rev_ind; simpl; auto.
    rewrite -mkApps_nested. 
    intros isf. specialize (IHl isf).
    simpl. rewrite IHl. destruct (mkApps t l); auto.
  Qed.

  Definition isFixLambda (t : term) : bool :=
    match t with
    | tFix _ _ => true
    | tLambda _ _ _ => true
    | _ => false
    end.

  Inductive fix_lambda_view : term -> Type :=
  | fix_lambda_lambda na b t : fix_lambda_view (tLambda na b t)
  | fix_lambda_fix mfix i : fix_lambda_view (tFix mfix i)
  | fix_lambda_other t : ~~ isFixLambda t -> fix_lambda_view t.

  Lemma view_fix_lambda (t : term) : fix_lambda_view t.
  Proof.
    destruct t; repeat constructor.
  Qed.
  
  Lemma isFixLambda_app_mkApps' t l x : isFixLambda t -> isFixLambda_app (tApp (mkApps t l) x).
  Proof. 
    induction l using rev_ind; simpl; auto.
    destruct t; auto. simpl => //.
    intros isl. specialize (IHl isl).
    simpl in IHl.
    now rewrite -mkApps_nested /=. 
  Qed.

  Ltac discr_mkApps H := 
    let Hf := fresh in let Hargs := fresh in
    rewrite ?tApp_mkApps ?mkApps_nested in H;
      (eapply mkApps_nApp_inj in H as [Hf Hargs] ||
        eapply (mkApps_nApp_inj _ _ []) in H as [Hf Hargs] ||
        eapply (mkApps_nApp_inj _ _ _ []) in H as [Hf Hargs]);
        [noconf Hf|reflexivity].

  Set Equations With UIP. (* This allows to use decidable equality on terms. *)

  (* Most of this is discrimination, we should have a more robust tactic to  
    solve this. *)
  Lemma rho_app_lambda Γ na ty b a l :
    rho Γ (mkApps (tApp (tLambda na ty b) a) l) =  
    mkApps ((rho (vass na (rho Γ ty) :: Γ) b) {0 := rho Γ a}) (map (rho Γ) l).
  Proof.
    induction l using rev_ind; autorewrite with rho.
    - simpl. reflexivity.
    - simpl. rewrite -mkApps_nested. autorewrite with rho.
      change (mkApps (tApp (tLambda na ty b) a) l) with
        (mkApps (tLambda na ty b) (a :: l)).
      now simp rho.
  Qed.
  
  Lemma bool_pirr (b b' : bool) (p q : b = b') : p = q.
  Proof. noconf p. now noconf q. Qed.

  Lemma view_lambda_fix_app_other t u (H : ~~ isFixLambda_app (tApp t u)) :
    view_lambda_fix_app t u = fix_lambda_app_other t u H.
  Proof.
    induction t; simpl; f_equal; try apply bool_pirr.
    simpl in H => //.
    specialize (IHt1 H).
    rewrite IHt1. destruct t1; auto.
    simpl in H => //.
  Qed.

  Lemma rho_app_lambda' Γ na ty b l :
    rho Γ (mkApps (tLambda na ty b) l) =
    match l with 
    | [] => rho Γ (tLambda na ty b)
    | a :: l => 
      mkApps ((rho (vass na (rho Γ ty) :: Γ) b) {0 := rho Γ a}) (map (rho Γ) l)
    end.
  Proof.
    destruct l using rev_case; autorewrite with rho; auto.
    simpl. rewrite -mkApps_nested. simp rho.
    destruct l; simpl; auto. now simp rho.
  Qed.

  Lemma rho_app_construct Γ c u i l :
    rho Γ (mkApps (tConstruct c u i) l) =
    mkApps (tConstruct c u i) (map (rho Γ) l).
  Proof.
    induction l using rev_ind; autorewrite with rho; auto.
    simpl. rewrite -mkApps_nested. simp rho.
    unshelve erewrite view_lambda_fix_app_other. simpl.
    clear; induction l using rev_ind; simpl; auto. 
    rewrite -mkApps_nested. simpl. apply IHl.
    simp rho. rewrite IHl. now rewrite map_app -mkApps_nested.
  Qed.
  Hint Rewrite rho_app_construct : rho.

  Lemma rho_app_cofix Γ mfix idx l :
    rho Γ (mkApps (tCoFix mfix idx) l) =
    mkApps (tCoFix (map_fix rho Γ (rho_fix_context Γ mfix) mfix) idx) (map (rho Γ) l).
  Proof.
    induction l using rev_ind; autorewrite with rho; auto.
    simpl. now simp rho. rewrite -mkApps_nested. simp rho.
    unshelve erewrite view_lambda_fix_app_other. simpl.
    clear; induction l using rev_ind; simpl; auto. 
    rewrite -mkApps_nested. simpl. apply IHl.
    simp rho. rewrite IHl. now rewrite map_app -mkApps_nested.
  Qed.

  Hint Rewrite rho_app_cofix : rho.

  Lemma map_cofix_subst (f : context -> term -> term)
        (f' : context -> context -> term -> term) mfix Γ Γ' :
    (forall n, tCoFix (map (map_def (f Γ) (f' Γ Γ')) mfix) n = f Γ (tCoFix mfix n)) ->
    cofix_subst (map (map_def (f Γ) (f' Γ Γ')) mfix) =
    map (f Γ) (cofix_subst mfix).
  Proof.
    unfold cofix_subst. intros.
    rewrite map_length. generalize (#|mfix|). induction n. simpl. reflexivity.
    simpl. rewrite - IHn. f_equal. apply H.
  Qed.

  Lemma map_cofix_subst' f g mfix :
    (forall n, tCoFix (map (map_def f g) mfix) n = f (tCoFix mfix n)) ->
    cofix_subst (map (map_def f g) mfix) =
    map f (cofix_subst mfix).
  Proof.
    unfold cofix_subst. intros.
    rewrite map_length. generalize (#|mfix|) at 1 2. induction n. simpl. reflexivity.
    simpl. rewrite - IHn. f_equal. apply H.
  Qed.

  Lemma map_fix_subst f g mfix :
    (forall n, tFix (map (map_def f g) mfix) n = f (tFix mfix n)) ->
    fix_subst (map (map_def f g) mfix) =
    map f (fix_subst mfix).
  Proof.
    unfold fix_subst. intros.
    rewrite map_length. generalize (#|mfix|) at 1 2. induction n. simpl. reflexivity.
    simpl. rewrite - IHn. f_equal. apply H.
  Qed.

  Lemma rho_app_fix Γ mfix idx args :
    let rhoargs := map (rho Γ) args in
    rho Γ (mkApps (tFix mfix idx) args) = 
      match nth_error mfix idx with
      | Some d => 
        if is_constructor (rarg d) args then 
          let fn := (subst0 (map (rho Γ) (fix_subst mfix))) (rho (Γ ,,, fold_fix_context rho Γ [] mfix) (dbody d)) in
          mkApps fn rhoargs
        else mkApps (rho Γ (tFix mfix idx)) rhoargs
      | None => mkApps (rho Γ (tFix mfix idx)) rhoargs
      end.
  Proof.
    induction args using rev_ind; autorewrite with rho.
    - intros rhoargs.
      destruct nth_error as [d|] eqn:eqfix => //.
      rewrite /is_constructor nth_error_nil //.
    - simpl. rewrite map_app /=.
      destruct nth_error as [d|] eqn:eqfix => //.
      destruct (is_constructor (rarg d) (args ++ [x])) eqn:isc; simp rho.
      * rewrite -mkApps_nested /=.
        autorewrite with rho.
        simpl. simp rho. rewrite /unfold_fix.
        rewrite /map_fix nth_error_map eqfix /= isc map_fix_subst ?map_app //.
        intros n; simp rho. simpl. f_equal; now simp rho.
      * rewrite -mkApps_nested /=.
        simp rho. simpl. simp rho.
        now rewrite /unfold_fix /map_fix nth_error_map eqfix /= isc map_app.
      * rewrite -mkApps_nested /=. simp rho.
        simpl. simp rho.
        now  rewrite /unfold_fix /map_fix nth_error_map eqfix /= map_app.
  Qed.

  (* Helps factors proofs: only two cases to consider: the fixpoint unfolds or is stuck. *)
  Inductive rho_fix_spec Γ mfix i l : term -> Type :=
  | rho_fix_red d :
      let fn := (subst0 (map (rho Γ) (fix_subst mfix))) (rho (Γ ,,, rho_fix_context Γ mfix) (dbody d)) in
      nth_error mfix i = Some d ->
      is_constructor (rarg d) l ->
      rho_fix_spec Γ mfix i l (mkApps fn (map (rho Γ) l))
  | rho_fix_stuck :
      (match nth_error mfix i with
       | None => true
       | Some d => ~~ is_constructor (rarg d) l
       end) ->
      rho_fix_spec Γ mfix i l (mkApps (rho Γ (tFix mfix i)) (map (rho Γ) l)).

  Lemma rho_fix_elim Γ mfix i l :
    rho_fix_spec Γ mfix i l (rho Γ (mkApps (tFix mfix i) l)).
  Proof.
    rewrite rho_app_fix /= /unfold_fix.
    case e: nth_error => [d|] /=.
    case isc: is_constructor => /=.
    - eapply (rho_fix_red Γ mfix i l d) => //.
    - apply rho_fix_stuck.
      now rewrite e isc.
    - apply rho_fix_stuck. now rewrite e /=.
  Qed.

  Lemma rho_app_case Γ ci p x brs :
    rho Γ (tCase ci p x brs) =
    let (f, args) := decompose_app x in
    let p' := rho_predicate Γ p in
    match f with
    | tConstruct ind' c u => 
      if eq_inductive ci.(ci_ind) ind' then
        match nth_error brs c with
        | Some br => 
          if eqb #|skipn (ci_npar ci) args| (context_assumptions (bcontext br)) then
            let args' := map (rho Γ) args in 
            rho_iota_red Γ p' ci.(ci_npar) args' br
          else tCase ci p' (rho Γ x) (map (rho_br Γ p') brs)
        | None => tCase ci p' (rho Γ x) (map (rho_br Γ p') brs)
        end
      else tCase ci p' (rho Γ x) (map (rho_br Γ p') brs)
    | tCoFix mfix idx =>
      match nth_error mfix idx with
      | Some d => 
        let fn := (subst0 (map (rho Γ) (cofix_subst mfix))) (rho (Γ ,,, fold_fix_context rho Γ [] mfix) (dbody d)) in
        tCase ci (rho_predicate Γ p) (mkApps fn (map (rho Γ) args))
           (map (rho_br Γ p') brs)
      | None => tCase ci p' (rho Γ x) (map (rho_br Γ p') brs)
      end
    | _ => tCase ci p' (rho Γ x) (map (rho_br Γ p') brs)
    end.
  Proof.
    autorewrite with rho.
    set (app := inspect _).
    destruct app as [[f l] eqapp].
    rewrite {2}eqapp. autorewrite with rho.
    destruct view_construct_cofix; autorewrite with rho.
    destruct eq_inductive eqn:eqi; simp rho => //.
    destruct inspect as [[br|] eqnth]; cbv zeta; simp rho; rewrite eqnth //; cbv zeta; simp rho => //.
    simpl; now simp rho.
    cbv zeta. 
    simpl. autorewrite with rho. rewrite /map_fix nth_error_map.
    destruct nth_error => /=. f_equal.
    f_equal. rewrite (map_cofix_subst rho (fun x y => rho (x ,,, y))) //.
    intros. autorewrite with rho. simpl. now autorewrite with rho.
    reflexivity.
    simpl.
    autorewrite with rho.
    destruct t; simpl in d => //.
  Qed.

  Lemma rho_app_proj Γ ind pars arg x :
    rho Γ (tProj (ind, pars, arg) x) =
    let (f, args) := decompose_app x in
    match f with
    | tConstruct ind' 0 u => 
      if eq_inductive ind ind' then
        match nth_error args (pars + arg) with
        | Some arg1 => rho Γ arg1
        | None => tProj (ind, pars, arg) (rho Γ x)
        end
      else tProj (ind, pars, arg) (rho Γ x)
    | tCoFix mfix idx =>
      match nth_error mfix idx with
      | Some d => 
        let fn := (subst0 (map (rho Γ) (cofix_subst mfix))) (rho (Γ ,,, fold_fix_context rho Γ [] mfix) (dbody d)) in
        tProj (ind, pars, arg) (mkApps fn (map (rho Γ) args))
      | None => tProj (ind, pars, arg) (rho Γ x)
      end
    | _ => tProj (ind, pars, arg) (rho Γ x)
    end.
  Proof.
    autorewrite with rho.
    set (app := inspect _).
    destruct app as [[f l] eqapp].
    rewrite {2}eqapp. autorewrite with rho.
    destruct view_construct0_cofix; autorewrite with rho.
    destruct eq_inductive eqn:eqi; simp rho => //.
    set (arg' := inspect _). clearbody arg'.
    destruct arg' as [[arg'|] eqarg'];
    autorewrite with rho. rewrite eqi.
    simp rho in eqarg'. rewrite nth_error_map in eqarg'.
    destruct nth_error => //. now simpl in eqarg'.
    simp rho in eqarg'; rewrite nth_error_map in eqarg'.
    destruct nth_error => //.
    destruct inspect as [[arg'|] eqarg'] => //; simp rho.
    now rewrite eqi.
    simpl. autorewrite with rho.
    rewrite /map_fix nth_error_map.
    destruct nth_error eqn:nth => /= //.
    f_equal. f_equal. f_equal.
    rewrite (map_cofix_subst rho (fun x y => rho (x ,,, y))) //.
    intros. autorewrite with rho. simpl. now autorewrite with rho.
    simpl. eapply decompose_app_inv in eqapp.
    subst x. destruct t; simpl in d => //.
    now destruct n.
  Qed.

  Lemma fold_fix_context_rev_mapi {Γ l m} :
    fold_fix_context rho Γ l m =
    List.rev (mapi (fun (i : nat) (x : def term) =>
                    vass (dname x) ((lift0 (#|l| + i)) (rho Γ (dtype x)))) m) ++ l.
  Proof.
    unfold mapi.
    rewrite rev_mapi.
    induction m in l |- *. simpl. auto.
    intros. simpl. rewrite mapi_app. simpl.
    rewrite IHm. cbn.
    rewrite - app_assoc. simpl. rewrite List.rev_length.
    rewrite Nat.add_0_r. rewrite minus_diag. simpl.
    f_equal. apply mapi_ext_size. simpl; intros.
    rewrite List.rev_length in H.
    f_equal. f_equal. lia. f_equal. f_equal. f_equal. lia.
  Qed.

  Lemma fold_fix_context_rev {Γ m} :
    fold_fix_context rho Γ [] m =
    List.rev (mapi (fun (i : nat) (x : def term) =>
                    vass (dname x) (lift0 i (rho Γ (dtype x)))) m).
  Proof.
    pose proof (@fold_fix_context_rev_mapi Γ [] m).
    now rewrite app_nil_r in H.
  Qed.

  Lemma nth_error_map_fix i f Γ Δ m :
    nth_error (map_fix f Γ Δ m) i = option_map (map_def (f Γ) (f (Γ ,,, Δ))) (nth_error m i).
  Proof.
    now rewrite /map_fix nth_error_map.
  Qed.

  Lemma fold_fix_context_app Γ l acc acc' :
    fold_fix_context rho Γ l (acc ++ acc') =
    fold_fix_context rho Γ (fold_fix_context rho Γ l acc) acc'.
  Proof.
    induction acc in l, acc' |- *. simpl. auto.
    simpl. rewrite IHacc. reflexivity.
  Qed.

  Section All2i.
    (** A special notion of All2 just for this proof *)

    Hint Constructors All2i : pcuic.

    Inductive All2i_ctx {A B : Type} (R : nat -> A -> B -> Type) : list A -> list B -> Type :=
      All2i_ctx_nil : All2i_ctx R [] []
    | All2i_ctx_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
            R (List.length l) x y -> All2i_ctx R l l' -> All2i_ctx R (x :: l) (y :: l').
    Hint Constructors All2i_ctx : core pcuic.

    Lemma All2i_ctx_app {A B} (P : nat -> A -> B -> Type) l0 l0' l1 l1' :
      All2i_ctx P l0' l1' ->
      All2i_ctx (fun n => P (n + #|l0'|)) l0 l1 ->
      All2i_ctx P (l0 ++ l0') (l1 ++ l1').
    Proof.
      intros H. induction 1; simpl. apply H.
      constructor. now rewrite app_length. apply IHX.
    Qed.

    Lemma All2i_ctx_length {A B} (P : nat -> A -> B -> Type) l l' :
      All2i_ctx P l l' -> #|l| = #|l'|.
    Proof. induction 1; simpl; lia. Qed.

    Lemma All2i_ctx_impl {A B} (P Q : nat -> A -> B -> Type) l l' :
      All2i_ctx P l l' -> (forall n x y, P n x y -> Q n x y) -> All2i_ctx Q l l'.
    Proof. induction 1; simpl; auto. Qed.

    Lemma All2i_ctx_rev {A B} (P : nat -> A -> B -> Type) l l' :
      All2i_ctx P l l' ->
      All2i_ctx (fun n => P (#|l| - S n)) (List.rev l) (List.rev l').
    Proof.
      induction 1. constructor. simpl List.rev.
      apply All2i_ctx_app. repeat constructor. simpl. rewrite Nat.sub_0_r. auto.
      simpl. eapply All2i_ctx_impl; eauto. intros. simpl in X0. now rewrite Nat.add_1_r.
    Qed.
    
    Lemma All2i_rev_ctx {A B} (R : nat -> A -> B -> Type) (n : nat) (l : list A) (l' : list B) :
      All2i_ctx R l l' -> All2i R 0 (List.rev l) (List.rev l').
    Proof.
      induction 1. simpl. constructor.
      simpl. apply All2i_app => //. simpl. rewrite List.rev_length. pcuic.
    Qed.

    Lemma All2i_rev_ctx_gen {A B} (R : nat -> A -> B -> Type) (n : nat) (l : list A) (l' : list B) :
      All2i R n l l' -> All2i_ctx (fun m => R (n + m)) (List.rev l) (List.rev l').
    Proof.
      induction 1. simpl. constructor.
      simpl. eapply All2i_ctx_app. constructor. now rewrite Nat.add_0_r. constructor.
      eapply All2i_ctx_impl; eauto. intros.
      simpl in *. rewrite [S _]Nat.add_succ_comm in X0. now rewrite Nat.add_1_r.
    Qed.

    Lemma All2i_rev_ctx_inv {A B} (R : nat -> A -> B -> Type) (l : list A) (l' : list B) :
      All2i R 0 l l' -> All2i_ctx R (List.rev l) (List.rev l').
    Proof.
      intros. eapply All2i_rev_ctx_gen in X. simpl in X. apply X.
    Qed.

    Lemma All2i_mapi_rec {A B C D} (R : nat -> A -> B -> Type)
          (l : list C) (l' : list D) (f : nat -> C -> A) (g : nat -> D -> B) n :
      All2i (fun n x y => R n (f n x) (g n y)) n l l' ->
      All2i R n (mapi_rec f l n) (mapi_rec g l' n).
    Proof.
      induction 1; constructor; auto.
    Qed.

    Lemma All2i_trivial {A B} (R : nat -> A -> B -> Type) (H : forall n x y, R n x y) n l l' :
      #|l| = #|l'| -> All2i R n l l'.
    Proof.
      induction l in n, l' |- *; destruct l'; simpl; try discriminate; intros; constructor; auto.
    Qed.
  End All2i.

  Definition pres_bodies Γ Δ σ :=
    All2i_ctx
     (fun n decl decl' => (decl_body decl' = option_map (fun x => x.[⇑^n σ]) (decl_body decl)))
     Γ Δ.

  Lemma pres_bodies_inst_context Γ σ : pres_bodies Γ (inst_context σ Γ) σ.
  Proof.
    red; induction Γ. constructor.
    rewrite inst_context_snoc. constructor. simpl. reflexivity.
    apply IHΓ.
  Qed.
  Hint Resolve pres_bodies_inst_context : pcuic.
      
  Definition ctxmap (Γ Δ : context) (s : nat -> term) :=
    forall x d, nth_error Γ x = Some d ->
                match decl_body d return Type with
                | Some b =>
                  ∑ i b', s x = tRel i /\
                          option_map decl_body (nth_error Δ i) = Some (Some b') /\
                          b'.[↑^(S i)] = b.[↑^(S x) ∘s s]
                | None => True
                end.

  Lemma All2_prop2_eq_split (Γ Γ' Γ2 Γ2' : context) (A B : Type) (f g : A -> term)
        (h : A -> B) (rel : context -> context -> term -> term -> Type) x y :
    All2_prop2_eq Γ Γ' Γ2 Γ2' f g h rel x y ->
    All2 (on_Trel (rel Γ Γ') f) x y *
    All2 (on_Trel (rel Γ2 Γ2') g) x y *
    All2 (on_Trel eq h) x y.
  Proof.
    induction 1; intuition.
  Qed.

  Lemma refine_pred Γ Δ t u u' : u = u' -> pred1 Σ Γ Δ t u' -> pred1 Σ Γ Δ t u.
  Proof. now intros ->. Qed.

  Lemma ctxmap_ext Γ Δ : CMorphisms.Proper (CMorphisms.respectful (pointwise_relation _ eq) iffT) (ctxmap Γ Δ).
  Proof.
    red. red. intros.
    split; intros X.
    - intros n d Hn. specialize (X n d Hn).
      destruct d as [na [b|] ty]; simpl in *; auto.
      destruct X as [i [b' [? ?]]]. exists i, b'.
      rewrite -H. split; auto.
    - intros n d Hn. specialize (X n d Hn).
      destruct d as [na [b|] ty]; simpl in *; auto.
      destruct X as [i [b' [? ?]]]. exists i, b'.
      rewrite H. split; auto.
  Qed.

  Lemma Up_ctxmap Γ Δ c c' σ :
    ctxmap Γ Δ σ ->
    (decl_body c' = option_map (fun x => x.[σ]) (decl_body c)) ->
    ctxmap (Γ ,, c) (Δ ,, c') (⇑ σ).
  Proof.
    intros.
    intros x d Hnth.
    destruct x; simpl in *; noconf Hnth.
    destruct c as [na [b|] ty]; simpl; auto.
    exists 0. eexists. repeat split; eauto. simpl in H. simpl. now rewrite H.
    now autorewrite with sigma.
    specialize (X _ _ Hnth). destruct decl_body; auto.
    destruct X as [i [b' [? [? ?]]]]; auto.
    exists (S i), b'. simpl. repeat split; auto.
    unfold subst_compose. now rewrite H0.
    autorewrite with sigma in H2 |- *.
    rewrite -subst_compose_assoc.
    rewrite -subst_compose_assoc.
    rewrite -subst_compose_assoc.
    rewrite -inst_assoc. rewrite H2.
    now autorewrite with sigma.
  Qed.

  Lemma Upn_ctxmap Γ Δ Γ' Δ' σ :
    pres_bodies Γ' Δ' σ ->
    ctxmap Γ Δ σ ->
    ctxmap (Γ ,,, Γ') (Δ ,,, Δ') (⇑^#|Γ'| σ).
  Proof.
    induction 1. simpl. intros.
    eapply ctxmap_ext. rewrite Upn_0. reflexivity. apply X.
    simpl. intros Hσ.
    eapply ctxmap_ext. now sigma.
    eapply Up_ctxmap; eauto.
  Qed.
  Hint Resolve Upn_ctxmap : pcuic.

  Lemma inst_ctxmap Γ Δ Γ' σ : 
    ctxmap Γ Δ σ ->
    ctxmap (Γ ,,, Γ') (Δ ,,, inst_context σ Γ') (⇑^#|Γ'| σ).
  Proof.
    intros cmap.
    apply Upn_ctxmap => //. 
    apply pres_bodies_inst_context.
  Qed.
  Hint Resolve inst_ctxmap : pcuic.

  Lemma inst_ctxmap_up Γ Δ Γ' σ : 
    ctxmap Γ Δ σ ->
    ctxmap (Γ ,,, Γ') (Δ ,,, inst_context σ Γ') (up #|Γ'| σ).
  Proof.
    intros cmap.
    eapply ctxmap_ext. rewrite up_Upn. reflexivity.
    now apply inst_ctxmap.
  Qed.
  Hint Resolve inst_ctxmap_up : pcuic.

  (** Untyped renamings *)
  Definition renaming Γ Δ r :=
    forall x, match nth_error Γ x with
              | Some d =>
                match decl_body d return Prop with
                | Some b =>
                  exists b', option_map decl_body (nth_error Δ (r x)) = Some (Some b') /\
                             b'.[↑^(S (r x))] = b.[↑^(S x) ∘s ren r]
                (* whose body is b substituted with the previous variables *)
                | None => option_map decl_body (nth_error Δ (r x)) = Some None
                end
              | None => nth_error Δ (r x) = None
              end.

  Instance renaming_ext Γ Δ : Morphisms.Proper (`=1` ==> iff)%signature (renaming Γ Δ).
  Proof.
    red. red. intros.
    split; intros.
    - intros n. specialize (H0 n).
      destruct nth_error; auto.
      destruct c as [na [b|] ty]; simpl in *; auto.
      destruct H0 as [b' [Heq Heq']]; auto. exists b'. rewrite -(H n).
      intuition auto. now rewrite Heq' H. now rewrite -H.
      now rewrite -H.
    - intros n. specialize (H0 n).
      destruct nth_error; auto.
      destruct c as [na [b|] ty]; simpl in *; auto.
      destruct H0 as [b' [Heq Heq']]; auto. exists b'. rewrite (H n).
      intuition auto. now rewrite Heq' H. now rewrite H.
      now rewrite H.
  Qed.

  Lemma shiftn1_renaming Γ Δ c c' r :
    renaming Γ Δ r ->
    (decl_body c' = option_map (fun x => x.[ren r]) (decl_body c)) ->
    renaming (c :: Γ) (c' :: Δ) (shiftn 1 r).
  Proof.
    intros.
    red.
    destruct x. simpl.
    destruct (decl_body c) eqn:Heq; rewrite H0; auto. eexists. simpl. split; eauto.
    sigma. rewrite -ren_shiftn. now sigma.

    simpl.
    rewrite Nat.sub_0_r. specialize (H x).
    destruct nth_error eqn:Heq.
    destruct c0 as [na [b|] ty]; cbn in *.
    destruct H as [b' [Hb Heq']].
    exists b'; intuition auto.
    rewrite -ren_shiftn. autorewrite with sigma in Heq' |- *.
    rewrite Nat.sub_0_r.
    rewrite -?subst_compose_assoc -inst_assoc.
    rewrite -[b.[_]]inst_assoc. rewrite Heq'.
    now sigma.
    auto. auto.
  Qed.
  
  Lemma shift_renaming Γ Δ ctx ctx' r :
    All2i_ctx (fun n decl decl' => (decl_body decl' = option_map (fun x => x.[ren (shiftn n r)]) (decl_body decl)))
          ctx ctx' ->
    renaming Γ Δ r ->
    renaming (Γ ,,, ctx) (Δ ,,, ctx') (shiftn #|ctx| r).
  Proof.
    induction 1.
    intros. rewrite shiftn0. apply H.
    intros. simpl.
    rewrite shiftnS. apply shiftn1_renaming. apply IHX; try lia. auto.
    apply r0.
  Qed.

  Lemma shiftn_renaming Γ Δ ctx r :
    renaming Γ Δ r ->
    renaming (Γ ,,, ctx) (Δ ,,, rename_context r ctx) (shiftn #|ctx| r).
  Proof.
    induction ctx; simpl; auto.
    * intros. rewrite shiftn0. apply H.
    * intros. simpl.
      rewrite shiftnS rename_context_snoc /=.
      apply shiftn1_renaming. now apply IHctx.
      simpl. destruct (decl_body a) => /= //.
      now sigma.
  Qed.

  Lemma shiftn_renaming_eq Γ Δ ctx r k :
    renaming Γ Δ r ->
    k = #|ctx| ->
    renaming (Γ ,,, ctx) (Δ ,,, rename_context r ctx) (shiftn k r).
  Proof.
    now intros hr ->; apply shiftn_renaming.
  Qed.

  Lemma renaming_shift_rho_fix_context:
    forall (mfix : mfixpoint term) (Γ Δ : list context_decl) (r : nat -> nat),
      renaming Γ Δ r ->
      renaming (Γ ,,, rho_fix_context Γ mfix)
               (Δ ,,, rho_fix_context Δ (map (map_def (rename r) (rename (shiftn #|mfix| r))) mfix))
               (shiftn #|mfix| r).
  Proof.
    intros mfix Γ Δ r Hr.
    rewrite -{2}(rho_fix_context_length Γ mfix).
    eapply shift_renaming; auto.
    rewrite /rho_fix_context !fold_fix_context_rev.
    apply All2i_rev_ctx_inv, All2i_mapi.
    simpl. apply All2i_trivial; auto. now rewrite map_length.
  Qed.
  
  Lemma map_fix_rho_rename:
    forall (mfix : mfixpoint term) (i : nat) (l : list term),
      (forall t' : term, depth t' < depth (mkApps (tFix mfix i) l)
                    -> forall (Γ Δ : list context_decl) (r : nat -> nat) (P : nat -> bool),
            renaming Γ Δ r ->
            on_free_vars P t' ->
            rename r (rho Γ t') = rho Δ (rename r t'))
      -> forall (Γ Δ : list context_decl) (r : nat -> nat) P n,
        renaming Γ Δ r ->
        on_free_vars P (tFix mfix n) ->
         map (map_def (rename r) (rename (shiftn #|mfix| r)))
              (map_fix rho Γ (fold_fix_context rho Γ [] mfix) mfix) =
          map_fix rho Δ (fold_fix_context rho Δ [] (map (map_def (rename r) (rename (shiftn #|mfix| r))) mfix))
                  (map (map_def (rename r) (rename (shiftn #|mfix| r))) mfix).
  Proof.
    intros mfix i l H Γ Δ r P H2 Hr onfix. inv_on_free_vars.
    rewrite /map_fix !map_map_compose !compose_map_def.
    apply map_ext_in => d hin.
    have hdepth := mfixpoint_depth_In hin.
    eapply All_In in onfix as []; tea.
    move/andP: H0 => [onty onbod].
    apply map_def_eq_spec.
    - specialize (H (dtype d)).
      forward H. move: (depth_mkApps (tFix mfix i) l). simpl. lia.
      now eapply H; tea.
    - specialize (H (dbody d)).
      forward H. move: (depth_mkApps (tFix mfix i) l). simpl. lia.
      eapply H. eapply renaming_shift_rho_fix_context; tea. tea.
  Qed.

  Lemma All_IH {A depth} (l : list A) k (P : A -> Type) :
    list_depth_gen depth l < k ->
    (forall x, depth x < k -> P x) -> 
    All P l.
  Proof.
    induction l in k |- *. constructor.
    simpl. intros Hk IH.
    constructor. apply IH. lia.
    eapply (IHl k). lia. intros x sx.
    apply IH. lia.
  Qed.

  Lemma All_IH' {A depth B depth'} (f : A -> B) (l : list A) k (P : B -> Type) :
    list_depth_gen depth l < k ->
    (forall x, depth' (f x) <= depth x) ->
    (forall x, depth' x < k -> P x) -> 
    All (fun x => P (f x)) l.
  Proof.
    induction l in k |- *. constructor.
    simpl. intros Hk Hs IH.
    constructor. apply IH. specialize (Hs a). lia.
    eapply (IHl k). lia. apply Hs.
    apply IH.
  Qed.

  Lemma isConstruct_app_rename r t :
    isConstruct_app t = isConstruct_app (rename r t).
  Proof.
    unfold isConstruct_app. unfold decompose_app. generalize (@nil term) at 1.
    change (@nil term) with (map (rename r) []). generalize (@nil term).
    induction t; simpl; auto.
    intros l l0. specialize (IHt1 (t2 :: l) (t2 :: l0)).
    now rewrite IHt1.
  Qed.

  Lemma is_constructor_rename x l r : is_constructor x l = is_constructor x (map (rename r) l).
  Proof.
    rewrite /is_constructor nth_error_map.
    elim: nth_error_spec => //.
    move=> n hnth xl /=.
    now apply isConstruct_app_rename.
  Qed.

  Lemma isFixLambda_app_rename r t : ~~ isFixLambda_app t -> ~~ isFixLambda_app (rename r t).
  Proof.
    induction t; simpl; auto.
    destruct t1; simpl in *; auto.
  Qed.

  Lemma construct_cofix_rename r t : discr_construct_cofix t -> discr_construct_cofix (rename r t).
  Proof.
    destruct t; simpl; try congruence.
  Qed.
  Transparent fold_context.

  Lemma fold_context_mapi_context f g Γ : 
    fold_context f (mapi_context g Γ) =
    fold_context (fun Γ => f Γ ∘ map_decl (g #|Γ|)) Γ.
  Proof.
    induction Γ. simpl. auto.
    simpl. f_equal; auto.
    now rewrite -IHΓ; len.
  Qed.

  Lemma mapi_context_fold_context f g Γ : 
    mapi_context f (fold_context (fun Γ => g (mapi_context f Γ)) Γ) =
    fold_context (fun Γ => map_decl (f #|Γ|) ∘ g Γ) Γ.
  Proof.
    induction Γ. simpl. auto.
    simpl. f_equal; auto. len.
    now rewrite -IHΓ.
  Qed.

  Lemma onctx_fold_context_term P Γ (f g : context -> term -> term) :
    onctx P Γ ->
    (forall Γ x, 
      onctx P Γ -> 
      fold_context_term f Γ = fold_context_term g Γ ->
      P x -> f (fold_context_term f Γ) x = g (fold_context_term g Γ) x) ->
    fold_context_term f Γ = fold_context_term g Γ.
  Proof.
    intros onc Hp. induction onc; simpl; auto.
    f_equal; auto.
    eapply map_decl_eq_spec; tea.
    intros. now apply Hp.
  Qed.

  Lemma rho_ctx_rename Γ r :
    fold_context_term (fun Γ' x => rho Γ' (rename (shiftn #|Γ'| r) x)) Γ =
    rho_ctx (rename_context r Γ).
  Proof.
    rewrite /rename_context.
    rewrite -mapi_context_fold.
    rewrite fold_context_mapi_context.
    now setoid_rewrite compose_map_decl.
  Qed.

  Lemma rename_rho_ctx {r ctx} :
    onctx
      (fun t : term =>
        forall (Γ Δ : list context_decl) (r : nat -> nat),
        renaming Γ Δ r -> rename r (rho Γ t) = rho Δ (rename r t))
      ctx ->
    rename_context r (rho_ctx ctx) =
    rho_ctx (rename_context r ctx).
  Proof.
    intros onc.
    rewrite /rename_context - !mapi_context_fold.
    induction onc; simpl; eauto.
    f_equal; eauto.
    rewrite !compose_map_decl.
    eapply map_decl_eq_spec; tea => /= t.
    intros IH.
    erewrite IH. rewrite -IHonc. len. reflexivity.
    rewrite mapi_context_fold.
    rewrite -/(rename_context r (rho_ctx l)).
    epose proof (shiftn_renaming [] [] (rho_ctx l) r).
    rewrite !app_context_nil_l in H. eapply H.
    now intros i; rewrite !nth_error_nil.
  Qed.

  Lemma ondecl_map (P : term -> Type) f (d : context_decl) : 
    ondecl P (map_decl f d) ->
    ondecl (fun x => P (f x)) d.
  Proof.
    destruct d => /=; rewrite /ondecl /=.
    destruct decl_body => /= //.
  Qed.

  (*
  Lemma rename_rho_ctx_over {ctx} {Γ Δ r n} :
    renaming Γ Δ r ->
    test_context_k (fun k : nat => on_free_vars (closedP k xpredT)) n ctx ->
    onctx
      (fun t : term =>
        forall (Γ Δ : list context_decl) (r : nat -> nat) P,
        renaming Γ Δ r -> on_free_vars P t -> rename r (rho Γ t) = rho Δ (rename r t))
      ctx ->
    rename_context r (rho_ctx_over Γ ctx) =
    rho_ctx_over Δ (rename_context r ctx).
  Proof.
    intros Hr clc onc.
    rewrite /rename_context - !mapi_context_fold.
    induction onc; simpl; eauto.
    move: clc => /= /andP [] clc clx.
    f_equal; eauto.
    rewrite !compose_map_decl.
    eapply map_decl_eqP_spec; tea => /= t.
    intros IH onfv.
    erewrite IH. rewrite -IHonc //. len. reflexivity.
    rewrite mapi_context_fold.
    rewrite -/(rename_context r (rho_ctx l)).
    apply (shiftn_renaming _ _ (rho_ctx_over Γ l) r Hr). tea.
  Qed. *)
  
  Lemma rename_rho_ctx_over {ctx} {Γ Δ r P p} :
    renaming Γ Δ r ->
    forallb (on_free_vars P) (pparams p) ->
    test_context_k (fun k : nat => on_free_vars (closedP k xpredT)) #|p.(pparams)| ctx ->
    onctx
      (fun t : term =>
        forall (Γ Δ : list context_decl) (r : nat -> nat) P,
        renaming Γ Δ r -> on_free_vars P t -> rename r (rho Γ t) = rho Δ (rename r t))
      (inst_case_context p.(pparams) p.(puinst) ctx) ->
    rename_context r (rho_ctx_over Γ (inst_case_context p.(pparams) p.(puinst) ctx)) =
    rho_ctx_over Δ (rename_context r (inst_case_context p.(pparams) p.(puinst) ctx)).
  Proof.
    rewrite /inst_case_context.
    intros Hr onpars clc onc.
    rewrite /rename_context - !mapi_context_fold.
    induction ctx; simpl; eauto.
    move: clc => /= /andP [] clc clx.
    specialize (IHctx clc).
    move: onc. rewrite /inst_case_context subst_instance_cons subst_context_snoc /= => onc.
    depelim onc.
    f_equal; eauto.
    rewrite !compose_map_decl.
    eapply ondecl_map in o.
    eapply ondecl_map in o.
    eapply map_decl_eqP_spec; tea => t.
    cbn; intros IH onfv.
    rewrite Nat.add_0_r; len. len in IH.
    erewrite <-IH => //. specialize (IHctx onc).
    rewrite -IHctx.
    rewrite mapi_context_fold.
    rewrite -/(rename_context _ _).
    relativize #|ctx|.
    apply (shiftn_renaming _ _ (rho_ctx_over Γ _) r Hr). now len.
    eapply on_free_vars_subst_gen.
    2:erewrite <- on_free_vars_subst_instance; tea.
    rewrite /on_free_vars_terms.
    solve_all.
  Qed.

  Lemma context_assumptions_fold_context_term f Γ : 
    context_assumptions (fold_context_term f Γ) = context_assumptions Γ.
  Proof.
    induction Γ => /= //.
    destruct (decl_body a) => /= //; f_equal => //.
  Qed.
  Hint Rewrite context_assumptions_fold_context_term : len.

  Lemma mapi_context_rename r Γ :
    mapi_context (fun k : nat => rename (shiftn k r)) Γ =
    rename_context r Γ.
  Proof. rewrite mapi_context_fold //. Qed.

  Lemma inspect_nth_error_rename {r brs u res} (eq : nth_error brs u = res) :
    ∑ prf,
      inspect (nth_error (rename_branches r brs) u) = 
      exist (option_map (rename_branch r) res) prf.
  Proof. simpl.
    rewrite nth_error_map eq. now exists eq_refl.
  Qed.

  Lemma pres_bodies_rename Γ Δ r ctx :
    renaming Γ Δ r ->
    All2i_ctx
      (fun (n : nat) (decl decl' : context_decl) =>
        decl_body decl' =
        option_map (fun x : term => x.[ren (shiftn n r)]) (decl_body decl))
      (rho_ctx_over Γ ctx)
      (rename_context r (rho_ctx_over Γ ctx)).
  Proof.
    intros Hr.
    induction ctx; simpl; auto.
    - constructor.
    - rewrite rename_context_snoc. constructor; auto.
      destruct a as [na [b|] ty] => /= //.
      f_equal. now sigma.
  Qed.
  
  Lemma pres_bodies_rename' Γ Δ r ctx :
    renaming Γ Δ r ->
    All2i_ctx
      (fun (n : nat) (decl decl' : context_decl) =>
        decl_body decl' =
        option_map (fun x : term => x.[ren (shiftn n r)]) (decl_body decl))
      ctx
      (rename_context r ctx).
  Proof.
    intros Hr.
    induction ctx; simpl; auto.
    - constructor.
    - rewrite rename_context_snoc. constructor; auto.
      destruct a as [na [b|] ty] => /= //.
      f_equal. now sigma.
  Qed.

  Lemma rho_rename_pred Γ Δ p r P :
    renaming Γ Δ r ->
    forallb (on_free_vars P) (pparams p) ->
    on_free_vars (shiftnP #|pcontext p| P) (preturn p) ->
    test_context_k (fun k : nat => PCUICOnFreeVars.on_free_vars (PCUICOnFreeVars.closedP k xpredT))
      #|pparams p| (pcontext p) ->
    CasePredProp_depth
      (fun t : term =>
      forall (Γ Δ : list context_decl) (r : nat -> nat) P,
      renaming Γ Δ r -> on_free_vars P t -> rename r (rho Γ t) = rho Δ (rename r t)) p ->
    rename_predicate r (rho_predicate Γ p) = rho_predicate Δ (rename_predicate r p).
  Proof.
    intros Hr onpars onret onp [? [? ?]].
    rewrite /rename_predicate /rho_predicate; cbn. f_equal. solve_all.
    eapply e. relativize #|pcontext p|; [eapply shift_renaming|]; tea; len => //.
    assert ((map (rho Δ) (map (rename r) (pparams p)) = map (rename r) (map (rho Γ) (pparams p)))).
    solve_all. erewrite b; trea.
    rewrite H.
    rewrite -rename_inst_case_context_wf //. len => //.
    (*erewrite <-(rename_rho_ctx_over Hr) => //; tea.*)
    rewrite /id. eapply pres_bodies_rename' => //; tea. tea.
  Qed.

  Lemma rename_rho_iota_red Γ Δ r p P pars args brs br c :
    renaming Γ Δ r ->
    #|skipn pars args| = context_assumptions br.(bcontext) ->
    forallb (on_free_vars P) (pparams p) ->
    closedn_ctx #|pparams p| br.(bcontext) ->
    on_free_vars (shiftnP #|bcontext br| P) (bbody br) ->
    test_context_k (fun k : nat => on_free_vars (closedP k xpredT)) #|pparams p| (bcontext br) ->
    CasePredProp_depth
    (fun t : term =>
    forall (Γ Δ : list context_decl) (r : nat -> nat) P,
    renaming Γ Δ r -> on_free_vars P t -> rename r (rho Γ t) = rho Δ (rename r t)) p ->
    CaseBrsProp_depth p
      (fun t : term =>
      forall (Γ Δ : list context_decl) (r : nat -> nat) P,
      renaming Γ Δ r -> on_free_vars P t -> rename r (rho Γ t) = rho Δ (rename r t)) brs ->
    nth_error brs c = Some br ->
    rename r (rho_iota_red Γ (rho_predicate Γ p) pars args br) =
    rho_iota_red Δ (rho_predicate Δ (rename_predicate r p)) pars (map (rename r) args) (rename_branch r br).
  Proof.
    intros Hr hlen hpars hlen' hbod hbr hpred hbrs hnth.
    unfold rho_iota_red.
    rewrite rename_subst0 map_rev map_skipn. f_equal.
    rewrite List.rev_length /expand_lets /expand_lets_k.
    rewrite rename_subst0. len.
    rewrite shiftn_add -hlen Nat.add_comm rename_shiftnk.
    rewrite hlen.
    relativize (context_assumptions _); [erewrite rename_extended_subst|now len].
    assert ((map (rho Δ) (map (rename r) (pparams p)) = map (rename r) (map (rho Γ) (pparams p)))).
    destruct hpred as [? _].
    solve_all. erewrite b; trea.
    f_equal. f_equal. rewrite /inst_case_branch_context /= /id.
    rewrite H.
    rewrite -rename_inst_case_context_wf // /id. len => //.
    eapply All_nth_error in hbrs as []; tea.
    f_equal.
    rewrite /inst_case_branch_context. cbn.
    erewrite e; trea.
    relativize #|bcontext br|; [eapply shift_renaming|]; tea; len => //.
    rewrite H -rename_inst_case_context_wf //. now len.
    rewrite /id. now eapply pres_bodies_rename'.
  Qed.

  Lemma rho_rename P Γ Δ r t :
    renaming Γ Δ r ->
    on_free_vars P t ->
    rename r (rho Γ t) = rho Δ (rename r t).
  Proof.
    revert t Γ Δ r P.
    refine (PCUICDepth.term_ind_depth_app _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      intros until Γ; intros Δ r P Hr ont; try subst Γ; try rename Γ0 into Γ; repeat inv_on_free_vars.
    all:auto 2.

    - red in Hr. simpl.
      specialize (Hr n).
      destruct (nth_error Γ n) as [c|] eqn:Heq.
      -- simp rho. rewrite Heq /=.
         destruct decl_body eqn:Heq''.
         simp rho. rewrite lift0_inst.
         destruct Hr as [b' [-> Hb']] => /=.
         rewrite lift0_inst.
         sigma. autorewrite with sigma in *. now rewrite <- Hb'.
         simpl.
         rewrite Hr. simpl. reflexivity.

      -- simp rho. rewrite Heq Hr //.

    - simpl; simp rho. simpl. f_equal; rewrite !map_map_compose. solve_all.

    - simpl; simp rho; simpl. erewrite H; eauto. f_equal.
      erewrite H0; eauto.
      simpl. eapply (shift_renaming _ _ [_] [_]). repeat constructor. auto.

    - simpl; simp rho; simpl. erewrite H; eauto.
      erewrite H0; eauto.
      simpl. eapply (shift_renaming _ _ [_] [_]). repeat constructor. auto.

    - simpl; simp rho; simpl. rewrite /subst1 subst_inst.
      specialize (H _ _ _ _ Hr p). specialize (H0 _ _ _ _ Hr p0).
      autorewrite with sigma in H, H0, H1.
      erewrite <- (H1 ((vdef n (rho Γ t) (rho Γ t0) :: Γ))).
      2:{ eapply (shift_renaming _ _ [_] [_]). repeat constructor. simpl.
          sigma. now rewrite -H. auto. }
      sigma. apply inst_ext. rewrite H.
      rewrite -ren_shiftn. sigma. unfold Up. now sigma. tea.

    - rewrite rho_equation_8.
      destruct (view_lambda_fix_app t u); try inv_on_free_vars.

      + (* Fixpoint application *)
        rename b into onfvb. rename a into onfvfix. rename a0 into a.
        simpl; simp rho. rewrite rename_mkApps. cbn [rename].
        assert (eqargs : map (rename r) (map (rho Γ) (l ++ [a])) =
                map (rho Δ) (map (rename r) (l ++ [a]))).
        { rewrite !map_map_compose !map_app. f_equal => /= //.
          2:{ f_equal. now eapply H1. }
          unshelve epose proof (All_IH l _ _ _ H); simpl; eauto.
          pose proof (depth_mkApps (tFix mfix i) l). lia. solve_all. }
        destruct (rho_fix_elim Γ mfix i (l ++ [a])).
        simpl. simp rho.
        rewrite /unfold_fix /map_fix nth_error_map e /= i0.
        simp rho; rewrite /map_fix !nth_error_map /= e /=.
        move: i0; rewrite /is_constructor -(map_app (rename r) l [a]) nth_error_map.
        destruct (nth_error_spec (l ++ [a]) (rarg d)) => /= //.
        rewrite -isConstruct_app_rename => -> //.
        rewrite rename_mkApps.
        f_equal; auto.
        assert (Hbod: forall (Γ Δ : list context_decl) (r : nat -> nat),
                   renaming Γ Δ r -> rename r (rho Γ (dbody d)) = rho Δ (rename r (dbody d))).
        { pose proof (H (dbody d)) as Hbod.
          forward Hbod.
          { simpl; move: (depth_mkApps (tFix mfix i) l). simpl.
            eapply mfixpoint_depth_nth_error in e. lia. }
          auto. intros. eapply Hbod; tea.
          inv_on_free_vars. eapply All_nth_error in onfvfix; tea.
          now move/andP: onfvfix. }
        assert (Hren : renaming (Γ ,,, rho_fix_context Γ mfix)
                           (Δ ,,, rho_fix_context Δ (map (map_def (rename r) (rename (shiftn #|mfix| r))) mfix))
                           (shiftn #|mfix| r)).
        now apply renaming_shift_rho_fix_context.
        specialize (Hbod _ _ _ Hren).
        rewrite -Hbod.
        rewrite !subst_inst.
        { sigma. eapply inst_ext.
          rewrite -{1}(rename_inst r).
          rewrite -ren_shiftn. sigma.
          rewrite Upn_comp ?map_length ?fix_subst_length ?map_length //.
          apply subst_consn_proper => //.
          rewrite map_fix_subst //.
          intros n. simp rho. simpl. simp rho.
          reflexivity.
          clear -H Hr Hren onfvfix.
          unfold fix_subst. autorewrite with len. generalize #|mfix| at 1 4.
          induction n; simpl; auto.
          rewrite IHn. clear IHn. f_equal; auto.
          specialize (H (tFix mfix n)) as Hbod.
          forward Hbod.
          { simpl. move: (depth_mkApps (tFix mfix i) l). simpl. lia. }
          simp rho. simpl. simp rho.
          specialize (Hbod _ _ _ _ Hr onfvfix).
          simpl in Hbod. simp rho in Hbod.
          simpl in Hbod; simp rho in Hbod.
          rewrite -rename_inst.
          rewrite ren_shiftn -(rename_inst (shiftn _ r)).
          rewrite Hbod. f_equal.
          rewrite /map_fix !map_map_compose. apply map_ext.
          intros []; unfold map_def; cbn. f_equal.
          f_equal. 2:rewrite -up_Upn ren_shiftn. 2:now sigma.
          f_equal. f_equal.
          apply map_ext => x. f_equal.
          now rewrite -up_Upn ren_shiftn; sigma. }

        simp rho; simpl; simp rho.
        rewrite /unfold_fix /map_fix !nth_error_map.
        destruct (nth_error mfix i) eqn:hfix => /=.
        assert(is_constructor (rarg d) (l ++ [a]) = false).
        red in i0; unfold negb in i0.
        destruct is_constructor; auto.
        rewrite H2.
        rewrite -(map_app (rename r) l [a]) -is_constructor_rename H2 //.
        rewrite rename_mkApps.
        f_equal. simpl. f_equal.
        autorewrite with len. 
        eapply (map_fix_rho_rename mfix i l); eauto.
        intros. eapply H; eauto. rewrite /=. lia.
        apply eqargs.
        rewrite rename_mkApps. f_equal; auto.
        2:{ now rewrite -(map_app (rename r) _ [_]). }
        simpl. f_equal. autorewrite with len.
        eapply (map_fix_rho_rename mfix i l); eauto.
        intros; eapply H; tea; simpl; try lia.

      + (* Lambda abstraction *)
        inv_on_free_vars. rename a0 into arg. rename b0 into body.
        pose proof (rho_app_lambda' Γ na ty body (l ++ [arg])).
        simp rho in H2. rewrite -mkApps_nested in H2.
        simpl in H2. simp rho in H2. rewrite {}H2.
        simpl. 
        rewrite rename_mkApps. simpl.
        rewrite tApp_mkApps mkApps_nested.
        rewrite -(map_app (rename r) _ [_]). 
        rewrite rho_app_lambda'.
        simpl.
        assert (All (fun x => rename r (rho Γ x) = rho Δ (rename r x)) (l ++ [arg])).
        { apply All_app_inv. 2:constructor; auto.
          unshelve epose proof (All_IH l _ _ _ H); simpl; eauto.
          move: (depth_mkApps (tLambda na ty body) l). lia. solve_all.
          eapply H1; tea. }
        remember (l ++ [arg]) as args.
        destruct args; simpl; simp rho.
        { apply (f_equal (@length _)) in Heqargs. simpl in Heqargs.
         autorewrite with len in Heqargs. simpl in Heqargs. lia. }
        rewrite rename_inst /subst1 subst_inst.
        simpl in H.
        specialize (H body).
        forward H.
        { move: (depth_mkApps (tLambda na ty body) l) => /=. lia. }
        rewrite inst_mkApps. 
        specialize (H (vass na (rho Γ ty) :: Γ) (vass na (rho Δ ty.[ren r]) :: Δ) (shiftn 1 r) (shiftnP 1 P)).
        forward H. eapply shiftn1_renaming; auto.
        sigma. depelim X.
        autorewrite with sigma in H, e, X.                
        f_equal.
        rewrite -H //. sigma. apply inst_ext.
        rewrite e.
        rewrite -ren_shiftn. sigma.
        unfold Up. now sigma.
        rewrite !map_map_compose. solve_all.
        now autorewrite with sigma in H.
      + simpl.
        simp rho. pose proof (isFixLambda_app_rename r _ i).
        simpl in H2. rewrite (view_lambda_fix_app_other (rename r t) (rename r a0) H2). simpl.
        erewrite H0, H1; eauto.

    - (* Constant unfolding *)
      simpl; simp rho; simpl.
      case e: lookup_env => [[decl|decl]|] //; simp rho.
      case eb: cst_body => [b|] //; simp rho.
      rewrite rename_inst inst_closed0 //.
      apply declared_decl_closed in e => //.
      hnf in e. rewrite eb in e. rewrite closedn_subst_instance; auto.
      now move/andP: e => [-> _].

    - (* construct/cofix iota reduction *)
      simpl; simp rho.
      destruct inspect as [[f a] decapp].
      destruct inspect as [[f' a'] decapp'].
      epose proof (decompose_app_rename decapp).
      rewrite -> decapp' in H0. noconf H0.
      simpl.
      assert (map (rename_branch r) (map (rho_br Γ (rho_predicate Γ p)) brs) =
              (map (rho_br Δ (rho_predicate Δ (rename_predicate r p))) (map (rename_branch r) brs))).
      { destruct X as [? [? ?]]; red in X0.
        simpl in *. rewrite !map_map_compose /rename_branch 
          /PCUICSigmaCalculus.rename_branch /rho_br /=. 
        simpl. solve_all. f_equal.
        rewrite /inst_case_branch_context /=.
        eapply All_prod_inv in p0 as [].
        unshelve epose proof (rename_rho_ctx_over Hr _ _ a2). shelve. solve_all. solve_all.
        erewrite b0. reflexivity.
        assert (map (rho Δ) (map (rename r) (pparams p)) = (map (rename r) (map (rho Γ) ((pparams p))))).
        solve_all. erewrite a0; trea. rewrite H3.
        rewrite - rename_inst_case_context_wf //.
        len => //.
        eapply shiftn_renaming_eq => //. now len. tea. }

      simpl.
      destruct X as [? [? ?]]; cbn in *. red in X0.
      destruct view_construct_cofix; simpl; simp rho.

      * destruct (eq_inductive ci ind) eqn:eqi.
        simp rho.
        destruct inspect as [[br|] eqbr]=> //; simp rho;
        destruct (inspect_nth_error_rename (r:=r) eqbr) as [prf ->]; simp rho.
        cbv zeta. simp rho.
        cbn -[eqb]. autorewrite with len.
        case: eqb_spec => // hlen.
        + erewrite rename_rho_iota_red; tea => //.
          f_equal.
          pose proof (decompose_app_inv decapp). subst t.
          specialize (H _ _ _ _ Hr p3).
          rewrite /= !rho_app_construct /= !rename_mkApps in H.
          simpl in H. rewrite rho_app_construct in H.
          apply mkApps_eq_inj in H as [_ Heq] => //.
          now rewrite skipn_map_length.
          { cbn. len. eapply nth_error_forallb in p4; tea.
            move: p4 => /= /andP[]. rewrite test_context_k_closed_on_free_vars_ctx.
            now rewrite closedn_ctx_on_free_vars. }
          eapply nth_error_forallb in p4; tea. cbn in p4.
          now move/andP: p4.
          eapply nth_error_forallb in p4; tea. cbn in p4.
          now move/andP: p4.
        + simp rho. simpl. f_equal; auto.
          erewrite -> rho_rename_pred; tea => //.
          erewrite H; trea.
        + simp rho. simpl. f_equal; eauto.
          erewrite -> rho_rename_pred; tea => //.
          simp rho.
        + simp rho. simpl. simp rho. f_equal; eauto.
          erewrite -> rho_rename_pred; tea => //.

      * simpl; simp rho.
        rewrite /map_fix !map_map_compose.
        rewrite /unfold_cofix !nth_error_map.
        apply decompose_app_inv in decapp. subst t.
        specialize (H _ _ _ _ Hr p3).
        simp rho in H; rewrite !rename_mkApps /= in H. simp rho in H.
        eapply mkApps_eq_inj in H as [Heqcof Heq] => //.
        noconf Heqcof. simpl in H.
        autorewrite with len in H.
        rewrite /map_fix !map_map_compose in H.

        case efix: (nth_error mfix idx) => [d|] /= //.
        + rewrite rename_mkApps !map_map_compose compose_map_def.
          f_equal. erewrite -> rho_rename_pred; tea => //.
          rewrite !map_map_compose in Heq.
          f_equal => //.
          rewrite !subst_inst. sigma.
          apply map_eq_inj in H.
          epose proof (nth_error_all efix H). cbn in H1.
          simpl in H1. apply (f_equal dbody) in H1.
          simpl in H1. rewrite -(rename_inst (shiftn _ r)) -(rename_inst r).
          rewrite -H1. sigma.
          apply inst_ext.
          rewrite -ren_shiftn. sigma.
          rewrite Upn_comp ?map_length ?fix_subst_length ?map_length //.
          apply subst_consn_proper => //.
          2:now autorewrite with len.
          rewrite map_cofix_subst' //. 
          intros n'; simp rho. simpl; f_equal. now simp rho.
          rewrite map_cofix_subst' //.
          simpl. move=> n'; f_equal. simp rho; simpl; simp rho.
          f_equal. rewrite /map_fix.
          rewrite !map_map_compose !compose_map_def.
          apply map_ext => x; apply map_def_eq_spec => //.
          rewrite !map_map_compose.
          unfold cofix_subst. generalize #|mfix|.
          clear -H.
          induction n; simpl; auto. f_equal; auto.
          simp rho. simpl. simp rho. f_equal.
          rewrite /map_fix !map_map_compose. autorewrite with len.
          solve_all.
          apply (f_equal dtype) in H. simpl in H.
          now sigma; sigma in H. sigma.
          rewrite -ren_shiftn. rewrite up_Upn.
          apply (f_equal dbody) in H. simpl in H.
          sigma in H. now rewrite <-ren_shiftn, up_Upn in H.
          now rewrite !map_map_compose in H0. 
          
        + rewrite map_map_compose. f_equal; auto.
          { erewrite -> rho_rename_pred; tea => //. }
          { simp rho. rewrite !rename_mkApps /= !map_map_compose !compose_map_def /=.
            simp rho. f_equal. f_equal.
            rewrite /map_fix map_map_compose. rewrite -H.
            autorewrite with len. reflexivity.
            now rewrite -Heq !map_map_compose. }
        now rewrite !map_map_compose in H0.
      * pose proof (construct_cofix_rename r t0 d).
        destruct (view_construct_cofix (rename r t0)); simpl in H1 => //.
        simp rho. simpl.
        f_equal; auto.
        erewrite rho_rename_pred; tea=> //.
        now rewrite !map_map_compose in H0. simp rho.

    - (* Proj construct/cofix reduction *)
      simpl; simp rho. destruct s as [[ind pars] n]. 
      rewrite !rho_app_proj.
      destruct decompose_app as [f a] eqn:decapp.
      erewrite (decompose_app_rename decapp).
      erewrite <-H; eauto.
      apply decompose_app_inv in decapp. subst t.
      specialize (H _ _ _ _ Hr ont).
      rewrite rename_mkApps in H.

      destruct f; simpl; auto.
      * destruct n0; simpl; auto.
        destruct eq_inductive eqn:eqi; simpl; auto.
        rewrite nth_error_map.
        destruct nth_error eqn:hnth; simpl; auto.
        simp rho in H. rewrite rename_mkApps in H.
        eapply mkApps_eq_inj in H as [_ Hargs] => //.
        rewrite !map_map_compose in Hargs.
        eapply map_eq_inj in Hargs.  
        apply (nth_error_all hnth Hargs).
      * rewrite nth_error_map.
        destruct nth_error eqn:hnth; auto.
        simpl. rewrite rename_mkApps.
        f_equal; auto.
        simpl in H; simp rho in H. rewrite rename_mkApps in H.
        eapply mkApps_eq_inj in H as [Hcof Hargs] => //.
        f_equal; auto. simpl in Hcof. noconf Hcof. simpl in H.
        noconf H.
        rewrite /map_fix !map_map_compose in H.
        apply map_eq_inj in H.
        epose proof (nth_error_all hnth H).
        simpl in H0. apply (f_equal dbody) in H0.
        simpl in H0. autorewrite with sigma in H0.
        rewrite !rename_inst -H0 - !rename_inst.
        sigma. autorewrite with len.
        apply inst_ext.
        rewrite -ren_shiftn. sigma.
        rewrite Upn_comp ?map_length ?fix_subst_length ?map_length //.
        apply subst_consn_proper => //.
        2:now autorewrite with len.
        rewrite map_cofix_subst' //. 
        intros n0. simpl. now rewrite up_Upn.
        rewrite !map_map_compose.
        unfold cofix_subst. generalize #|mfix|.
        clear -H.
        induction n; simpl; auto. f_equal; auto.
        simp rho. simpl. simp rho. f_equal.
        rewrite /map_fix !map_map_compose.  autorewrite with len.
        eapply All_map_eq, All_impl; tea => /= //.
        intros x.
        rewrite !rename_inst ren_shiftn => <-.
        apply map_def_eq_spec; simpl. now sigma. sigma. now len.

    - (* Fix *)
      simpl; simp rho; simpl; simp rho.
      f_equal. rewrite /map_fix !map_length !map_map_compose.
      red in X0. solve_all.
      move/andP: b => [] onty onbody.
      erewrite a0; tea; auto.
      move/andP: b => [] onty onbody.
      assert (#|m| = #|fold_fix_context rho Γ [] m|). rewrite fold_fix_context_length /= //.
      erewrite <-b0; trea.
      rewrite {2}H.
      eapply shift_renaming; auto.
      clear. generalize #|m|. induction m using rev_ind. simpl. constructor.
      intros. rewrite map_app !fold_fix_context_app. simpl. constructor. simpl. reflexivity. apply IHm.

    - (* CoFix *)
      simpl; simp rho; simpl; simp rho.
      f_equal. rewrite /map_fix !map_length !map_map_compose.
      red in X0. solve_all.
      move/andP: b => [] onty onbody.
      erewrite a0; tea; auto.
      move/andP: b => [] onty onbody.
      assert (#|m| = #|fold_fix_context rho Γ [] m|). rewrite fold_fix_context_length /= //.
      erewrite <-b0; trea.
      rewrite {2}H.
      eapply shift_renaming; auto.
      clear. generalize #|m|. induction m using rev_ind. simpl. constructor.
      intros. rewrite map_app !fold_fix_context_app. simpl. constructor. simpl. reflexivity. apply IHm.
  Qed.

  Lemma rho_lift0 Γ Δ P t : 
    on_free_vars P t ->
    lift0 #|Δ| (rho Γ t) = rho (Γ ,,, Δ) (lift0 #|Δ| t).
  Proof.
    rewrite !lift_rename. eapply rho_rename.
    red. intros x. destruct nth_error eqn:Heq.
    unfold lift_renaming. simpl. rewrite Nat.add_comm.
    rewrite nth_error_app_ge. lia. rewrite Nat.add_sub Heq.
    destruct c as [na [b|] ty]; simpl in *; auto.
    exists b. split; eauto.
    rewrite -ren_shiftk. rewrite shiftk_compose. reflexivity.
    unfold lift_renaming. simpl. rewrite Nat.add_comm.
    rewrite nth_error_app_ge. lia. now rewrite Nat.add_sub Heq.
  Qed.

  Lemma rho_ctx_over_app Γ' Γ Δ :
    rho_ctx_over Γ' (Γ ,,, Δ) =
    rho_ctx_over Γ' Γ ,,, rho_ctx_over (Γ' ,,, rho_ctx_over Γ' Γ) Δ.
  Proof.
    induction Δ; simpl; auto.
    destruct a as [na [b|] ty]. simpl. f_equal; auto.
    now rewrite IHΔ app_context_assoc.
    now rewrite IHΔ app_context_assoc.
  Qed.

  Lemma rho_ctx_app Γ Δ : rho_ctx (Γ ,,, Δ) = rho_ctx Γ ,,, rho_ctx_over (rho_ctx Γ) Δ.
  Proof.
    induction Δ; simpl; auto.
    destruct a as [na [b|] ty]; simpl; f_equal; auto.
    now rewrite -IHΔ.
    now rewrite -IHΔ.
  Qed.

  Lemma fold_fix_context_over_acc p Γ m acc :
    forallb (test_def (on_free_vars p) (on_free_vars (shiftnP #|m| p))) m ->
    rho_ctx_over (Γ ,,, acc)
      (List.rev (mapi_rec (fun (i : nat) (d : def term) => vass (dname d) ((lift0 i) (dtype d))) m #|acc|))
      ++ acc =
    fold_fix_context rho Γ acc m.
  Proof.
    generalize #|m| => n.
    induction m in Γ, acc |- *; simpl; auto.
    move/andP => [] ha hm.
    rewrite rho_ctx_over_app. simpl.
    unfold app_context. unfold app_context in IHm.
    erewrite <- IHm => //.
    rewrite - app_assoc. cbn. f_equal.
    apply fold_context_Proper. intros Δ d.
    apply map_decl_ext => x.
    rewrite (rho_lift0 _ _ p); auto. now move/andP: ha.
    repeat f_equal. rewrite (rho_lift0 _ _ p); auto.
    now move/andP: ha.
  Qed.

  Lemma fold_fix_context_rho_ctx p Γ m :
    forallb (test_def (on_free_vars p) (on_free_vars (shiftnP #|m| p))) m ->
    rho_ctx_over Γ (fix_context m) =
    fold_fix_context rho Γ [] m.
  Proof.
    intros hm.
    rewrite <- (fold_fix_context_over_acc p); now rewrite ?app_nil_r.
  Qed.

  Definition fold_fix_context_alt Γ m :=
    mapi (fun k def => vass def.(dname) (lift0 k (rho Γ def.(dtype)))) m.

  Lemma fix_context_fold p Γ m :
    forallb (test_def (on_free_vars p) (on_free_vars (shiftnP #|m| p))) m ->
    fix_context (map (map_def (rho Γ)
                              (rho (Γ ,,, rho_ctx_over Γ (fix_context m)))) m) =
    rho_ctx_over Γ (fix_context m).
  Proof.
    intros hm.
    unfold fix_context. rewrite mapi_map. simpl.
    rewrite (fold_fix_context_rho_ctx p); auto.
    rewrite fold_fix_context_rev_mapi. simpl.
    now rewrite app_nil_r.
  Qed.

  Lemma fix_context_map_fix p Γ mfix :
    forallb (test_def (on_free_vars p) (on_free_vars (shiftnP #|mfix| p))) mfix ->
    fix_context (map_fix rho Γ (rho_ctx_over Γ (fix_context mfix)) mfix) =
    rho_ctx_over Γ (fix_context mfix).
  Proof.
    intros hm. 
    rewrite - (fix_context_fold p) //.
    unfold map_fix. f_equal.
    f_equal. f_equal. rewrite (fix_context_fold p) //.
  Qed.

  Lemma rho_cofix_subst p Γ mfix :
    forallb (test_def (on_free_vars p) (on_free_vars (shiftnP #|mfix| p))) mfix ->
    cofix_subst (map_fix rho Γ (rho_ctx_over Γ (fix_context mfix)) mfix)
    = (map (rho Γ) (cofix_subst mfix)).
  Proof.
    intros hm.
    unfold cofix_subst. unfold map_fix at 2. rewrite !map_length.
    induction #|mfix| at 1 2. reflexivity. simpl. simp rho. simpl.
    simp rho. rewrite - (fold_fix_context_rho_ctx p) //. f_equal. apply IHn.
  Qed.

  Lemma rho_fix_subst p Γ mfix :
    forallb (test_def (on_free_vars p) (on_free_vars (shiftnP #|mfix| p))) mfix ->
    fix_subst (map_fix rho Γ (rho_ctx_over Γ (fix_context mfix)) mfix)
    = (map (rho Γ) (fix_subst mfix)).
  Proof.
    intros hm. unfold fix_subst. unfold map_fix at 2. rewrite !map_length.
    induction #|mfix| at 1 2. reflexivity. simpl. simp rho; simpl; simp rho.
    rewrite -(fold_fix_context_rho_ctx p) //. f_equal. apply IHn.
  Qed.

  Lemma nth_error_cofix_subst mfix n b :
    nth_error (cofix_subst mfix) n = Some b ->
    b = tCoFix mfix (#|mfix| - S n).
  Proof.
    unfold cofix_subst.
    generalize #|mfix|. induction n0 in n, b |- *. simpl.
    destruct n; simpl; congruence.
    destruct n; simpl. intros [= <-]. f_equal.
    destruct n0; simpl; try reflexivity.
    intros H. now specialize (IHn0 _ _ H).
  Qed.

  Lemma nth_error_fix_subst mfix n b :
    nth_error (fix_subst mfix) n = Some b ->
    b = tFix mfix (#|mfix| - S n).
  Proof.
    unfold fix_subst.
    generalize #|mfix|. induction n0 in n, b |- *. simpl.
    destruct n; simpl; congruence.
    destruct n; simpl. intros [= <-]. f_equal.
    destruct n0; simpl; try reflexivity.
    intros H. now specialize (IHn0 _ _ H).
  Qed.

  Lemma ctxmap_cofix_subst:
    forall (Γ' : context) (mfix1 : mfixpoint term),
      ctxmap (Γ' ,,, fix_context mfix1) Γ' (cofix_subst mfix1 ⋅n ids).
  Proof.
    intros Γ' mfix1.
    intros x d' Hnth.
    destruct (leb_spec_Set #|fix_context mfix1| x).
    rewrite nth_error_app_ge // in Hnth.
    rewrite fix_context_length in l Hnth.
    destruct d' as [na [b'|] ty]; simpl; auto.
    rewrite subst_consn_ge cofix_subst_length //.
    unfold ids. eexists _, _; split; eauto.
    rewrite Hnth. split; simpl; eauto.
    apply inst_ext.
    rewrite /subst_compose. simpl. intros v.
    rewrite subst_consn_ge ?cofix_subst_length. lia.
    unfold shiftk. f_equal. lia.
    rewrite nth_error_app_lt in Hnth => //.
    pose proof (fix_context_assumption_context mfix1).
    destruct d' as [na [b'|] ty]; simpl; auto.
    elimtype False. eapply nth_error_assumption_context in H; eauto.
    simpl in H; discriminate.
  Qed.

  Lemma ctxmap_fix_subst:
    forall (Γ' : context) (mfix1 : mfixpoint term),
      ctxmap (Γ' ,,, fix_context mfix1) Γ' (fix_subst mfix1 ⋅n ids).
  Proof.
    intros Γ' mfix1.
    intros x d' Hnth.
    destruct (leb_spec_Set #|fix_context mfix1| x).
    rewrite nth_error_app_ge // in Hnth.
    rewrite fix_context_length in l Hnth.
    destruct d' as [na [b'|] ty]; simpl; auto.
    rewrite subst_consn_ge fix_subst_length //.
    unfold ids. eexists _, _; split; eauto.
    rewrite Hnth. split; simpl; eauto.
    apply inst_ext.
    rewrite /subst_compose. simpl. intros v.
    rewrite subst_consn_ge ?fix_subst_length. lia.
    unfold shiftk. f_equal. lia.
    rewrite nth_error_app_lt in Hnth => //.
    pose proof (fix_context_assumption_context mfix1).
    destruct d' as [na [b'|] ty]; simpl; auto.
    elimtype False. eapply nth_error_assumption_context in H; eauto.
    simpl in H; discriminate.
  Qed.

  Lemma rho_triangle_All_All2_ind:
    forall (Γ : context) (brs : list (nat * term)),
    pred1_ctx Σ Γ (rho_ctx Γ) ->
    All (fun x => pred1_ctx Σ Γ (rho_ctx Γ) -> pred1 Σ Γ (rho_ctx Γ) (snd x) (rho (rho_ctx Γ) (snd x)))
        brs ->
    All2 (on_Trel_eq (pred1 Σ Γ (rho_ctx Γ)) snd fst) brs
         (map (fun x => (fst x, rho (rho_ctx Γ) (snd x))) brs).
  Proof.
    intros. rewrite - {1}(map_id brs). eapply All2_map, All_All2; eauto.
  Qed.

  Lemma rho_triangle_All_All2_ind_terms:
    forall (Γ Γ' Γ'0 : context) (args0 args1 : list term),
      pred1_ctx Σ Γ Γ' ->
      pred1_ctx Σ Γ' Γ'0 ->
      All2 (fun x y => 
        (pred1 Σ Γ Γ' x y * 
        ((on_ctx_free_vars xpredT Γ ->
          on_free_vars xpredT x ->
          forall Γ'0, pred1_ctx Σ Γ' Γ'0 ->
          pred1 Σ Γ' Γ'0 y (rho Γ'0 x))%type)))
        args0 args1 ->
      on_ctx_free_vars xpredT Γ ->
      forallb (on_free_vars xpredT) args0 ->
      All2 (pred1 Σ Γ' Γ'0) args1 (map (rho Γ'0) args0).
  Proof.
    intros. rewrite - {1}(map_id args1).
    solve_all.
    eapply All2_map_right, All2_sym, All2_impl; tea. solve_all. 
  Qed.

  (* Lemma rho_triangle_All_All2_ind_brs:
    forall (Γ Γ' : context) (brs0 brs1 : list (branch term)),
      pred1_ctx Σ Γ Γ' ->
      All2 (on_Trel_eq
       (fun x y => 
       (pred1 Σ Γ Γ' x y * pred1 Σ Γ' (rho_ctx Γ) y (rho (rho_ctx Γ) x))%type)
       bbody bcontext) brs0 brs1 ->
      All2 (on_Trel (pred1 Σ Γ' (rho_ctx Γ)) bbody) brs1 
        (map (fun x => (bcontext x, rho (rho_ctx Γ) (bbody x))) brs0).
  Proof.
    intros. rewrite - {1}(map_id brs1). eapply All2_map, All2_sym, All2_impl; pcuic.
  Qed. *)

  (*Lemma All2_fold_pred_fix_ctx p P (Γ Γ' Δ : context) (mfix0 : mfixpoint term) (mfix1 : list (def term)) :
    forallb (test_def (on_free_vars p) (on_free_vars (shiftnP #|mfix0| p))) mfix0 ->
     All2_fold
       (on_decls
          (on_decls_over (fun (Γ0 Γ'0 : context) (t t0 : term) => P Γ'0 (rho_ctx Γ0) t0 (rho (rho_ctx Γ0) t)) Γ Γ'))
       (fix_context mfix0) (fix_context mfix1)
     -> All2_fold (on_decls (on_decls_over P Γ' Δ) (fix_context mfix1)
                      (fix_context (map_fix rho Δ (rho_ctx_over Δ (fix_context mfix0)) mfix0)).
  Proof.
    intros.
    rewrite (fix_context_map_fix p) //.
    revert X. generalize (fix_context mfix0) (fix_context mfix1).
    induction 1; simpl; constructor; auto.
    depelim p0; constructor; simpl; auto;
    unfold on_decls_over in * |- *;  now rewrite -> rho_ctx_app in *.
  Qed.*)
  
   Lemma All2_fold_sym P Γ Γ' Δ Δ' :
    All2_fold (on_decls (on_decls_over (fun Γ Γ' t t' => P Γ' Γ t' t) Γ' Γ)) Δ' Δ ->
    All2_fold (on_decls (on_decls_over P Γ Γ')) Δ Δ'.
  Proof.
    induction 1; constructor; eauto. depelim p; constructor.
    all:now unfold on_decls_over in *.
  Qed.

  (*Lemma wf_rho_fix_subst Γ Γ' mfix0 mfix1 :
    #|mfix0| = #|mfix1| ->
    pred1_ctx Σ Γ' (rho_ctx Γ) ->
    All2_fold
      (on_decls
         (on_decls_over
            (fun (Γ Γ' : context) (t t0 : term) => pred1 Σ Γ' (rho_ctx Γ) t0 (rho (rho_ctx Γ) t)) Γ
            Γ')) (fix_context mfix0) (fix_context mfix1) ->
    All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1) dtype dbody
                  (fun x : def term => (dname x, rarg x))
                  (fun (Γ Γ' : context) (x y : term) => (pred1 Σ Γ Γ' x y *
                                                     pred1 Σ Γ' (rho_ctx Γ) y (rho (rho_ctx Γ) x))%type)
                  mfix0 mfix1 ->
    psubst Σ Γ' (rho_ctx Γ) (fix_subst mfix1) (map (rho (rho_ctx Γ)) (fix_subst mfix0))
           (fix_context mfix1) (rho_ctx_over (rho_ctx Γ) (fix_context mfix0)).
  Proof.
    intros Hlen Hred Hctxs a0. pose proof Hctxs as Hctxs'.
    pose proof a0 as a0'. apply All2_rev in a0'.
    revert Hctxs.
    unfold fix_subst, fix_context. simpl.
    revert a0'. rewrite -Hlen -(@List.rev_length _ mfix0).
    rewrite !rev_mapi. unfold mapi.
    assert (#|mfix0| >= #|List.rev mfix0|) by (rewrite List.rev_length; lia).
    assert (#|mfix1| >= #|List.rev mfix1|) by (rewrite List.rev_length; lia).
    assert (He :0 = #|mfix0| - #|List.rev mfix0|) by (rewrite List.rev_length; auto with arith).
    assert (He' :0 = #|mfix1| - #|List.rev mfix1|) by (rewrite List.rev_length; auto with arith).
    rewrite {2 6}He {3 6}He'. clear He He'. revert H H0.
    assert (#|List.rev mfix0| = #|List.rev mfix1|) by (rewrite !List.rev_length; lia).
    revert H.
    generalize (List.rev mfix0) (List.rev mfix1).
    intros l l' Heqlen Hlen' Hlen'' H. induction H. simpl. constructor.
    simpl.
    simpl in *.
    replace (S (#|mfix0| - S #|l|)) with (#|mfix0| - #|l|) by lia.
    replace (S (#|mfix1| - S #|l'|)) with (#|mfix1| - #|l'|) by lia.
    rewrite -Hlen.
    assert ((Nat.pred #|mfix0| - (#|mfix0| - S #|l|)) = #|l|) by lia.
    assert ((Nat.pred #|mfix0| - (#|mfix0| - S #|l'|)) = #|l'|) by lia.
    rewrite H0 H1.
    intros. depelim Hctxs. depelim a.
    red in o. noconf Heqlen. simpl in H.
    rewrite -H.
    econstructor. unfold mapi in IHAll2.
    forward IHAll2 by lia.
    forward IHAll2 by lia.
    forward IHAll2 by lia. rewrite -H in IHAll2.
    rewrite -Hlen in IHAll2.
    apply IHAll2; clear IHAll2.
    rewrite -H in Hctxs.
    apply Hctxs; clear Hctxs.
    clear IHAll2 Hctxs. destruct r.
    destruct o0. destruct p. destruct p.
    simpl in *. simpl in H.
    rewrite H in o |- *.
    rewrite rho_ctx_app in o. apply o.
    simp rho; simpl; simp rho.
    econstructor. eauto. clear Hctxs o IHAll2.
    rewrite -fold_fix_context_rho_ctx.
    eapply All2_fold_pred_fix_ctx. eapply Hctxs'.
    eapply All2_mix. rewrite -fold_fix_context_rho_ctx.
    all:clear IHAll2 Hctxs H o r.
    { eapply All2_mix_inv in a0. destruct a0.
      eapply All2_sym. unfold on_Trel.
      eapply All2_mix_inv in a. destruct a.
      eapply All2_map_left. simpl. auto. }
    { eapply All2_mix_inv in a0. destruct a0.
      eapply All2_sym. unfold on_Trel.
      eapply All2_mix_inv in a0. destruct a0.
      eapply All2_mix_inv in a0. destruct a0.
      eapply All2_mix.
      rewrite -fold_fix_context_rho_ctx.
      rewrite fix_context_map_fix. simpl.
      rewrite rho_ctx_app in a2. unfold on_Trel.
      eapply All2_map_left. simpl. eapply a2.
      eapply All2_map_left. simpl. solve_all. }
  Qed.*)

  (*Lemma wf_rho_cofix_subst Γ Γ' mfix0 mfix1 :
    #|mfix0| = #|mfix1| ->
    pred1_ctx Σ Γ' (rho_ctx Γ) ->
    All2_fold
      (on_decls
         (on_decls_over
            (fun (Γ Γ' : context) (t t0 : term) => pred1 Σ Γ' (rho_ctx Γ) t0 (rho (rho_ctx Γ) t)) Γ
            Γ')) (fix_context mfix0) (fix_context mfix1) ->
    All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1) dtype dbody
                  (fun x : def term => (dname x, rarg x))
                  (fun (Γ Γ' : context) (x y : term) => (pred1 Σ Γ Γ' x y *
                                                     pred1 Σ Γ' (rho_ctx Γ) y (rho (rho_ctx Γ) x))%type)
                  mfix0 mfix1 ->
    psubst Σ Γ' (rho_ctx Γ) (cofix_subst mfix1) (map (rho (rho_ctx Γ)) (cofix_subst mfix0))
           (fix_context mfix1) (rho_ctx_over (rho_ctx Γ) (fix_context mfix0)).
  Proof.
    intros Hlen Hred Hctxs a0. pose proof Hctxs as Hctxs'.
    pose proof a0 as a0'. apply All2_rev in a0'.
    revert Hctxs.
    unfold cofix_subst, fix_context. simpl.
    revert a0'. rewrite -Hlen -(@List.rev_length _ mfix0).
    rewrite !rev_mapi. unfold mapi.
    assert (#|mfix0| >= #|List.rev mfix0|) by (rewrite List.rev_length; lia).
    assert (#|mfix1| >= #|List.rev mfix1|) by (rewrite List.rev_length; lia).
    assert (He :0 = #|mfix0| - #|List.rev mfix0|) by (rewrite List.rev_length; auto with arith).
    assert (He' :0 = #|mfix1| - #|List.rev mfix1|) by (rewrite List.rev_length; auto with arith).
    rewrite {2 6}He {3 6}He'. clear He He'. revert H H0.
    assert (#|List.rev mfix0| = #|List.rev mfix1|) by (rewrite !List.rev_length; lia).
    revert H.
    generalize (List.rev mfix0) (List.rev mfix1).
    intros l l' Heqlen Hlen' Hlen'' H. induction H. simpl. constructor.
    simpl.
    simpl in *.
    replace (S (#|mfix0| - S #|l|)) with (#|mfix0| - #|l|) by lia.
    replace (S (#|mfix1| - S #|l'|)) with (#|mfix1| - #|l'|) by lia.
    rewrite -Hlen.
    assert ((Nat.pred #|mfix0| - (#|mfix0| - S #|l|)) = #|l|) by lia.
    assert ((Nat.pred #|mfix0| - (#|mfix0| - S #|l'|)) = #|l'|) by lia.
    rewrite H0 H1.
    intros. depelim Hctxs. red in o.
    constructor. unfold mapi in IHAll2.
    forward IHAll2 by lia.
    forward IHAll2 by lia.
    forward IHAll2 by lia. rewrite -Hlen in IHAll2.
    apply IHAll2; clear IHAll2. apply Hctxs; clear Hctxs.
    clear IHAll2 Hctxs. destruct r.
    destruct o0. destruct p. destruct p. red in o.
    simpl in *. noconf Heqlen. simpl in H.
    rewrite H in o |- *.
    rewrite rho_ctx_app in o. apply o.
    simp rho; simpl; simp rho.
    econstructor. eauto. clear Hctxs o IHAll2.
    rewrite -fold_fix_context_rho_ctx.
    eapply All2_fold_pred_fix_ctx. eapply Hctxs'.
    eapply All2_mix. rewrite -fold_fix_context_rho_ctx.
    all:clear IHAll2 Hctxs H o r.
    { eapply All2_mix_inv in a0. destruct a0.
      eapply All2_sym. unfold on_Trel.
      eapply All2_mix_inv in a. destruct a.
      eapply All2_map_left. simpl. auto. }
    { eapply All2_mix_inv in a0. destruct a0.
      eapply All2_sym. unfold on_Trel.
      eapply All2_mix_inv in a0. destruct a0.
      eapply All2_mix_inv in a0. destruct a0.
      eapply All2_mix.
      rewrite -fold_fix_context_rho_ctx.
      rewrite fix_context_map_fix. simpl.
      rewrite rho_ctx_app in a2. unfold on_Trel.
      eapply All2_map_left. simpl. eapply a2.
      eapply All2_map_left. simpl. solve_all. }
  Qed.*)


  Lemma isConstruct_app_pred1 {Γ Δ a b} : pred1 Σ Γ Δ a b -> isConstruct_app a -> isConstruct_app b.
  Proof.
    move=> pr; rewrite /isConstruct_app.
    move e: (decompose_app a) => [hd args].
    apply decompose_app_inv in e. subst a. simpl.
    case: hd pr => // ind n ui.
    move/pred1_mkApps_tConstruct => [args' [-> Hargs']] _.
    rewrite decompose_app_mkApps //.
  Qed.

  Lemma is_constructor_pred1 Γ Γ' n l l' : 
    All2 (pred1 Σ Γ Γ') l l' ->
    is_constructor n l -> is_constructor n l'.
  Proof.
    induction 1 in n |- *.
    - now rewrite /is_constructor nth_error_nil.
    - destruct n; rewrite /is_constructor /=.
      now eapply isConstruct_app_pred1.
      eapply IHX.
  Qed.
  
  Ltac inv_on_free_vars ::=
    match goal with
    | [ H : is_true (on_free_vars ?P ?t) |- _ ] => 
      progress (cbn in H || rewrite on_free_vars_mkApps in H);
      (move/and5P: H => [] || move/and4P: H => [] || move/and3P: H => [] || move/andP: H => [] || 
        eapply forallb_All in H); intros
    | [ H : is_true (test_def (on_free_vars ?P) ?Q ?x) |- _ ] =>
      move/andP: H => []; rewrite ?shiftnP_xpredT; intros
    end.
  
  Lemma pred1_on_free_vars_gen :
    (forall Γ Γ' t u,
    pred1 Σ Γ Γ' t u ->
    forall P, 
      on_ctx_free_vars P Γ ->
      on_free_vars P t -> on_free_vars P u) ×
    (forall Γ Γ' Δ Δ',
      pred1_ctx Σ Γ Γ' ->
      pred1_ctx_over Σ Γ Γ' Δ Δ' ->
      forall P, 
        on_ctx_free_vars P (Γ ,,, Δ) ->
        on_ctx_free_vars P (Γ' ,,, Δ')).
  Proof.
    set Pctx :=
      fun (Γ Δ : context) => 
        forall P, on_ctx_free_vars P Γ -> on_ctx_free_vars P Δ.
    set Pctxover := 
      fun (Γ Γ' Δ Δ' : context) => 
        forall P,
          on_ctx_free_vars P (Γ ,,, Δ) ->
          on_ctx_free_vars P (Γ' ,,, Δ').

    Ltac IHs := 
        match goal with
        [ H : forall P, is_true (on_ctx_free_vars P ?Γ) -> is_true (on_free_vars P ?t) -> _, 
          H' : is_true (on_ctx_free_vars _ ?Γ), 
          H'' : is_true (on_free_vars _ ?t) |- _ ] =>
          specialize (H _ H' H'')
        end.
    Ltac t := repeat IHs; rtoProp; intuition auto.

    apply: (pred1_ind_all_ctx _ _ Pctx Pctxover); subst Pctx Pctxover; cbn; intros; auto.
    all:try solve [t].

    - move: H; rewrite /on_ctx_free_vars.
      generalize 0.
      induction X0 in P |- *; simpl; auto.
      intros n.
      move/andP => [] Hd HΓ.
      apply/andP; split.
      destruct (P n) => //.
      rewrite /= in Hd *.
      { destruct p; cbn in Hd |- *.
        specialize (i (addnP (S n) P)).
        rewrite alli_shift in HΓ.
        rewrite /on_ctx_free_vars in i.
        setoid_rewrite addnP_add in i.
        setoid_rewrite Nat.add_comm in i.
        setoid_rewrite Nat.add_succ_r in i.
        eauto.
        specialize (i (addnP (S n) P)).
        specialize (i0 (addnP (S n) P)).
        move/andP: Hd => /= [onb ont].
        rewrite alli_shift in HΓ.
        rewrite /on_ctx_free_vars in i i0.
        setoid_rewrite addnP_add in i.
        setoid_rewrite Nat.add_comm in i.
        setoid_rewrite Nat.add_succ_r in i.
        setoid_rewrite addnP_add in i0.
        setoid_rewrite Nat.add_comm in i0.
        setoid_rewrite Nat.add_succ_r in i0.
        eauto with fvs. }
      now specialize (IHX0 P (S n) HΓ).
    
    - move: H0.
      rewrite !on_ctx_free_vars_app.
      move/andP=> [] onΔ onΓ. specialize (H _ onΓ).
      rewrite -(All2_fold_length X2) H andb_true_r.
      clear H. move: onΓ.
      move: onΔ; rewrite /on_ctx_free_vars.
      generalize 0. clear -X2.
      induction X2 in P |- *; simpl; auto.
      intros n.
      move/andP => [] Hd HΓ' HΓ.
      apply/andP; split.
      destruct (P n) => //.
      rewrite /= in Hd *.
      { destruct p; cbn in Hd |- *.
        - red in o.
          specialize (o (addnP (S n) P)).
          forward o.
          rewrite on_ctx_free_vars_app.
          rewrite alli_shift in HΓ'.
          rewrite alli_shift in HΓ.
          rewrite /on_ctx_free_vars.
          setoid_rewrite addnP_add.
          setoid_rewrite Nat.add_comm.
          setoid_rewrite Nat.add_succ_r.
          rewrite HΓ' /=.
          red. rewrite -HΓ. apply alli_ext => i d.
          rewrite addnP_add {1 4}/addnP !addnP_add. lia_f_equal.
          eauto.
        - red in o, o0.
          specialize (o (addnP (S n) P)).
          specialize (o0 (addnP (S n) P)).
          assert (onext : on_ctx_free_vars (addnP (S n) P) (Γ ,,, Γ0)).
          { rewrite on_ctx_free_vars_app.
            rewrite alli_shift in HΓ'.
            rewrite alli_shift in HΓ.
            rewrite /on_ctx_free_vars.
            setoid_rewrite addnP_add.
            setoid_rewrite Nat.add_comm.
            setoid_rewrite Nat.add_succ_r.
            rewrite HΓ' /=.
            red. rewrite -HΓ. apply alli_ext => i d.
            rewrite addnP_add {1 4}/addnP !addnP_add. lia_f_equal. }
          move/andP: Hd => /= [onb ont].
          specialize (o onext onb).
          specialize (o0 onext ont).
          eauto with fvs. }
      apply (IHX2 P (S n) HΓ').
      rewrite (alli_shiftn 1).
      red; rewrite -HΓ.
      apply alli_ext => i ?.
      rewrite !addnP_add {1 3}/addnP. lia_f_equal.

    - repeat t.
      eapply on_free_vars_subst; cbn; t.
      specialize (H (shiftnP 1 P)).
      setoid_rewrite addnP_shiftnP in H.
      rewrite {1}/shiftnP /= in H. 
      forward H. t.
      rewrite alli_shift.
      rewrite /on_ctx_free_vars in H2.
      red; rewrite -H2.
      apply alli_ext => i ?.
      rewrite {1}/shiftnP /=.
      now rewrite Nat.sub_0_r (addnP_shiftnP_k 1).
      specialize (H H5). t.

    - move/and3P: H3 => [] ond0 ont0 onb0; t.
      eapply on_free_vars_subst; cbn; t.
      specialize (H1 (shiftnP 1 P)).
      setoid_rewrite addnP_shiftnP in H1.
      rewrite {1}/shiftnP /= in H1. 
      forward H1. t. now eapply on_free_vars_vdef.
      rewrite alli_shift.
      rewrite /on_ctx_free_vars in H2.
      red; rewrite -H2.
      apply alli_ext => i ?.
      rewrite {1}/shiftnP /=.
      now rewrite Nat.sub_0_r (addnP_shiftnP_k 1).
      specialize (H1 onb0). t.

    - specialize (H _ H1). t.
      rewrite on_free_vars_lift0 //.
      change P with (addnP 0 P) in H.
      destruct nth_error eqn:hnth => //.
      eapply nth_error_on_free_vars_ctx in H; tea.
      destruct c as [na [decl|] ty] => //. noconf H0.
      now move/andP: H.

    - move/and4P: H3 => [] hpars hret hctx /andP[] hargs hbrs.
      rewrite /iota_red.
      eapply on_free_vars_subst.
      { rewrite forallb_rev forallb_skipn //.
        inv_on_free_vars. solve_all; eauto with fvs. }
      len.
      eapply All2_nth_error_Some_right in X2 as [t' [hnth [? [[? ?] ?]]]]; tea.
      eapply nth_error_forallb in hbrs; tea. cbn in hbrs.
      move/andP: hbrs => [] hctx' hbody.
      eapply on_free_vars_expand_lets_k. now len.
      eapply on_free_vars_ctx_inst_case_context; trea; len; eauto with fvs.
      solve_all.
      rewrite -e. 
      now rewrite -(All2_length X1). len. eapply i0.
      rewrite on_ctx_free_vars_app; len; rewrite e addnP_shiftnP H2 andb_true_r.
      relativize #|bcontext br|; [erewrite on_free_vars_ctx_on_ctx_free_vars|]; len; try congruence.
      eapply on_free_vars_ctx_inst_case_context; trea; len.
      now rewrite -e.

    - inv_on_free_vars. t.
      rewrite on_free_vars_mkApps.
      specialize (H _ H3). t. inv_on_free_vars.
      2:solve_all.
      move: H1.
      rewrite /unfold_fix. destruct nth_error eqn:hnth => //.
      intros [= <- <-].
      assert (on_ctx_free_vars (shiftnP #|mfix0| P) (Γ,,, fix_context mfix0)).
      { rewrite on_ctx_free_vars_app; len; rewrite addnP_shiftnP H3 andb_true_r.
        relativize #|mfix0|; [erewrite on_free_vars_ctx_on_ctx_free_vars|]; len => //.
        eapply on_free_vars_fix_context. solve_all. }
      assert (forallb (test_def (on_free_vars P) (on_free_vars (shiftnP #|mfix1| P))) mfix1).
      { solve_all. eapply All2_All_mix_left in X1; tea.
        rewrite -(All2_length X1).
        unfold on_Trel in *; solve_all.
        inv_on_free_vars. apply /andP; split; eauto with fvs. }
      eapply on_free_vars_subst.
      eapply (on_free_vars_fix_subst _ _ idx). cbn => //.
      len. eapply nth_error_forallb in H4; tea.
      now move/andP: H4 => [].
    
    - admit.
    - inv_on_free_vars. admit.
    - t. admit.
    - t. admit.
    - t; admit.
    - t; admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.

  Lemma pred1_on_free_vars {P Γ Γ' t u} :
    pred1 Σ Γ Γ' t u ->
    on_ctx_free_vars P Γ ->
    on_free_vars P t ->
    on_free_vars P u.
  Proof.
    intros p onΓ ont.
    now move/andP: (fst pred1_on_free_vars_gen _ _ _ _ p P onΓ ont).
  Qed.
  
  Lemma pred1_on_free_vars_ctx {P Γ Γ'} :
    pred1_ctx Σ Γ Γ' ->
    on_ctx_free_vars P Γ ->
    on_ctx_free_vars P Γ'.
  Proof.
    intros p onΓ.
    epose proof (snd pred1_on_free_vars_gen _ _ [] [] p).
    forward H. constructor. now apply H.
  Qed.


  Lemma pred1_over_on_free_vars_ctx {P Γ Γ' Δ Δ'} :
    pred1_ctx Σ Γ Γ' ->
    pred1_ctx_over Σ Γ Γ' Δ Δ' ->
    on_ctx_free_vars P (Γ ,,, Δ) ->
    on_ctx_free_vars P (Γ' ,,, Δ').
  Proof.
    intros p p' onΓ.
    now apply (snd pred1_on_free_vars_gen _ _ _ _ p p' P).
  Qed.

  Lemma on_free_vars_subst_consn P s x : 
    forallb (on_free_vars P) s ->
    on_free_vars xpredT ((s ⋅n ids) x).
  Proof.
    rewrite /subst_consn => hs.
    destruct nth_error eqn:hnth => //.
    eapply nth_error_forallb in hs; tea; cbn in *.
    eapply on_free_vars_impl; tea => //.
  Qed.

  Lemma on_free_vars_cofix_subst_pred p mfix0 mfix1 : 
    forallb (on_free_vars p) (cofix_subst mfix0) ->
    forallb (on_free_vars p) (cofix_subst mfix1).
  Proof.
  Admitted.

  Lemma on_free_vars_fix_subst_pred p mfix0 mfix1 : 
    forallb (on_free_vars p) (fix_subst mfix0) ->
    forallb (on_free_vars p) (fix_subst mfix1).
  Proof.
  Admitted.

  Lemma lift0_inst_id k t s : #|s| < k -> (lift0 k t).[s ⋅n ids] = lift0 (k - #|s|) t.
  Proof.
    intros Hs. sigma.
    apply inst_ext.
    rewrite shift_subst_consn_ge. 2:lia. now sigma.
  Qed.

  Lemma pred_subst_rho_cofix p (Γ Γ' rΓ : context) (mfix0 mfix1 : mfixpoint term) :
    forallb (test_def (on_free_vars p) (on_free_vars (shiftnP #|mfix0| p))) mfix0 ->
    on_ctx_free_vars xpredT Γ' ->
    pred1_ctx Σ Γ Γ' -> pred1_ctx Σ Γ' rΓ -> 
    pred1_ctx_over Σ Γ' rΓ (fix_context mfix1)
    (rho_ctx_over rΓ (fix_context mfix0)) ->
    All2 (on_Trel eq (fun x : def term => (dname x, rarg x)))
           mfix0 mfix1
    -> All2
        (on_Trel
           (fun x y : term => pred1 Σ Γ Γ' x y
                                × pred1 Σ Γ' rΓ y
                                (rho rΓ x)) dtype)
        mfix0 mfix1
    -> All2
        (on_Trel
           (fun x y : term => pred1 Σ
                                (Γ ,,, fix_context mfix0)
                                (Γ' ,,, fix_context mfix1) x
                                y
                                × pred1 Σ
                                (Γ' ,,, fix_context mfix1)
                                (rΓ ,,, rho_ctx_over rΓ (fix_context mfix0)) y
                                (rho (rΓ ,,, rho_ctx_over rΓ (fix_context mfix0)) x))
           dbody) mfix0 mfix1
    -> pred1_subst (Σ := Σ) xpredT xpredT (Γ' ,,, fix_context mfix1) 
      (rΓ ,,, rho_ctx_over rΓ (fix_context mfix0)) Γ' rΓ 
        (cofix_subst mfix1 ⋅n ids)
        (cofix_subst (map_fix rho rΓ (rho_ctx_over rΓ (fix_context mfix0)) mfix0) ⋅n ids).
  Proof.
    intros hm onΓ' predΓ predΓ' fctx eqf redr redl.
    split => //. split => //.
    intros x _.
    split.
    { eapply on_free_vars_cofix_subst in hm => //.
      eapply on_free_vars_subst_consn.
      eapply on_free_vars_cofix_subst_pred; tea. }
    split. 
    destruct (leb_spec_Set (S x) #|cofix_subst mfix1|).
    2:{ len in l; rewrite !subst_consn_ge //; len; try lia.
        all:rewrite (All2_length redl) //. lia.
        now eapply pred1_refl_gen.
    }
    destruct (subst_consn_lt_spec l) as [? [Hb Hb']].
    rewrite Hb'.
    eapply nth_error_cofix_subst in Hb. subst.
    rewrite cofix_subst_length in l.
    rewrite -(All2_length eqf) in l.
    rewrite -(cofix_subst_length mfix0) in l.
    destruct (subst_consn_lt_spec l) as [b' [Hb0 Hb0']].
    rewrite (rho_cofix_subst p) //.
    pose proof (nth_error_map (rho rΓ) x (cofix_subst mfix0)).
    rewrite Hb0 in H. simpl in H.
    rewrite /subst_consn H.
    eapply nth_error_cofix_subst in Hb0. subst b'.
    cbn. rewrite (All2_length eqf).
    simp rho; simpl; simp rho.
    rewrite -(fold_fix_context_rho_ctx p) //. constructor; auto.
    + rewrite (fix_context_map_fix p) //.
    + red. clear -wfΣ p hm eqf redr redl.
      eapply All2_sym. apply All2_map_left.
      pose proof (All2_mix eqf (All2_mix redr redl)) as X; clear eqf redr redl.
      eapply All2_impl; eauto. clear X.
      unfold on_Trel in *. simpl. intros x y.
      rewrite (fix_context_map_fix p) //. intuition auto.
    + intros decl. pose proof (fix_context_assumption_context mfix1).
      destruct (leb_spec_Set (S x) #|fix_context mfix1|).
      rewrite nth_error_app_lt //.
      destruct (nth_error (fix_context mfix1) x) eqn:Heq => // /=; auto.
      destruct c as [na [?|] ty] => //.
      move: (nth_error_assumption_context _ _ _ H Heq) => //.
      intros [= <-] => //.
      pose proof (All2_length redl). len in l.
      rewrite nth_error_app_ge ?fix_context_length //; try lia.
      destruct nth_error eqn:hnth => //.
      intros [= ->]. destruct decl as [na [b|] ty] => /= //.
      eapply nth_error_pred1_ctx in predΓ.
      2:erewrite hnth=> /= //.
      destruct predΓ as [body' [eq pr]].
      epose proof (nth_error_pred1_ctx_l _ _ predΓ').
      erewrite hnth in X. specialize (X eq_refl) as [body'' [eq' pr']].
      exists body''.
      rewrite nth_error_app_ge //; len; try lia. rewrite H0.
      split => //.
      rewrite subst_consn_ge. len; lia. len.
      rewrite -H0 {1}/ids.
      rewrite -inst_assoc.
      rewrite -lift0_inst lift0_inst_id. len. lia.
      len. replace (S x - #|mfix0|) with (S (x - #|mfix0|)) by lia.
      econstructor; tea. now rewrite H0.
  Qed.

  Lemma pred_subst_rho_fix p (Γ Γ' rΓ : context) (mfix0 mfix1 : mfixpoint term) :
    forallb (test_def (on_free_vars p) (on_free_vars (shiftnP #|mfix0| p))) mfix0 ->
    on_ctx_free_vars xpredT Γ' ->
    pred1_ctx Σ Γ Γ' -> pred1_ctx Σ Γ' rΓ -> 
    pred1_ctx_over Σ Γ' rΓ (fix_context mfix1)
    (rho_ctx_over rΓ (fix_context mfix0)) ->
    All2 (on_Trel eq (fun x : def term => (dname x, rarg x)))
           mfix0 mfix1
    -> All2
        (on_Trel
           (fun x y : term => pred1 Σ Γ Γ' x y
                                × pred1 Σ Γ' rΓ y
                                (rho rΓ x)) dtype)
        mfix0 mfix1
    -> All2
        (on_Trel
           (fun x y : term => pred1 Σ
                                (Γ ,,, fix_context mfix0)
                                (Γ' ,,, fix_context mfix1) x
                                y
                                × pred1 Σ
                                (Γ' ,,, fix_context mfix1)
                                (rΓ ,,, rho_ctx_over rΓ (fix_context mfix0)) y
                                (rho (rΓ ,,, rho_ctx_over rΓ (fix_context mfix0)) x))
           dbody) mfix0 mfix1
    -> pred1_subst (Σ := Σ) xpredT xpredT (Γ' ,,, fix_context mfix1) 
      (rΓ ,,, rho_ctx_over rΓ (fix_context mfix0)) Γ' rΓ 
        (fix_subst mfix1 ⋅n ids)
        (fix_subst (map_fix rho rΓ (rho_ctx_over rΓ (fix_context mfix0)) mfix0) ⋅n ids).
  Proof.
    intros hm onΓ' predΓ predΓ' fctx eqf redr redl.
    split => //. split => //.
    intros x _.
    split.
    { eapply on_free_vars_fix_subst in hm => //.
      eapply on_free_vars_subst_consn.
      eapply on_free_vars_fix_subst_pred; tea. }
    split. 
    destruct (leb_spec_Set (S x) #|fix_subst mfix1|).
    2:{ len in l; rewrite !subst_consn_ge //; len; try lia.
        all:rewrite (All2_length redl) //. lia.
        now eapply pred1_refl_gen.
    }
    destruct (subst_consn_lt_spec l) as [? [Hb Hb']].
    rewrite Hb'.
    eapply nth_error_fix_subst in Hb. subst.
    rewrite fix_subst_length in l.
    rewrite -(All2_length eqf) in l.
    rewrite -(fix_subst_length mfix0) in l.
    destruct (subst_consn_lt_spec l) as [b' [Hb0 Hb0']].
    rewrite (rho_fix_subst p) //.
    pose proof (nth_error_map (rho rΓ) x (fix_subst mfix0)).
    rewrite Hb0 in H. simpl in H.
    rewrite /subst_consn H.
    eapply nth_error_fix_subst in Hb0. subst b'.
    cbn. rewrite (All2_length eqf).
    simp rho; simpl; simp rho.
    rewrite -(fold_fix_context_rho_ctx p) //. constructor; auto.
    + rewrite (fix_context_map_fix p) //.
    + red. clear -wfΣ p hm eqf redr redl.
      eapply All2_sym. apply All2_map_left.
      pose proof (All2_mix eqf (All2_mix redr redl)) as X; clear eqf redr redl.
      eapply All2_impl; eauto. clear X.
      unfold on_Trel in *. simpl. intros x y.
      rewrite (fix_context_map_fix p) //. intuition auto.
    + intros decl. pose proof (fix_context_assumption_context mfix1).
      destruct (leb_spec_Set (S x) #|fix_context mfix1|).
      rewrite nth_error_app_lt //.
      destruct (nth_error (fix_context mfix1) x) eqn:Heq => // /=; auto.
      destruct c as [na [?|] ty] => //.
      move: (nth_error_assumption_context _ _ _ H Heq) => //.
      intros [= <-] => //.
      pose proof (All2_length redl). len in l.
      rewrite nth_error_app_ge ?fix_context_length //; try lia.
      destruct nth_error eqn:hnth => //.
      intros [= ->]. destruct decl as [na [b|] ty] => /= //.
      eapply nth_error_pred1_ctx in predΓ.
      2:erewrite hnth=> /= //.
      destruct predΓ as [body' [eq pr]].
      epose proof (nth_error_pred1_ctx_l _ _ predΓ').
      erewrite hnth in X. specialize (X eq_refl) as [body'' [eq' pr']].
      exists body''.
      rewrite nth_error_app_ge //; len; try lia. rewrite H0.
      split => //.
      rewrite subst_consn_ge. len; lia. len.
      rewrite -H0 {1}/ids.
      rewrite -inst_assoc.
      rewrite -lift0_inst lift0_inst_id. len. lia.
      len. replace (S x - #|mfix0|) with (S (x - #|mfix0|)) by lia.
      econstructor; tea. now rewrite H0.
  Qed.

  Section All2_telescope.
    Context (P : forall (Γ Γ' : context),  context_decl -> context_decl -> Type).

    Definition telescope := context.

    Inductive All2_telescope (Γ Γ' : context) : telescope -> telescope -> Type :=
    | telescope2_nil : All2_telescope Γ Γ' [] []
    | telescope2_cons_abs na t t' Δ Δ' :
        P Γ Γ' (vass na t) (vass na t') ->
        All2_telescope (Γ ,, vass na t) (Γ' ,, vass na t') Δ Δ' ->
        All2_telescope Γ Γ' (vass na t :: Δ) (vass na t' :: Δ')
    | telescope2_cons_def na b b' t t' Δ Δ' :
        P Γ Γ' (vdef na b t) (vdef na b' t') ->
        All2_telescope (Γ ,, vdef na b t) (Γ' ,, vdef na b' t') Δ Δ' ->
        All2_telescope Γ Γ' (vdef na b t :: Δ) (vdef na b' t' :: Δ').
  End All2_telescope.

  Section All2_telescope_n.
    Context (P : forall (Γ Γ' : context), context_decl -> context_decl -> Type).
    Context (f : nat -> term -> term).

    Inductive All2_telescope_n (Γ Γ' : context) (n : nat) : telescope -> telescope -> Type :=
    | telescope_n_nil : All2_telescope_n Γ Γ' n [] []
    | telescope_n_cons_abs na t t' Δ Δ' :
        P Γ Γ' (vass na (f n t)) (vass na (f n t')) ->
        All2_telescope_n (Γ ,, vass na (f n t)) (Γ' ,, vass na (f n t')) (S n) Δ Δ' ->
        All2_telescope_n Γ Γ' n (vass na t :: Δ) (vass na t' :: Δ')
    | telescope_n_cons_def na b b' t t' Δ Δ' :
        P Γ Γ' (vdef na (f n b) (f n t)) (vdef na (f n b') (f n t')) ->
        All2_telescope_n (Γ ,, vdef na (f n b) (f n t)) (Γ' ,, vdef na (f n b') (f n t'))
                         (S n) Δ Δ' ->
        All2_telescope_n Γ Γ' n (vdef na b t :: Δ) (vdef na b' t' :: Δ').

  End All2_telescope_n.

  Lemma All2_telescope_mapi {P} Γ Γ' Δ Δ' (f : nat -> term -> term) k :
    All2_telescope_n P f Γ Γ' k Δ Δ' ->
    All2_telescope P Γ Γ' (mapi_rec (fun n => map_decl (f n)) Δ k)
                   (mapi_rec (fun n => map_decl (f n)) Δ' k).
  Proof.
    induction 1; simpl; constructor; auto.
  Qed.

  Lemma local_env_telescope P Γ Γ' Δ Δ' :
    All2_telescope (on_decls P) Γ Γ' Δ Δ' ->
    All2_fold_over P Γ Γ' (List.rev Δ) (List.rev Δ').
  Proof.
    induction 1. simpl. constructor.
    - simpl. depelim p. eapply All2_fold_over_app.
      repeat constructor => //.
      revert IHX.
      generalize (List.rev Δ) (List.rev Δ'). induction 1. constructor.
      constructor; auto. depelim p0; constructor; unfold on_decls_over in *;
      now rewrite !app_context_assoc.
    - simpl. eapply All2_fold_over_app. repeat constructor => //.
      revert IHX.
      generalize (List.rev Δ) (List.rev Δ'). induction 1. constructor.
      constructor; auto. depelim p0; constructor; unfold on_decls_over in *;
      now rewrite !app_context_assoc.
  Qed.


  Lemma All_All2_telescopei_gen p (Γ Γ' Δ Δ' : context) (m m' : mfixpoint term) :
    #|Δ| = #|Δ'| ->
    on_ctx_free_vars p Γ' ->
    forallb (test_def (on_free_vars p) (on_free_vars (shiftnP #|m| p))) m ->
    forallb (test_def (on_free_vars p) (on_free_vars (shiftnP #|m| p))) m' ->
    All2
      (fun (x y : def term) => (pred1 Σ Γ' Γ (dtype x) (rho Γ (dtype y))) * (dname x = dname y))%type m m' ->
    All2_fold_over (pred1 Σ) Γ' Γ Δ (rho_ctx_over Γ Δ') ->
    All2_telescope_n (on_decls (pred1 Σ)) (fun n : nat => lift0 n)
                    (Γ' ,,, Δ) (Γ ,,, rho_ctx_over Γ Δ')
                    #|Δ|
  (map (fun def : def term => vass (dname def) (dtype def)) m)
    (map (fun def : def term => vass (dname def) (rho Γ (dtype def))) m').
  Proof.
    generalize #|m|. intros n Δlen onΓ' onm onm'.
    induction 1 in Δ, Δ', Δlen, onm, onm' |- *; cbn. constructor.
    intros. destruct r. rewrite e.
    move: onm => /= /andP[] /andP [] onty onbody onl.
    move: onm' => /= /andP[] /andP [] onty' onbody' onl'.
    repeat constructor.
    assert (#|Δ| = #|rho_ctx_over Γ Δ'|) by now rewrite rho_ctx_over_length.
    rewrite {2}H.
    eapply weakening_pred1_pred1; eauto.
    specialize (IHX (vass (dname y) (lift0 #|Δ| (dtype x)) :: Δ)
                    (vass (dname y) (lift0 #|Δ'| (dtype y)) :: Δ')).
    assert (#|Δ| = #|rho_ctx_over Γ Δ'|) by now rewrite rho_ctx_over_length.
    rewrite {2}H.
    rewrite (rho_lift0 _ _ p) //.
    unfold snoc. forward IHX. simpl. lia.
    do 2 forward IHX by auto. cbn.
    forward IHX. constructor. apply X0. constructor. simpl.
    red.
    assert (#|Δ'| = #|rho_ctx_over Γ Δ'|) by now rewrite rho_ctx_over_length.
    rewrite H0.
    rewrite - (rho_lift0 Γ (rho_ctx_over Γ Δ') p) //. simpl.
    eapply weakening_pred1_pred1; eauto.
    simpl in IHX. rewrite -H. rewrite {2}Δlen.
    apply IHX.
  Qed.

  Lemma All_All2_telescopei p (Γ Γ' : context) (m m' : mfixpoint term) :
    on_ctx_free_vars p Γ' ->
    forallb (test_def (on_free_vars p) (on_free_vars (shiftnP #|m| p))) m ->
    forallb (test_def (on_free_vars p) (on_free_vars (shiftnP #|m| p))) m' ->
    All2 (fun (x y : def term) => (pred1 Σ Γ' Γ (dtype x) (rho Γ (dtype y))) *
                              (dname x = dname y))%type m m' ->
    All2_telescope_n (on_decls (pred1 Σ)) (fun n : nat => lift0 n) Γ' Γ 0
      (map (fun def : def term => vass (dname def) (dtype def)) m)
      (map (fun def : def term => vass (dname def) (rho Γ (dtype def))) m').
  Proof.
    specialize (All_All2_telescopei_gen p Γ Γ' [] [] m m'). simpl.
    intros. specialize (X eq_refl H H0 H1 X0). forward X. constructor.
    apply X.
  Qed.


  Lemma rho_All_All2_fold_inv :
  forall Γ Γ' : context, pred1_ctx Σ Γ' Γ -> forall Δ Δ' : context,
      All2_fold (on_decls (on_decls_over (pred1 Σ) Γ' Γ)) Δ
                     (rho_ctx_over Γ Δ') ->
      All2_fold
        (on_decls
           (fun (Δ Δ' : context) (t t' : term) => pred1 Σ (Γ' ,,, Δ)
                                                    (Γ ,,, rho_ctx_over Γ Δ') t
                                                    (rho (Γ ,,, rho_ctx_over Γ Δ') t'))) Δ Δ'.

  Proof.
    intros. induction Δ in Δ', X0 |- *; depelim X0; destruct Δ'; noconf H.
    - constructor.
    - destruct c as [? [?|] ?]; simpl in *; depelim a0; simpl in *; constructor;
      rewrite ?rho_ctx_app.
      2:constructor; auto. eapply IHΔ; auto; rewrite !rho_ctx_app; eauto.
      apply IHΔ; auto. constructor; auto.
  Qed.

  Lemma pred1_rho_fix_context_2 p (Γ Γ' : context) (m m' : mfixpoint term) :
    on_ctx_free_vars p Γ' ->
    forallb (test_def (on_free_vars p) (on_free_vars (shiftnP #|m| p))) m ->
    forallb (test_def (on_free_vars p) (on_free_vars (shiftnP #|m'| p))) m' ->
    pred1_ctx Σ Γ' Γ ->
    All2 (on_Trel_eq (pred1 Σ Γ' Γ) dtype dname) m
         (map_fix rho Γ (fold_fix_context rho Γ [] m') m') ->
    All2_fold
      (on_decls (on_decls_over (pred1 Σ) Γ' Γ))
      (fix_context m)
      (fix_context (map_fix rho Γ (fold_fix_context rho Γ [] m') m')).
  Proof.
    intros onΓ' hm hm' HΓ a.
    rewrite - (fold_fix_context_rho_ctx p) // in a.
    unfold map_fix in a.
    eapply All2_map_right' in a.
    rewrite - (fold_fix_context_rho_ctx p) //.
    unfold fix_context. unfold map_fix.
    eapply local_env_telescope.
    cbn.
    rewrite - (mapi_mapi
                 (fun n def => vass (dname def) (dtype def))
                 (fun n decl => lift_decl n 0 decl)).
    rewrite mapi_map. simpl.
    rewrite - (mapi_mapi
                 (fun n def => vass (dname def) (rho Γ (dtype def)))
                 (fun n decl => lift_decl n 0 decl)).
    eapply All2_telescope_mapi.
    rewrite !mapi_cst_map.
    eapply All_All2_telescopei; eauto.
    now rewrite (All2_length a).
  Qed.
  
  (* Lemma substitution_pred1 Γ Δ Γ' Δ' s s' N N' :
    psubst Σ Γ Γ' s s' Δ Δ' ->
    pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ') N N' ->
    pred1 Σ Γ Γ' (subst s 0 N) (subst s' 0 N').
  Proof.
    intros redM redN.
    pose proof (substitution_let_pred1 Σ Γ Δ [] Γ' Δ' [] s s' N N' wfΣ) as H.
    assert (#|Γ| = #|Γ'|).
    { eapply psubst_length in redM. intuition auto.
      apply pred1_pred1_ctx in redN. eapply All2_fold_length in redN.
      rewrite !app_context_length in redN. lia. }
    forward H by auto.
    forward H by pcuic.
    specialize (H eq_refl). forward H.
    apply pred1_pred1_ctx in redN; pcuic.
    eapply All2_fold_app_inv in redN; auto.
    destruct redN. apply a0.
    simpl in H. now apply H.
  Qed. *)

  (* Lemma All2_fold_fix_context P σ τ Γ Δ :
    All2_fold (on_decls (fun Γ Δ T U =>
       P (inst_context σ Γ) (inst_context τ Δ) (T.[⇑^#|Γ| σ]) (U.[⇑^#|Δ| τ]))) Γ Δ ->
    All2_fold (on_decls P) (inst_context σ Γ) (inst_context τ Δ).
  Proof.
    intros H.
    eapply All2_fold_fold_context.
    eapply PCUICEnvironment.All2_fold_impl; tea => /=.
    intros ? ? ? ? []; constructor; auto.
  Qed. *)

  Lemma All2_fold_impl_len P Q Γ Δ :
    All2_fold P Γ Δ ->
    (forall Γ Δ T U, #|Γ| = #|Δ| -> P Γ Δ T U -> Q Γ Δ T U) ->
    All2_fold Q Γ Δ.
  Proof.
    intros H HP. pose proof (All2_fold_length H).
    induction H; constructor; simpl; eauto.
  Qed.

  Lemma decompose_app_rec_inst s t l :
    let (f, a) := decompose_app_rec t l in
    inst s f = f ->
    decompose_app_rec (inst s t) (map (inst s) l)  = (f, map (inst s) a).
  Proof.
    induction t in s, l |- *; simpl; auto; try congruence.

    intros ->. simpl. reflexivity.
    specialize (IHt1 s (t2 :: l)).
    destruct decompose_app_rec. intros H. rewrite IHt1; auto.
  Qed.

  Lemma decompose_app_inst s t f a :
    decompose_app t = (f, a) -> inst s f = f ->
    decompose_app (inst s t) = (inst s f, map (inst s) a).
  Proof.
    generalize (decompose_app_rec_inst s t []).
    unfold decompose_app. destruct decompose_app_rec.
    move=> Heq [= <- <-] Heq'. now rewrite Heq' (Heq Heq').
  Qed.
  Hint Rewrite decompose_app_inst using auto : lift.


  (*
  Instance All_decls_refl P : 
  Reflexive P ->
  Reflexive (All_decls P).
Proof. intros hP d; destruct d as [na [b|] ty]; constructor; auto. Qed. *)

  (*Lemma strong_substitutivity_fixed Γ Γ' Δ Δ' s t σ τ :
    pred1 Σ Γ Γ' s t -> s = t -> Γ = Γ' ->
    ctxmap Γ Δ σ ->
    ctxmap Γ' Δ' τ ->
    (forall x : nat, pred1 Σ Δ Δ' (σ x) (τ x)) ->
    pred1 Σ Δ Δ' s.[σ] t.[τ].
  Proof.
    intros redst eq eqΓ.
    revert Δ Δ' σ τ.
    revert Γ Γ' s t redst eq eqΓ.
    set (P' := fun Γ Γ' => Γ = Γ' -> pred1_ctx Σ Γ Γ').
    set (Pover := fun Γ Γ' ctx ctx' =>
      forall Δ Δ' σ τ,
        Γ = Γ' ->
        ctxmap Γ Δ σ ->
        ctxmap Γ' Δ' τ ->
        (forall x, pred1 Σ Δ Δ' (σ x) (τ x)) ->
        pred1_ctx_over Σ Δ Δ' (inst_context σ ctx) (inst_context τ ctx')).*)


  Lemma All2_fold_context_assumptions {P Γ Δ} : 
    All2_fold (on_decls P) Γ Δ ->
    context_assumptions Γ = context_assumptions Δ.
  Proof.
    induction 1; simpl; auto. depelim p => /=; now auto using f_equal.
  Qed.
  
  Lemma pred1_subst_consn {Δ Δ' Γ Γ' args0 args1} : 
    pred1_ctx Σ Γ' Γ ->
    on_ctx_free_vars xpredT Γ' ->
    forallb (on_free_vars xpredT) args1 ->
    #|args1| = #|args0| ->
    context_assumptions Δ' = #|args0| ->
    context_assumptions Δ = context_assumptions Δ' ->
    All2 (pred1 Σ Γ' Γ) args1 args0 ->
    pred1_subst (Σ := Σ) xpredT xpredT (Γ',,, smash_context [] Δ)
      (Γ ,,, smash_context [] Δ') Γ' Γ (args1 ⋅n ids) (args0 ⋅n ids).
  Proof.
    intros Hpred hlen onΓ' onargs Hctx hΔ Ha.
    split => //. split => //.
    intros i _.
    destruct (leb_spec_Set (S i) #|args1|).
    pose proof (subst_consn_lt_spec l) as [arg [hnth heq]].
    rewrite heq.
    split; [|split].
    - eapply nth_error_forallb in hnth; tea.
    - eapply All2_nth_error_Some in Ha as [t' [hnth' pred]]; tea.
      pose proof (subst_consn_lt_spec (nth_error_Some_length hnth')) as [arg' [hnth'' ->]].
      rewrite hnth' in hnth''. now noconf hnth''.
    - intros decl. case: nth_error_appP => /= //.
      * intros x hnth'. len => hleni. intros [= <-].
        eapply nth_error_smash_context in hnth'.
        now rewrite hnth'.
        intros ? ?; now rewrite nth_error_nil.
      * len. intros x hnth' hi.
        intros [= <-]. lia.
    - rewrite subst_consn_ge //. lia.
      pose proof (All2_length Ha). len in H. rewrite H.
      rewrite subst_consn_ge //. len. lia. len. split => //.
      split => //.
      * eapply pred1_refl_gen => //.
      * intros decl. rewrite nth_error_app_ge. len. lia. len.
        destruct nth_error eqn:hnth' => /= //.
        destruct decl_body eqn:db => /= //. intros [= <-].
        rewrite nth_error_app_ge; len; try lia.
        pose proof Hpred as predΓ'.
        eapply nth_error_pred1_ctx_l in Hpred; tea.
        2:erewrite hnth'; rewrite /= db //.
        destruct Hpred as [body' [eq' pr]]. exists body'; split => //.
        now rewrite -hΔ. rewrite {1}/ids.
        rewrite -inst_assoc -lift0_inst lift0_inst_id. lia.
        replace (S i - #|args0|) with (S (i - #|args0|)) by lia.
        econstructor; tea. congruence.
  Qed.
(*
  Lemma pred1_subst_shiftn {Δ Δ' Γ Γ' n s s'} : 
    n = #|Δ'| ->
    pred1_subst (Δ ,,, Δ') Γ Γ' s s' -> 
    pred1_subst Δ Γ Γ' (↑^n ∘s s) (↑^n ∘s s').
  Proof.
    intros hn Hp i.
    specialize (Hp (n + i)) as [IH hnth].
    split => //.
    case: nth_error_spec => /= // x hnth' hi.
    destruct decl_body eqn:db => //. subst n.
    rewrite nth_error_app_ge in hnth; try lia.
    unfold subst_compose, shiftk; simpl.
    replace (#|Δ'| + i - #|Δ'|) with i in hnth by lia.
    now rewrite hnth' /= db in hnth.
  Qed.

  Lemma pred1_subst_ids Δ Γ Γ' :
    pred1_ctx Σ Γ Γ' ->
    pred1_subst Δ Γ Γ' ids ids.
  Proof.
    intros i; split.
    - now eapply pred1_refl_gen.
    - destruct nth_error => /= //.
      destruct decl_body => //.
  Qed.

  Lemma pred1_subst_skipn {Δ Δ' Γ Γ' n s s'} : 
    #|s| = #|s'| ->
    #|Δ'| = n ->
    pred1_ctx Σ Γ Γ' ->
    pred1_subst (Δ ,,, Δ') Γ Γ' (s ⋅n ids) (s' ⋅n ids) -> 
    pred1_subst Δ Γ Γ' (skipn n s ⋅n ids) (skipn n s' ⋅n ids).
  Proof.
    intros.
    destruct (leb_spec_Set (S n) #|s|).
    - eapply pred1_subst_ext.
      1,2:rewrite skipn_subst //; try lia.
      now eapply pred1_subst_shiftn.
    - rewrite !skipn_all2; try lia.
      eapply pred1_subst_ext. 1-2:rewrite subst_consn_nil //.
      now eapply pred1_subst_ids.
  Qed.

  Lemma ctxmap_smash_context Γ Δ s :
    #|s| = context_assumptions Δ ->
    ctxmap (Γ,,, smash_context [] Δ) Γ (s ⋅n ids).
  Proof.
    red. intros hargs x d hnth'.
    destruct (decl_body d) eqn:db => /= //.
    move: hnth'.
    case: nth_error_appP; len => //.
    - intros x' hnths hlen [= ->].
      eapply nth_error_smash_context in hnths => //. congruence.
      intros ? ?; rewrite nth_error_nil => /= //.
    - intros x' hnth cass [= ->].
      rewrite subst_consn_ge. lia.
      unfold ids. eexists _, _. intuition eauto.
      rewrite hargs hnth /= db //.
      apply inst_ext => i.
      unfold shiftk, subst_compose; simpl.
      rewrite subst_consn_ge. lia.
      lia_f_equal.
  Qed.
*)
  Lemma context_assumptions_smash_context' acc Γ : 
    context_assumptions (smash_context acc Γ) = #|smash_context [] Γ| +
    context_assumptions acc.
  Proof.
    induction Γ as [|[na [b|] ty] Γ]; simpl; len; auto;
    rewrite context_assumptions_smash_context; now len.
  Qed.

  Lemma context_assumptions_smash_context''  Γ : 
    context_assumptions (smash_context [] Γ) = #|smash_context [] Γ|.
  Proof.
    rewrite context_assumptions_smash_context' /=; lia.
  Qed.

  Lemma context_assumptions_smash Γ :
    context_assumptions Γ = #|smash_context [] Γ|.
  Proof.
    rewrite -context_assumptions_smash_context''.
    now rewrite context_assumptions_smash_context.
  Qed.

  Lemma All2_fold_over_smash_acc {Γ Γ' Δ Δ'} acc acc' :
    pred1_ctx_over Σ Γ Γ' Δ Δ' ->
    pred1_ctx_over Σ (Γ ,,, Δ) (Γ' ,,, Δ') acc acc' ->    
    pred1_ctx_over Σ Γ Γ' (smash_context acc Δ) (smash_context acc' Δ').
  Proof.
    intros hΔ. revert acc acc'.
    induction hΔ; simpl; auto.
    intros acc acc' h.
    depelim p => /=.
    - eapply IHhΔ.
      eapply All2_fold_app. repeat constructor; auto.
      eapply All2_fold_impl; tea => Γ1 Δ T U; 
      rewrite /on_decls_over => hlen;
      rewrite !app_context_assoc; intuition auto.
    - eapply IHhΔ.
      rewrite /subst_context - !mapi_context_fold.
      eapply All2_fold_mapi.
      eapply All2_fold_impl_ind; tea.
      intros par par' x y onpar; rewrite /on_decls_over /=.
      rewrite !mapi_context_fold - !/(subst_context _ _ _).
      intros pred. rewrite !Nat.add_0_r.
      eapply (@substitution_let_pred1 _ Σ wfΣ (Γ ,,, Γ0) [vdef na b t] par
        (Γ' ,,, Γ'0) [vdef na b' t'] par' [b] [b'] x y) => //; eauto with pcuic.
      * rewrite -{1}(subst_empty 0 b) -{1}(subst_empty 0 b').
        repeat constructor; pcuic. now rewrite !subst_empty.
      * len. move: (length_of onpar).
        move: (length_of (pred1_pred1_ctx _ pred)). len. simpl. len. lia.
      * repeat constructor. pcuic. pcuic.
      * admit.
      * admit.
      * admit.
      * admit.
      * admit.
  Admitted.

  Lemma pred1_ctx_over_smash Γ Γ' Δ Δ' :
    pred1_ctx_over Σ Γ Γ' Δ Δ' ->
    pred1_ctx_over Σ Γ Γ' (smash_context [] Δ) (smash_context [] Δ').
  Proof.
    intros h.
    eapply (All2_fold_over_smash_acc [] []) in h => //.
    constructor.
  Qed.

  Lemma pred1_ext Γ Γ' t t' u u' :
    t = t' -> u = u' -> pred1 Σ Γ Γ' t u -> pred1 Σ Γ Γ' t' u'.
  Proof.
    now intros -> ->.
  Qed.
  
  Lemma pred1_expand_lets Γ Γ' Δ Δ' b b' :
    pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ') b b' ->
    #|Γ| = #|Γ'| ->
    pred1 Σ (Γ ,,, smash_context [] Δ) (Γ' ,,, smash_context [] Δ') 
      (expand_lets Δ b) (expand_lets Δ' b').
  Proof.
    intros pred hlen.
    induction Δ in Γ, Γ', hlen, Δ', b, b', pred |- * using ctx_length_rev_ind.
    - destruct Δ'. simpl. now rewrite !expand_lets_nil.
      eapply pred1_pred1_ctx in pred.
      move: (length_of pred). len. lia.
    - destruct Δ' using rev_case.
      { eapply pred1_pred1_ctx in pred.
        move: (length_of pred). len. lia. }
      pose proof (pred1_pred1_ctx _ pred).
      apply All2_fold_app_inv in X0 as [].
      apply All2_fold_app_inv in a0 as [].
      depelim a0. clear a0.
      all:simpl; auto.
      depelim a1.
      * rewrite !(smash_context_app) /=.
        rewrite !app_context_assoc in pred.
        specialize (X Γ0 ltac:(reflexivity) _ _ _ _ _ pred ltac:(len; lia)).
        now rewrite !expand_lets_vass !app_context_assoc.
      * rewrite !(smash_context_app) /=.
        rewrite !app_context_assoc in pred.
        specialize (X Γ0 ltac:(reflexivity) _ _ _ _ _ pred ltac:(len; lia)).
        rewrite !expand_lets_vdef.
        rewrite (expand_lets_subst_comm Γ0 [b0] b).
        rewrite (expand_lets_subst_comm l [b'0] b').
        eapply substitution_let_pred1 in X. len in X. now exact X.
        + rewrite -{1}(subst_empty 0 b0) -{1}(subst_empty 0 b'0); repeat constructor; pcuic.
          now rewrite !subst_empty.
        + len. now eapply All2_fold_context_assumptions in a2.
        + len. admit.
        + constructor; pcuic. repeat constructor => //.
        + admit.
        + admit.
        + admit.
        + admit.
        + admit.
  Admitted.

  Lemma fold_context_cst ctx : ctx = fold_context (fun _ d => map_decl id d) ctx.
  Proof.
    induction ctx; simpl; auto. 
    now rewrite -IHctx map_decl_id.
  Qed.

  Lemma All2_fold_sym' P (Γ Δ : context) : 
    All2_fold P Γ Δ ->
    All2_fold (fun Δ Γ t' t => P Γ Δ t t') Δ Γ.
  Proof.
    induction 1; constructor; auto; now symmetry.
  Qed.
(* 
  Lemma pred1_ctx_over_rho_right Γ Γ' Δ Δ' :
    pred1_ctx_over Σ Γ Γ' Δ' (rho_ctx_over (rho_ctx Γ) Δ) ->
    All2_fold
      (on_decls
        (on_decls_over
            (fun (Γ0 Γ'0 : context) (t t0 : term) =>
            pred1 Σ Γ0 Γ'0 t0 (rho (rho_ctx Γ0) t)) Γ Γ'))
      Δ Δ'.
  Proof.
    rewrite {1}(fold_context_cst Δ').
    intros h.
    eapply All2_fold_fold_context_inv in h.
    eapply All2_fold_sym' in h.
    eapply All2_fold_impl; tea; clear => /=; 
      rewrite /on_decls /on_decls_over /id => Γ'' Δ'' [[? ?]|] ? ?; 
      simpl; intuition auto.
      rewrite -fold_context_cst in a, b. *)

  Lemma nth_error_fix_context_ass Γ mfix x decl :
    nth_error (rho_ctx_over (rho_ctx Γ) (fix_context mfix)) x = Some decl ->
    decl_body decl = None.
  Proof.
    rewrite (fold_fix_context_rho_ctx xpredT). admit.
    rewrite fold_fix_context_rev_mapi.
    rewrite rev_mapi /= app_nil_r nth_error_mapi.
    now destruct nth_error => /= // => [= <-].
  Admitted.

  Lemma All_decls_on_free_vars_map_impl_inv P Q R f d d' :
    All_decls P d d' ->
    on_free_vars_decl R d ->
    (forall t t', on_free_vars R t -> P t t' -> Q t' (f t)) ->
    All_decls Q d' (map_decl f d).
  Proof.
    move=> [] /=; constructor; auto.
    eapply X; eauto with pcuic.
    now move/andP: H => /= [].
    now move/andP: H => /= [].
  Qed.

  Lemma on_ctx_free_vars_xpredT_snoc d Γ : 
    on_ctx_free_vars xpredT (d :: Γ) =
    on_ctx_free_vars xpredT Γ && on_free_vars_decl xpredT d.
  Proof.
    rewrite -{1}(shiftnP_xpredT (S #|Γ|)).
    now rewrite on_ctx_free_vars_snocS shiftnP_xpredT; bool_congr.
  Qed.

  Hint Resolve pred1_on_free_vars pred1_on_free_vars_ctx : fvs.

  Hint Extern 3 (is_true (on_ctx_free_vars xpredT _)) =>
    rewrite on_ctx_free_vars_xpredT_snoc : fvs.

  Hint Extern 3 (is_true (_ && _)) => apply/andP; idtac : fvs.

  Lemma on_ctx_free_vars_xpredT_skipn Γ n : 
    on_ctx_free_vars xpredT Γ ->
    on_ctx_free_vars xpredT (skipn n Γ).
  Proof.
    rewrite -{1}(firstn_skipn n Γ).
    now rewrite on_ctx_free_vars_app addnP_xpredT => /andP[].
  Qed.

  Lemma eqb_refl {A} `{ReflectEq A} (x : A) : eqb x x.
  Proof.
    case: eqb_spec => //.
  Qed.

  Lemma pred1_ctx_over_refl_gen Γ Γ' Δ :
    pred1_ctx Σ Γ Γ' ->
    pred1_ctx_over Σ Γ Γ' Δ Δ.
  Proof.
    intros H.
    induction Δ as [|[na [b|] ty] Δ]; constructor; auto.
    all:constructor; apply pred1_refl_gen, All2_fold_app => //.
  Qed.

  Lemma on_free_vars_ctx_subst_context s ctx :
    on_free_vars_ctx xpredT ctx ->
    forallb (on_free_vars xpredT) s -> 
    on_free_vars_ctx xpredT (subst_context s 0 ctx).
  Proof.
    intros onctx ons.
    rewrite (on_free_vars_ctx_all_term _ _ Universe.type0).
    rewrite -(subst_it_mkProd_or_LetIn _ _ _ (tSort _)).
    eapply on_free_vars_subst => //.
    now rewrite -on_free_vars_ctx_all_term shiftnP_xpredT.
  Qed.

  Definition fake_params n : context := 
    unfold n (fun x => {| decl_name := {| binder_name := nAnon; binder_relevance := Relevant |};
                          decl_body := None;
                          decl_type := tSort Universe.type0 |}).

  Lemma context_assumptions_fake_params n :
    context_assumptions (fake_params n) = n.
  Proof.
    induction n; simpl; auto. cbn.
    len. now rewrite IHn.
  Qed.
  Hint Rewrite context_assumptions_fake_params : len.

  Lemma rho_inst_case_context Γ Γ' rΓ pars pars' puinst pctx :
    pred1_ctx Σ Γ Γ' ->
    pred1_ctx Σ Γ' rΓ ->
    on_ctx_free_vars xpredT Γ ->
    forallb (on_free_vars xpredT) pars ->
    on_free_vars_ctx (shiftnP #|pars| xpredT) pctx ->
    All2 (fun x y : term =>
        pred1 Σ Γ Γ' x y *
        (on_ctx_free_vars xpredT Γ ->
         on_free_vars xpredT x ->
         forall rΓ, pred1_ctx Σ Γ' rΓ ->
         pred1 Σ Γ' rΓ y (rho rΓ x))) pars pars' ->
    pred1_ctx_over Σ Γ' rΓ 
      (inst_case_context pars' puinst pctx)
      (inst_case_context (map (rho rΓ) pars) puinst pctx).
  Proof.
    intros pr pr' onctx onpars onpctx a.
    assert (clpars' : forallb (on_free_vars xpredT) (List.rev pars')).
    { rewrite forallb_rev //. solve_all. eauto with fvs. }
    rewrite /inst_case_context.
    rewrite !subst_context0_inst_context.
    eapply strong_substitutivity with (P := xpredT) (Q := xpredT).
    instantiate (1 := rΓ ,,, smash_context [] (fake_params #|pars|)).
    instantiate (1 := Γ' ,,, smash_context [] (fake_params #|pars|)).
    eapply All2_fold_app => //.
    now eapply pred1_ctx_over_refl_gen.
    eapply pred1_ctx_over_refl_gen.
    eapply All2_fold_app => //.
    now eapply pred1_ctx_over_refl_gen.
    rewrite on_free_vars_subst_instance_context; tea.
    now rewrite -> shiftnP_xpredT in onpctx.
    erewrite <- on_free_vars_ctx_on_ctx_free_vars.
    erewrite shiftnP_xpredT => //.     
    rewrite -subst_context0_inst_context.
    eapply on_free_vars_ctx_on_ctx_free_vars_xpredT.
    eapply on_free_vars_ctx_subst_context => //.
    rewrite on_free_vars_subst_instance_context //.
    now rewrite -> shiftnP_xpredT in onpctx.
    eapply pred1_subst_consn; tea; eauto with fvs.
    - len. now rewrite (All2_length a).
    - now len.
    - eapply All2_rev, All2_map_right, All2_sym; solve_all.
  Qed.
(* 

  Lemma triangle_inv :
    (forall Γ Δ t u, pred1 Σ Γ Δ t u ->
      on_ctx_free_vars xpredT Γ ->
      on_free_vars xpredT t ->
      forall Δl Δr u',
      Δ = Δl ,,, rho_ctx_over Δl Δr ->
      u = rho Δ u' ->
      pred1 Σ Γ (Δl ,,, Δr) t (rho (Δl ,,, Δr) u')).
  Proof with solve_discr.
    set Pctx := fun (Γ Δ : context) => 
      on_ctx_free_vars xpredT Γ ->
    pred1_ctx Σ Δ (rho_ctx Γ).      
    refine (fst (pred1_ind_all_ctx Σ _ Pctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    intros. admit. admit.

    intros. subst.
      subst Pctx; intros *.

    intros.
    subst.

 *)
   Ltac my_rename_hyp h th :=
    match th with
    | pred1 _ _ _ ?b _ => fresh "pred" b
    | is_true (on_ctx_free_vars _ _) -> _ => fresh "pred" th
    | _ => PCUICParallelReduction.my_rename_hyp h th
    end.

  Ltac rename_hyp h ht ::= my_rename_hyp h ht.
  
  Lemma All2_fold_fold_context_right P f ctx ctx' :
    All2_fold (fun Γ Γ' d d' => P Γ (fold_context_term f Γ') d (map_decl (f (fold_context_term f Γ')) d')) ctx ctx' ->
    All2_fold P ctx (fold_context_term f ctx').
  Proof.
    induction 1; cbn; constructor; auto.
  Qed.

  Lemma All_decls_map_right P d f d' :
    All_decls (fun t t' => P t (f t')) d d' ->
    All_decls P d (map_decl f d').
  Proof.
    case; constructor => //.
  Qed.

  Lemma construct_cofix_discr_match {A} t cstr (cfix : mfixpoint term -> nat -> A) default :
    construct_cofix_discr t = false ->
    match t with
    | tConstruct ind c _ => cstr ind c
    | tCoFix mfix idx => cfix mfix idx
    | _ => default
    end = default.
  Proof.
    destruct t => //.
  Qed.

  Theorem triangle_gen :
    (forall Γ Δ t u, pred1 Σ Γ Δ t u ->
      on_ctx_free_vars xpredT Γ ->
      on_free_vars xpredT t ->
      forall Γ', pred1_ctx Σ Δ Γ' ->
      pred1 Σ Δ Γ' u (rho Γ' t)) ×
    (forall Γ Γ' Δ Δ', 
      pred1_ctx Σ Γ Γ' ->
      pred1_ctx_over Σ Γ Γ' Δ Δ' ->
      on_ctx_free_vars xpredT (Γ ,,, Δ) ->
      forall Γ'0, pred1_ctx Σ Γ' Γ'0 -> 
      pred1_ctx_over Σ Γ' Γ'0 Δ' (rho_ctx_over Γ'0 Δ)).
  Proof with solve_discr.
    set Pctx := fun (Γ Δ : context) => 
      on_ctx_free_vars xpredT Γ ->
      pred1_ctx Σ Δ (rho_ctx Γ).      
    refine (pred1_ind_all_ctx Σ _ Pctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      subst Pctx; intros *.
    all:try intros **; rename_all_hyps;
      try solve [specialize (forall_Γ _ X3); eauto]; eauto;
        try solve [simpl; econstructor; simpl; eauto]; repeat inv_on_free_vars; 
        try rewrite -> shiftnP_xpredT in *; eauto.

    - cbn in *. simpl.
      induction X0; simpl; depelim predΓ'; [constructor|]; rewrite ?app_context_nil_l; simpl; eauto.
      rewrite on_ctx_free_vars_xpredT_snoc => /= /andP[] ond onΓ.
      constructor; auto.
      eapply All_decls_on_free_vars_map_impl_inv; tea.
      cbn. intros t t' ont IH. eauto.

    - (* ctx over *)
      simpl.
      induction X3; simpl; depelim X2; constructor; simpl; 
      unfold on_decls_over in p |- *; intuition auto.
      move: H. rewrite /= on_ctx_free_vars_xpredT_snoc => /andP[] ond onΓ; eauto.
      move: H. rewrite /= on_ctx_free_vars_xpredT_snoc => /andP[] ond onΓ; eauto.
      eapply All_decls_on_free_vars_map_impl_inv; tea; cbn; eauto.
      intros t t' ont IH.
      specialize (IH ond ont). eapply IH.
      eapply All2_fold_app => //. eapply X => //.

    - simpl. rename_all_hyps.
      rewrite (rho_app_lambda _ _ _ _ _ []).
      pose proof (pred1_pred1_ctx _ predt0).
      eapply (substitution0_pred1); simpl in *; eauto; rtoProp; eauto with fvs.
      eapply impl_impl_forall_Γ'; eauto with fvs.
      constructor; eauto. constructor. eauto with fvs. 
      
    - simp rho.
      pose proof (pred1_pred1_ctx _ predt0).
      eapply (substitution0_let_pred1); simpl in *; eauto with fvs.
      eapply pred1_on_free_vars; tea. eauto with fvs.
      eapply impl_impl_forall_Γ'1; eauto with fvs.
      constructor; eauto. constructor; eauto with fvs.

    - simp rho.
      destruct nth_error eqn:Heq. simpl in X0.
      pose proof Heq. apply nth_error_Some_length in Heq.
      destruct c as [na [?|] ?]; noconf heq_option_map.
      simpl in X0.
      assert (on_free_vars xpredT body).
      eapply pred1_on_free_vars_ctx in H0; tea.
      change xpredT with (addnP 0 xpredT) in H0.
      eapply nth_error_on_free_vars_ctx in H0; tea.
      now move/andP: H0.
      eapply (f_equal (option_map decl_body)) in H.
      eapply nth_error_pred1_ctx_l in H; eauto.
      destruct H. intuition. rewrite a. simp rho.
      rewrite -{1}(firstn_skipn (S i) Γ').
      rewrite -{1}(firstn_skipn (S i) Γ'0).
      pose proof (All2_fold_length predΓ'0).
      assert (S i = #|firstn (S i) Γ'|).
      rewrite !firstn_length_le; try lia.
      assert (S i = #|firstn (S i) Γ'0|).
      rewrite !firstn_length_le; try lia.
      rewrite {5}H3 {6}H4.
      eapply pred1_on_free_vars_ctx in predΓ'; tea.
      eapply weakening_pred1_pred1; eauto with fvs.
      eapply All2_fold_over_firstn_skipn. auto.
      erewrite on_ctx_free_vars_xpredT_skipn => //.
      noconf heq_option_map.

    - simp rho. simpl in *.
      destruct option_map eqn:Heq.
      destruct o. constructor; auto.
      constructor. auto.
      constructor. auto.

    - (* iota reduction *)
      simpl in X0. cbn.
      rewrite rho_app_case.
      rewrite decompose_app_mkApps; auto.
      change eq_inductive with (@eqb inductive _).
      destruct (eqb_spec ci.(ci_ind) ci.(ci_ind)); try discriminate.
      2:{ congruence. }
      unfold iota_red. eapply forallb_All in p4. eapply All2_All_mix_left in X3; tea.
      eapply All2_nth_error_Some_right in X3 as [br0 [hnth [hcl [IHbr [[predbod IHbod] breq]]]]]; tea.
      move/andP: hcl => [] clbctx clbod.
      rewrite hnth.
      have fvbrctx : on_ctx_free_vars xpredT (Γ,,, inst_case_branch_context p0 br0).
      {rewrite on_ctx_free_vars_app addnP_xpredT H1 andb_true_r /inst_case_branch_context.
        rewrite on_ctx_free_vars_xpredT. eapply on_free_vars_ctx_inst_case_context; trea. }
      intuition.
      forward X3. now rewrite -> shiftnP_xpredT in clbod.
      rewrite breq -heq_length !List.skipn_length.
      pose proof (All2_length X1).
      rewrite H eqb_refl.
      rewrite !subst_inst.
      assert (forallb (on_free_vars xpredT) args1).
      { solve_all; eauto with fvs. }
      eapply rho_triangle_All_All2_ind_terms in X1. 3:exact predΓ'0. all:tea.
      rewrite /rho_iota_red subst_inst.
      eapply strong_substitutivity.
      + instantiate (2 := (Γ' ,,, smash_context [] (inst_case_branch_context (set_pparams p0 pparams1) br))).
        instantiate (1 := (Γ'0 ,,, smash_context [] (inst_case_branch_context (rho_predicate Γ'0 p0) br0))).
        eapply pred1_expand_lets.
        rewrite /inst_case_branch_context in X3 *. cbn.
        eapply X3. eapply All2_fold_app => //.
        assert (bredctx :
        pred1_ctx_over Σ Γ' Γ'0 (inst_case_branch_context (set_pparams p0 pparams1) br)
          (inst_case_branch_context (rho_predicate Γ'0 p0) br0)).
        { rewrite /inst_case_branch_context /=.
          rewrite -breq.
          eapply rho_inst_case_context; tea. solve_all.
          rewrite test_context_k_closed_on_free_vars_ctx in clbctx.
          eapply on_free_vars_ctx_impl; tea; eauto. intros i.
          rewrite /shiftnP /closedP. destruct Nat.ltb => //. }
        exact bredctx.
        now rewrite (All2_fold_length predΓ'0).
      + eapply on_free_vars_expand_lets_k. reflexivity.
        eapply on_free_vars_ctx_inst_case_context; trea; cbn; solve_all; eauto with fvs.
        rewrite -(All2_length X2) // -breq //. len.
        rewrite -breq.
        eapply pred1_on_free_vars; tea.
        rewrite on_ctx_free_vars_app. len. rewrite addnP_shiftnP H1 andb_true_r.
        relativize #|bcontext br0|; [erewrite on_free_vars_ctx_on_ctx_free_vars|].
        eapply on_free_vars_ctx_inst_case_context; trea; cbn; solve_all; eauto with fvs.
        now len.
      + rewrite -subst_inst.
        eapply on_free_vars_subst. rewrite forallb_rev forallb_skipn //; tea.
        eapply on_free_vars_expand_lets_k => //. len. tea.
        rewrite /inst_case_branch_context.
        eapply on_free_vars_ctx_inst_case_context; trea; len; solve_all. eauto with fvs.
        rewrite -breq -(All2_length X2) //.
        eapply pred1_on_free_vars; tea. 2:len; rewrite -breq //.
        len. rewrite shiftnP_xpredT //.
      + eapply pred1_subst_ext.
        rewrite shiftnP_xpredT. intros i; reflexivity. intros i; reflexivity.
        1-2:sigma; reflexivity.
        eapply All2_skipn in X1.
        eapply All2_rev in X1.
        eapply pred1_subst_consn; tea. eauto with fvs.
        rewrite forallb_rev forallb_skipn //. len. rewrite !List.skipn_length; lia.
        len. rewrite List.skipn_length. rewrite breq. rewrite List.skipn_length in heq_length. lia.
        len. congruence.

    - (* Fix reduction *)
      unfold unfold_fix in heq_unfold_fix |- *.
      rewrite rho_app_fix.
      destruct nth_error eqn:Heq; noconf heq_unfold_fix.
      assert (on_free_vars xpredT (tFix mfix1 idx)).
      { eapply All2_All_mix_left in X3; tea.
        cbn. eapply All_forallb. eapply All2_All_right; tea. cbn.
        intuition auto. destruct a1. 
        move/andP: a0 => [] onty onb.
        rewrite -> shiftnP_xpredT in onb.
        apply/andP; split; eauto with fvs.
        rewrite shiftnP_xpredT.
        eapply pred1_on_free_vars; tea.
        rewrite on_ctx_free_vars_app H1 andb_true_r.
        rewrite -(shiftnP_xpredT #|fix_context mfix0|).
        rewrite on_free_vars_ctx_on_ctx_free_vars.
        eapply on_free_vars_fix_context. solve_all. }
      eapply All2_nth_error_Some_right in Heq; eauto.
      destruct Heq as [t' [Hnth Hrel]].
      destruct Hrel as [[Hty Hrhoty] [[Hreleq0 Hreleq1] Heq]].
      rewrite Hnth. simpl.
      destruct args0. depelim X4. unfold is_constructor in heq_is_constructor.
      rewrite nth_error_nil in heq_is_constructor => //.
      pose proof Hnth as hnth'.
      eapply All2_nth_error_Some in hnth'; eauto.
      destruct hnth' as [fn' [Hnth' [? ?]]].
      destruct t', d.
      noconf Heq. destruct o, p as [[ol ol'] or].
      noconf or. cbn -[map].
      move: heq_is_constructor. cbn -[map].
      revert X4 b. cbn in * |-. generalize (t :: args0). simpl.
      clear t args0. intros args0 Hargs onfvs isc.
      simpl. rewrite isc.
      eapply pred_mkApps.
      rewrite !subst0_inst. eapply PCUICParallelReduction.simpl_pred; [sigma; trea|sigma; trea|].
      rewrite /rho_fix_context -(fold_fix_context_rho_ctx xpredT) //; solve_all.
      move/andP: (nth_error_all Hnth a) => /= [] ondtype ondbody.
      specialize (X0 ondtype); specialize (X2 ondtype).
      assert (onfvfix : on_ctx_free_vars xpredT (Γ,,, fix_context mfix0)).
      { rewrite on_ctx_free_vars_app addnP_xpredT H1 andb_true_r.
        eapply on_free_vars_ctx_on_ctx_free_vars_xpredT.
        eapply on_free_vars_fix_context; solve_all. }
      specialize (Hreleq1 onfvfix).
      rewrite -> shiftnP_xpredT in ondbody. specialize (Hreleq1 ondbody).

      eapply strong_substitutivity; eauto with fvs.
      * eapply Hreleq1. eapply All2_fold_app => //.
        eapply impl_forall_Γ'0; eauto with fvs.
      * rewrite -subst0_inst. eapply on_free_vars_subst.
        eapply (on_free_vars_fix_subst _ _ idx). cbn. solve_all.
        eapply pred1_on_free_vars; tea; now rewrite shiftnP_xpredT.
      * rewrite -(rho_fix_subst xpredT). solve_all.
        eapply All2_prop2_eq_split in X3.
        eapply (pred_subst_rho_fix xpredT); intuition auto. solve_all.
        eauto with fvs. clear b0. solve_all. unfold on_Trel in *. intuition auto.
        clear b0; solve_all. eapply X4; eauto.
        now move/andP: a0 => []. solve_all. unfold on_Trel in *.
        intuition eauto with fvs. apply X4.
        move/andP: a0 => []. now rewrite shiftnP_xpredT.
        eapply All2_fold_app => //. eapply X3; eauto.
      * eapply forallb_All in onfvs. eapply All2_All_mix_left in Hargs; tea.
        eapply All2_sym, All2_map_left, All2_impl; eauto. simpl.
        intuition eauto.

    - (* Case-CoFix reduction *)
      rewrite rho_app_case.
      rewrite decompose_app_mkApps; auto.
      unfold unfold_cofix in heq_unfold_cofix |- *.
      destruct nth_error eqn:Heq; noconf heq_unfold_cofix. simpl.
      eapply All2_prop2_eq_split in X3. intuition.
      eapply All2_nth_error_Some_right in Heq; eauto.
      destruct Heq as [t' [Ht' Hrel]]. rewrite Ht'. simpl.
      unfold on_Trel in *. destruct Hrel.
      assert (oninst : on_ctx_free_vars xpredT (Γ,,, PCUICCases.inst_case_predicate_context p0)).
      { rewrite on_ctx_free_vars_app H2 andb_true_r.
        rewrite on_ctx_free_vars_xpredT.
        eapply on_free_vars_ctx_inst_case_context; trea. }
      forward impl_forall_Γ'1 by tas.
      intuition auto. 
      assert (predctx :
         pred1_ctx_over Σ Γ' Γ'0 (PCUICCases.inst_case_predicate_context p1)
          (PCUICCases.inst_case_predicate_context (rho_predicate Γ'0 p0))).
      { rewrite /PCUICCases.inst_case_predicate_context /=.
        rewrite -heq_puinst -heq_pcontext.
        eapply rho_inst_case_context; tea.
        rewrite test_context_k_closed_on_free_vars_ctx in p3.
        eapply on_free_vars_ctx_impl; tea; eauto. intros i.
        rewrite /shiftnP /closedP. destruct Nat.ltb => //. }
      
      eapply pred_case; simpl; eauto.
      * eapply All2_sym, All2_map_left. solve_all.
      * eapply All2_fold_app in predctx => //.
        exact (X2 _ predctx).
      * eapply All2_sym, All2_map_left.
        eapply forallb_All in p5.
        eapply All2_All_mix_left in X9; tea.
        eapply (All2_impl X9). cbn; move=> x y [] /andP[] clbctx clbbody [].
        assert (on_ctx_free_vars xpredT (Γ,,, inst_case_branch_context p0 x)).
        { rewrite on_ctx_free_vars_app addnP_xpredT H2 andb_true_r.
          rewrite /inst_case_branch_context.
          eapply on_free_vars_ctx_on_ctx_free_vars_xpredT.
          eapply on_free_vars_ctx_inst_case_context; trea; solve_all. }
        rewrite -> shiftnP_xpredT in clbbody.
        move/(_ H) => IHctx [] [] pbody /(_ H clbbody) IHbbody eqctx.
        assert (bredctx :
          pred1_ctx_over Σ Γ' Γ'0 (inst_case_branch_context p1 y)
            (inst_case_branch_context (rho_predicate Γ'0 p0) x)).
        { rewrite /inst_case_branch_context /=.
          rewrite -heq_puinst -eqctx.
          eapply rho_inst_case_context; tea. solve_all.
          rewrite test_context_k_closed_on_free_vars_ctx in clbctx.
          eapply on_free_vars_ctx_impl; tea; eauto. intros i.
          rewrite /shiftnP /closedP. destruct Nat.ltb => //. }
        repeat split => //.
        eapply IHbbody.
        eapply All2_fold_app => //.
      * eapply pred_mkApps.
        rewrite -(fold_fix_context_rho_ctx xpredT).
        set (rhoΓ := rho_ctx Γ ,,, rho_ctx_over (rho_ctx Γ) (fix_context mfix0)) in * => //.
        solve_all.
        rewrite !subst_inst. eapply PCUICParallelReduction.simpl_pred; try now sigma.
        assert (on_ctx_free_vars xpredT (Γ,,, fix_context mfix0)).
        { rewrite on_ctx_free_vars_app addnP_xpredT H2 andb_true_r.
          erewrite on_free_vars_ctx_on_ctx_free_vars_xpredT => //.
          now eapply on_free_vars_fix_context. }
        assert (on_free_vars xpredT (dbody t')).
        {eapply nth_error_all in a; tea.
          move/andP: a => []. now rewrite shiftnP_xpredT. }
        assert (forallb (test_def (on_free_vars xpredT) (on_free_vars (shiftnP #|mfix1| xpredT))) mfix1).
        { eapply All2_prod in a1; tea. solve_all; eauto with fvs. inv_on_free_vars.
          apply/andP; split; eauto with fvs. rewrite shiftnP_xpredT; eauto with fvs. }
        eapply strong_substitutivity; eauto; tea.
        + eapply p6; tea; eauto with fvs.
          eapply All2_fold_app => //. eapply impl_forall_Γ'0; eauto with fvs.
        + eauto with fvs.
        + rewrite -subst0_inst. eapply on_free_vars_subst.
          eapply (on_free_vars_cofix_subst _ _ idx); cbn; tea. len.
          eapply pred1_on_free_vars; tea; rewrite shiftnP_xpredT //.
        + rewrite -(rho_cofix_subst xpredT) //. solve_all.
          eapply pred_subst_rho_cofix; tea; auto. solve_all. eauto with fvs.
          eapply All2_All_mix_left in a1; tea.
          eapply (All2_impl a1); solve_all. inv_on_free_vars.
          solve_all. unfold on_Trel in *; solve_all.
          solve_all. unfold on_Trel in *; solve_all. inv_on_free_vars.
          eapply X3; eauto with fvs. now rewrite -> shiftnP_xpredT in b1.
          eapply All2_fold_app => //.
          eapply X0 => //.
        + eapply forallb_All in b. eapply All2_All_mix_left in X4; tea.
          eapply All2_sym, All2_map_left, All2_impl; eauto. simpl. intuition eauto.
          
    - (* Proj-Cofix reduction *)
      simpl. cbn in H1; inv_on_free_vars. cbn in a.
      assert (on_ctx_free_vars xpredT (Γ,,, fix_context mfix0)).
      { rewrite on_ctx_free_vars_app addnP_xpredT H0 andb_true_r.
        erewrite on_free_vars_ctx_on_ctx_free_vars_xpredT => //.
        eapply on_free_vars_fix_context; solve_all. }
      assert (forallb (test_def (on_free_vars xpredT) (on_free_vars (shiftnP #|mfix1| xpredT))) mfix1).
      { red in X3. solve_all; eauto with fvs. inv_on_free_vars. unfold on_Trel in *. solve_all.
        apply/andP; split; eauto with fvs. rewrite shiftnP_xpredT; eauto with fvs. }
      destruct p as [[ind pars] arg].
      rewrite rho_app_proj.
      rewrite decompose_app_mkApps. auto.
      unfold unfold_cofix in heq_unfold_cofix |- *.
      destruct nth_error eqn:Heq; noconf heq_unfold_cofix.
      eapply All2_nth_error_Some_right in Heq; eauto.
      destruct Heq as [t' [Hnth Hrel]]. destruct Hrel as [[Hty Hrhoty] [[Hreleq0 Hreleq1] Heq]].
      assert (on_free_vars xpredT (dbody t')).
      { solve_all. eapply nth_error_all in a; tea.
        move/andP: a => []. now rewrite shiftnP_xpredT. }
      assert (on_free_vars xpredT (dtype t')).
      { solve_all. eapply nth_error_all in a; tea.
        now move/andP: a => []. }
      assert (on_free_vars xpredT (dbody d)).
      { eauto with fvs. }
      unfold map_fix. rewrite Hnth /=.
      econstructor. eapply pred_mkApps; eauto.
      rewrite - (fold_fix_context_rho_ctx xpredT) //.
      rewrite !subst0_inst. eapply strong_substitutivity; tea.
      + eapply Hreleq1; eauto with fvs.
        eapply All2_fold_app => //.
        eapply impl_forall_Γ'0; eauto with fvs.
      + rewrite -subst0_inst.
        eapply on_free_vars_subst; eauto with fvs.
        eapply (on_free_vars_cofix_subst _ _ idx); eauto with fvs.
        rewrite shiftnP_xpredT //.
      + rewrite -(rho_cofix_subst xpredT) //.  
        red in X3. eapply (pred_subst_rho_cofix xpredT) => //; solve_all; unfold on_Trel in *; eauto with fvs.
        inv_on_free_vars. solve_all. inv_on_free_vars. solve_all.
        
        eapply X0; eauto with fvs. now rewrite -> shiftnP_xpredT in b1.
        eapply All2_fold_app => //. solve_all.
      + eapply forallb_All in b;eapply All2_All_mix_left in X4; tea.
        eapply All2_sym, All2_map_left; solve_all.

    - simpl; simp rho; simpl.
      simpl in X0. red in H. rewrite H /= heq_cst_body /=.
      now eapply pred1_refl_gen.

    - simpl in *. simp rho; simpl.
      destruct (lookup_env Σ c) eqn:Heq; pcuic. destruct g; pcuic.
      destruct cst_body eqn:Heq'; pcuic.
      
    - simpl in *. inv_on_free_vars. rewrite rho_app_proj.
      rewrite decompose_app_mkApps; auto.
      change eq_inductive with (@eqb inductive _).
      destruct (eqb_spec i i) => //.
      eapply All2_nth_error_Some_right in heq_nth_error as [t' [? ?]]; eauto.
      simpl in y. rewrite e0. simpl.
      auto. eapply y => //. 
      eapply nth_error_forallb in b; tea.
    
    - simpl; simp rho. eapply pred_abs; auto.
      eapply impl_impl_forall_Γ'0; eauto with fvs.
      constructor; eauto with fvs. constructor; eauto with fvs.

    - (** Application *)
      simp rho.
      assert (onΓ' : on_ctx_free_vars xpredT Γ').
      { pose proof (pred1_pred1_ctx _ predM0). eauto with fvs. }
      rename impl_impl_forall_Γ' into IHM1.
      rename impl_impl_forall_Γ'0 into IHN1.
      intuition auto. specialize (X1 _ predΓ'0).
      specialize (X _ predΓ'0).
      destruct view_lambda_fix_app. simp rho. simpl; simp rho.
      + (* Fix at head *)
        inv_on_free_vars. cbn in a.
        assert (onΓmfix : on_ctx_free_vars xpredT (Γ,,, fix_context mfix)).
        { rewrite on_ctx_free_vars_app addnP_xpredT H andb_true_r.
          erewrite on_free_vars_ctx_on_ctx_free_vars_xpredT => //.
          apply on_free_vars_fix_context. solve_all. }

        destruct (rho_fix_elim Γ'0 mfix i l).
        * rewrite /unfold_fix {1}/map_fix nth_error_map e /=. 
          eapply (is_constructor_app_ge (rarg d) _ _) in i0 => //.
          rewrite -> i0.
          rewrite map_app - !mkApps_nested.
          eapply (pred_mkApps _ _ _ _ _ [N1]) => //.
          rewrite - (fold_fix_context_rho_ctx xpredT) //.
          rewrite (rho_fix_subst xpredT) => //. subst fn.
          rewrite (fold_fix_context_rho_ctx xpredT) //.
          repeat constructor; auto.
        * simp rho in X1.
          simpl in X1. simp rho in X1.
          destruct (rho_fix_elim Γ'0 mfix i (l ++ [a0])).
          (* Shorter application does not reduce *)
          ** (* Longer application reduces *)
            rewrite e in i0.
            rewrite /unfold_fix nth_error_map e /= i1.
            simpl.
            destruct (pred1_mkApps_tFix_inv _ _ _ _ _ _ _ _ e i0 predM0) as
              [mfix1 [args1 [[HM1 Hmfix] Hargs]]].
            subst M1.
            rewrite [tApp _ _](mkApps_nested _ _ [N1]).
            red in Hmfix.
            eapply All2_nth_error_Some in Hmfix; eauto.
            destruct Hmfix as [d' [Hd' [eqd' [pred' eqsd']]]].
            eapply (pred1_mkApps_tFix_refl_inv _ _ _ mfix1) in X1; eauto.
            2:{ noconf eqsd'.
                rewrite -H1.
                pose proof (All2_length Hargs).
                unfold is_constructor in i1.
                move: i1 i0.
                elim: nth_error_spec => //.
                rewrite app_length; intros x hnth. simpl.
                unfold is_constructor.
                elim: nth_error_spec => // x' hnth' rargl rargsl.
                destruct (eq_dec (rarg d) #|l|). lia.
                rewrite nth_error_app_lt in hnth. lia. rewrite hnth in hnth'.
                noconf hnth'. intros. rewrite i1 in i0 => //.
                destruct (nth_error args1 (rarg d)) eqn:hnth'' => //.
                eapply nth_error_Some_length in hnth''. lia. }
            move: X1 => [redo redargs].
            rewrite map_app.
            assert (forallb (test_def (on_free_vars xpredT) (on_free_vars (shiftnP #|mfix1| xpredT))) mfix1).
            { eapply pred1_mkApps_tFix_refl_inv in predM0 as []; tea.
              red in a1. eapply forallb_All in a.
              eapply All2_All_mix_left in a1; tea. solve_all.
              inv_on_free_vars. unfold on_Trel in *; apply /andP; split; eauto with fvs.
              rewrite shiftnP_xpredT //. eapply pred1_on_free_vars; tea.
              destruct (is_constructor (rarg d) l) => //. }
            eapply pred_fix; eauto with pcuic.
            eapply pred1_rho_fix_context_2; eauto with pcuic fvs.
            red in redo.
            solve_all.
            unfold on_Trel in *. intuition auto. now noconf b0.
            unfold unfold_fix. rewrite nth_error_map e /=.
            rewrite map_fix_subst /= //.
            intros n.  simp rho; simpl; now simp rho.
            move: i1.
            eapply is_constructor_pred1.
            eapply All2_app; eauto.
            eapply All2_app => //. repeat constructor; auto. 

          ** (* None reduce *)
            simpl. rewrite map_app.
            rewrite /unfold_fix nth_error_map.
            destruct nth_error eqn:hnth => /=.
            destruct (is_constructor (rarg d) (l ++ [a0])) => //.
            rewrite -mkApps_nested.
            apply (pred_mkApps _ _ _ _ _ [N1] _). auto.
            repeat constructor; auto.
            rewrite -mkApps_nested.
            apply (pred_mkApps _ _ _ _ _ [N1] _). auto.
            repeat constructor; auto.

      + (* Beta at top *)
        rewrite rho_app_lambda' in X1. inv_on_free_vars.
        destruct l. simpl in *.
        depelim predM0; solve_discr.
        simp rho in X1. 
        depelim X1... econstructor; eauto.
        simpl. simp rho.
        rewrite map_app -mkApps_nested.
        constructor; eauto.
        
      + (* No head redex *)
        simpl. constructor; auto.

    - simpl; simp rho; simpl. eapply pred_zeta; eauto with fvs.
      eapply impl_impl_forall_Γ'1; eauto with fvs.
      do 2 (constructor; eauto with fvs).
      
    - (* Case reduction *)
      rewrite rho_app_case.
      have hpars : (All2 (pred1 Σ Γ' Γ'0) (pparams p1)
        (map (rho Γ'0) (pparams p0))).
      { eapply All2_sym, All2_map_left; solve_all. }
      have hbrs : All2
       (fun br br' : branch term =>
       on_Trel_eq (pred1 Σ (Γ',,, inst_case_branch_context p1 br)
         (Γ'0,,, inst_case_branch_context (rho_predicate Γ'0 p0) br')) bbody bcontext br br') brs1 
        (map (rho_br Γ'0 (rho_predicate Γ'0 p0)) brs0).
      { eapply All2_sym, All2_map_left; solve_all.
        assert (on_ctx_free_vars xpredT (Γ,,, inst_case_branch_context p0 x)).
        { rewrite on_ctx_free_vars_app addnP_xpredT H1 andb_true_r.
          rewrite /inst_case_branch_context.
          eapply on_free_vars_ctx_on_ctx_free_vars_xpredT.
          eapply on_free_vars_ctx_inst_case_context; trea; solve_all. }
        eapply b0 => //.
        now rewrite -> shiftnP_xpredT in H0.
        assert (bredctx :
          pred1_ctx_over Σ Γ' Γ'0 (inst_case_branch_context p1 y)
            (inst_case_branch_context (rho_predicate Γ'0 p0) x)).
        { rewrite /inst_case_branch_context /=.
          rewrite -heq_puinst -b.
          eapply rho_inst_case_context; tea. solve_all.
          rewrite test_context_k_closed_on_free_vars_ctx in H.
          eapply on_free_vars_ctx_impl; tea; eauto. intros i.
          rewrite /shiftnP /closedP. destruct Nat.ltb => //. solve_all. }
        eapply All2_fold_app => //. }
      have pred_pred_ctx : 
        pred1_ctx_over Σ Γ' Γ'0 (PCUICCases.inst_case_predicate_context p1)
            (PCUICCases.inst_case_predicate_context (rho_predicate Γ'0 p0)).
      { rewrite /PCUICCases.inst_case_predicate_context /=.
        rewrite -heq_pcontext -heq_puinst.
        eapply rho_inst_case_context; tea. solve_all.
        rewrite test_context_k_closed_on_free_vars_ctx in p3.
        eapply on_free_vars_ctx_impl; tea; eauto. intros i.
        rewrite /shiftnP /closedP. destruct Nat.ltb => //. }
      assert (on_ctx_free_vars xpredT (Γ,,, inst_case_context (pparams p0) (puinst p0) (pcontext p0))).
      { rewrite on_ctx_free_vars_app addnP_xpredT H1 andb_true_r.
        eapply on_free_vars_ctx_on_ctx_free_vars_xpredT.
        eapply on_free_vars_ctx_inst_case_context; trea; solve_all. }
      destruct (decompose_app c0) eqn:Heq. cbn -[eqb]. 
      eapply All2_fold_app in pred_pred_ctx.
      specialize (impl_impl_forall_Γ' H p2 _ pred_pred_ctx) as Hpret.
      specialize (impl_forall_Γ'0 H _ predΓ'0) as Hpctx.
      specialize (impl_impl_forall_Γ'0 H1 p4 _ predΓ'0) as Hc.
      destruct (construct_cofix_discr t) eqn:Heq'.
  
      destruct t; noconf Heq'.
      + (* Iota *)
        apply decompose_app_inv in Heq.
        subst c0. cbn -[eqb].
        simp rho.
        change eq_inductive with (@eqb inductive _).
        destruct (eqb_spec ci.(ci_ind) ind). subst ind.
        destruct (nth_error brs0 n) eqn:hbr => //.
        case: eqb_spec => [eq|neq].
        eapply pred1_mkApps_tConstruct in predc0 as [args' [? ?]]; pcuic. subst c1.
        intuition auto.
        rewrite rho_app_construct in Hc.
        eapply pred1_mkApps_refl_tConstruct in Hc.
        eapply PCUICParallelReduction.simpl_pred; revgoals. 3:reflexivity.
        econstructor. 1-2:tea.
        * erewrite nth_error_map, hbr. instantiate (1 := rho_br Γ'0 (rho_predicate Γ'0 p0) b).
          reflexivity.
        * now len.
        * solve_all.
        * solve_all. eapply All2_fold_app_inv => //. rewrite -heq_puinst.
          now eapply pred1_pred1_ctx in a0. apply (All2_fold_length predΓ'0).
          now rewrite -heq_puinst b0.
        * rewrite /rho_iota_red /iota_red /= /set_pparams /= /inst_case_branch_context /=.
          rewrite heq_puinst. reflexivity.
        * econstructor; eauto. eapply All2_fold_app_inv => //.
          apply (All2_fold_length predΓ'0). solve_all.
          eapply pred1_pred1_ctx in a. eapply All2_fold_app_inv => //.
          apply (All2_fold_length predΓ'0).
          simp rho in Hc.
        * econstructor; eauto. eapply All2_fold_app_inv => //.
          apply (All2_fold_length predΓ'0). solve_all.
          eapply pred1_pred1_ctx in a. eapply All2_fold_app_inv => //.
          apply (All2_fold_length predΓ'0).
          simp rho in Hc.
        * econstructor; eauto. eapply All2_fold_app_inv => //.
          apply (All2_fold_length predΓ'0). solve_all.
          eapply pred1_pred1_ctx in a. eapply All2_fold_app_inv => //.
          apply (All2_fold_length predΓ'0).
          simp rho in Hc.
        
      + (* CoFix *)
        apply decompose_app_inv in Heq.
        subst c0. simpl. simp rho.
        assert (forallb (test_def (on_free_vars xpredT) (on_free_vars (shiftnP #|mfix| xpredT))) mfix).
        { now inv_on_free_vars. }
        assert (onΓmfix: on_ctx_free_vars xpredT (Γ,,, fix_context mfix)).
        { rewrite on_ctx_free_vars_app addnP_xpredT H1 andb_true_r.
          erewrite on_free_vars_ctx_on_ctx_free_vars_xpredT => //.
          apply on_free_vars_fix_context. solve_all. }
        simpl.
        simp rho in Hc.
        eapply pred1_mkApps_tCoFix_inv in predc0 as [mfix' [idx' [[? ?] ?]]].
        subst c1.
        assert (forallb (test_def (on_free_vars xpredT) (on_free_vars (shiftnP #|mfix'| xpredT))) mfix').
        { eapply forallb_All in H0. eapply All2_All_mix_left in a; tea. solve_all. inv_on_free_vars.
          inv_on_free_vars. inv_on_free_vars.
          apply/andP; split; eauto with fvs. rewrite shiftnP_xpredT; eauto with fvs. }
        simpl in Hc. eapply pred1_mkApps_tCoFix_refl_inv in Hc.
        intuition.
        eapply All2_prop2_eq_split in a1. intuition.
        unfold unfold_cofix.
        assert (All2 (on_Trel eq dname) mfix'
                    (map_fix rho Γ'0 (fold_fix_context rho Γ'0 [] mfix) mfix)).
        { eapply All2_impl; [eapply b0|]; pcuic. }
        pose proof (All2_mix a1 X0).
        eapply pred1_rho_fix_context_2 in X7; eauto with fvs.
        
        rewrite - (fold_fix_context_rho_ctx xpredT) // in X7.
        rewrite (fix_context_map_fix xpredT) // in X7.
        eapply rho_All_All2_fold_inv in X7; pcuic.
        rewrite /rho_fix_context - (fold_fix_context_rho_ctx xpredT) // in a1.
        
        eapply All2_fold_app_inv in pred_pred_ctx as []. 2:eapply (All2_fold_length predΓ'0).
        destruct nth_error eqn:Heq. simpl.
        * (* CoFix unfolding *)
          pose proof Heq.
          eapply All2_nth_error_Some in Heq; eauto. destruct Heq; intuition auto.
          eapply pred_cofix_case with 
            (map_fix rho Γ'0 (rho_ctx_over Γ'0 (fix_context mfix)) mfix) (rarg d); pcuic.

          -- rewrite (fix_context_map_fix xpredT) //.
             eapply All2_fold_fold_context_right.
             eapply PCUICEnvironment.All2_fold_impl; tea. solve_all.
             eapply All_decls_map_right.
             eapply All_decls_impl; tea. solve_all.

          -- eapply All2_mix; pcuic.
            rewrite /rho_fix_context -(fold_fix_context_rho_ctx xpredT) // in b1.
            eapply All2_mix. eauto.
            now rewrite /rho_fix_context -(fold_fix_context_rho_ctx xpredT) in b0.
          -- unfold unfold_cofix.
              rewrite nth_error_map.
              rewrite H3. simpl. f_equal. f_equal.
              unfold map_fix.
              rewrite (fold_fix_context_rho_ctx xpredT) //.
              rewrite (map_cofix_subst _ (fun Γ Γ' => rho (Γ ,,,  Γ'))) //.
              intros. simp rho; simpl; simp rho. reflexivity.
          -- eapply All2_mix; pcuic.
             eapply All2_prod_inv in hbrs as [].
             eapply (All2_impl a7); solve_all.
             eapply All2_fold_app_inv => //.
             now eapply pred1_pred1_ctx in X8.
             apply (All2_fold_length predΓ'0).
          
        * eapply pred_case; simpl; eauto; solve_all.
          eapply pred1_pred1_ctx in a4. eapply All2_fold_app_inv in a4 as [] => //.
          now apply (All2_fold_length predΓ'0).
          eapply pred_mkApps. constructor. pcuic.
          --- rewrite /rho_fix_context -(fold_fix_context_rho_ctx xpredT) //. solve_all.
              rewrite (fix_context_map_fix xpredT) //. solve_all.
              eapply All2_fold_fold_context_right.
              eapply PCUICEnvironment.All2_fold_impl; tea. solve_all.
              eapply All_decls_map_right.
              eapply All_decls_impl; tea. solve_all.
 
          --- eapply All2_mix; pcuic.
              eapply All2_prod_inv in a1 as [].
              rewrite /rho_fix_context -(fold_fix_context_rho_ctx xpredT) //. solve_all.
              eapply All2_mix; pcuic.
          --- pcuic.
          
      + apply decompose_app_inv in Heq. subst c0.
        rewrite construct_cofix_discr_match //.
        econstructor; cbn; tea; auto.
        eapply All2_fold_app_inv => //. eapply (All2_fold_length predΓ'0).
        solve_all.
        eapply pred1_pred1_ctx in a.
        eapply All2_fold_app_inv => //. apply (All2_fold_length predΓ'0).

      + tas.

    - (* Proj *)
      simpl.
      destruct p as [[ind pars] arg].
      rewrite rho_app_proj.
      specialize (impl_impl_forall_Γ' H H0 _ predΓ'0).
      rename impl_impl_forall_Γ' into Hc.
      assert (onΓ' : on_ctx_free_vars xpredT Γ').
      { eapply pred1_pred1_ctx in predc; eauto with fvs. }
      destruct decompose_app eqn:Heq.
      destruct (view_construct0_cofix t).
      + apply decompose_app_inv in Heq.
        subst c. simpl.
        simp rho in Hc |- *.
        pose proof (pred1_pred1_ctx _ Hc).
        eapply pred1_mkApps_tConstruct in predc as [args' [? ?]]; subst.
        eapply pred1_mkApps_refl_tConstruct in Hc.
        destruct nth_error eqn:Heq.
        change eq_inductive with (@eqb inductive _).
        destruct (eqb_spec ind ind0); subst.
        econstructor; eauto.
        now rewrite nth_error_map Heq.
        eapply pred_proj_congr, pred_mkApps; auto with pcuic.
        destruct eq_inductive. constructor; auto.
        eapply pred_mkApps; auto.
        econstructor; eauto.
        constructor; auto.
        eapply pred_mkApps; auto.
        econstructor; eauto.
        
      + apply decompose_app_inv in Heq.
        subst c. simpl.
        simp rho in Hc |- *.
        eapply pred1_mkApps_tCoFix_inv in predc as [mfix' [idx' [[? ?] ?]]].
        subst c'. simpl in a. pose proof Hc.
        eapply pred1_mkApps_tCoFix_refl_inv in X.
        destruct X.
        unfold unfold_cofix.
        eapply All2_prop2_eq_split in a1. intuition auto.
        assert (All2 (on_Trel eq dname) mfix'
                    (map_fix rho Γ'0 (fold_fix_context rho Γ'0 [] mfix) mfix)).
        { eapply All2_impl; [eapply b|]; pcuic. }
        cbn in H0; inv_on_free_vars; cbn in a3.
        assert (onΓmfix: on_ctx_free_vars xpredT (Γ,,, fix_context mfix)).
        { rewrite on_ctx_free_vars_app addnP_xpredT H andb_true_r.
          erewrite on_free_vars_ctx_on_ctx_free_vars_xpredT => //.
          apply on_free_vars_fix_context. solve_all. }
        simpl.
        simp rho in Hc.
        assert (forallb (test_def (on_free_vars xpredT) (on_free_vars (shiftnP #|mfix'| xpredT))) mfix').
        { eapply forallb_All in a3.
          eapply All2_All_mix_left in a; tea. solve_all. unfold on_Trel in *; inv_on_free_vars.
          apply/andP; split; eauto with fvs. rewrite shiftnP_xpredT; eauto with fvs. }
        pose proof (All2_mix a1 X) as X2.
        eapply pred1_rho_fix_context_2 in X2; pcuic; tea.
        rewrite -(fold_fix_context_rho_ctx xpredT) // in X2.
        rewrite (fix_context_map_fix xpredT) // in X2.
        eapply rho_All_All2_fold_inv in X2; pcuic.
        rewrite /rho_fix_context -(fold_fix_context_rho_ctx xpredT) // in a1.
        intuition auto.
        destruct nth_error eqn:Heq. simpl.
        (* Proj cofix *)
        * (* CoFix unfolding *)
          pose proof Heq.
          eapply All2_nth_error_Some in Heq; eauto. destruct Heq; intuition auto.

          eapply pred_cofix_proj with (map_fix rho Γ'0 (rho_ctx_over Γ'0 (fix_context mfix)) mfix) (rarg d); pcuic.
          -- rewrite (fix_context_map_fix xpredT) //.
             eapply All2_fold_fold_context_right.
             eapply PCUICEnvironment.All2_fold_impl; tea. solve_all.
             eapply All_decls_map_right.
             eapply All_decls_impl; tea. solve_all.

          -- eapply All2_mix; pcuic.
             rewrite /rho_fix_context -(fold_fix_context_rho_ctx xpredT) // in b0.
             eapply All2_mix. eauto.
             now rewrite /rho_fix_context -(fold_fix_context_rho_ctx xpredT) // in b.
          -- unfold unfold_cofix.
             rewrite nth_error_map.
             rewrite H1. simpl. f_equal. f_equal.
             unfold map_fix.
             rewrite (fold_fix_context_rho_ctx xpredT) //. 
             rewrite (map_cofix_subst _ (fun Γ Γ' => rho (Γ ,,,  Γ'))) //.
             intros. simp rho; simpl; simp rho. reflexivity.

        * eapply pred_proj_congr; eauto.

      + eapply decompose_app_inv in Heq. subst c.
        destruct t; noconf d; try solve [econstructor; eauto].
        destruct n; [easy|].
        econstructor; eauto.

    - simp rho; simpl; simp rho.
      cbn in X0. intuition auto.
      assert (on_ctx_free_vars xpredT (Γ,,, fix_context mfix0)).
      { rewrite on_ctx_free_vars_app addnP_xpredT H andb_true_r.
        erewrite on_free_vars_ctx_on_ctx_free_vars_xpredT => //.
        apply on_free_vars_fix_context. solve_all. }
      intuition auto. specialize (X0 _ predΓ'0).
      rewrite /rho_fix_context -(fold_fix_context_rho_ctx xpredT) //; solve_all.
      constructor; eauto.
      { rewrite (fix_context_map_fix xpredT) //; solve_all. }
      red. red in X3.
      eapply All2_sym, All2_map_left.
      eapply All2_All_mix_left in X3; tea; eapply All2_impl; tea. unfold on_Trel.
      intros; cbn; intuition auto; inv_on_free_vars; eauto with fvs.
      rewrite (fix_context_map_fix xpredT) //; solve_all.
      eapply X4. now rewrite -> shiftnP_xpredT in b.
      eapply All2_fold_app => //.

    - simp rho; simpl; simp rho.
      cbn in X0. intuition auto.
      assert (on_ctx_free_vars xpredT (Γ,,, fix_context mfix0)).
      { rewrite on_ctx_free_vars_app addnP_xpredT H andb_true_r.
        erewrite on_free_vars_ctx_on_ctx_free_vars_xpredT => //.
        apply on_free_vars_fix_context. solve_all. }
      intuition auto. specialize (X0 _ predΓ'0).
      rewrite /rho_fix_context -(fold_fix_context_rho_ctx xpredT) //; solve_all.
      constructor; eauto.
      { rewrite (fix_context_map_fix xpredT) //; solve_all. }
      red. red in X3.
      eapply All2_sym, All2_map_left.
      eapply All2_All_mix_left in X3; tea; eapply All2_impl; tea. unfold on_Trel.
      intros; cbn; intuition auto; inv_on_free_vars; eauto with fvs.
      rewrite (fix_context_map_fix xpredT) //; solve_all.
      eapply X4. now rewrite -> shiftnP_xpredT in b.
      eapply All2_fold_app => //.

    - simp rho; simpl; econstructor; eauto with fvs.
      intuition auto. eapply impl_impl_forall_Γ'0; tea; eauto with fvs.
      do 2 (constructor; eauto with fvs).
    - simpl in *. simp rho. constructor. eauto.
      eapply All2_All_mix_left in X1; tea.
      eapply All2_sym, All2_map_left, All2_impl; tea => /=; intuition auto.
    - destruct t; noconf H; simpl; constructor; eauto.
  Qed.

  Corollary triangle {Γ Δ t u} :
    on_ctx_free_vars xpredT Γ ->
    on_free_vars xpredT t ->
    pred1 Σ Γ Δ t u ->
    pred1 Σ Δ (rho_ctx Γ) u (rho (rho_ctx Γ) t).
  Proof.
    intros. eapply triangle_gen; tea.
    eapply pred1_pred1_ctx in X.
    induction X; simpl. constructor.
    move: H; rewrite on_ctx_free_vars_xpredT_snoc => /= /andP[] ond onΓ.
    constructor; auto.
    eapply All_decls_on_free_vars_map_impl_inv; tea.
    cbn. intros ? ? ont IH. eapply triangle_gen; eauto.
  Qed.

End Rho.

Notation fold_context_term f := (fold_context (fun Γ' => map_decl (f Γ'))).
Notation rho_ctx Σ := (fold_context_term (rho Σ)).

(* The diamond lemma for parallel reduction follows directly from the triangle lemma. *)

Corollary pred1_diamond {cf : checker_flags} {Σ : global_env} {wfΣ : wf Σ} {Γ Δ Δ' t u v} :
  on_ctx_free_vars xpredT Γ ->
  on_free_vars xpredT t ->
  pred1 Σ Γ Δ t u ->
  pred1 Σ Γ Δ' t v ->
  pred1 Σ Δ (rho_ctx Σ Γ) u (rho Σ (rho_ctx Σ Γ) t) *
  pred1 Σ Δ' (rho_ctx Σ Γ) v (rho Σ (rho_ctx Σ Γ) t).
Proof.
  intros.
  split; eapply triangle; auto.
Qed.

Print Assumptions pred1_diamond.
