(* Distributed under the terms of the MIT license. *)

From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config Environment uGraph.
From MetaCoq.Template Require Import Ast AstUtils LiftSubst UnivSubst Typing Checker Evars.
Import MCMonadNotation.

(** This file implements retyping, i.e. type inference on terms which
    are already known to be well-typed. This information can be used
    to skip many checks, resulting in a much faster algorithm in practice.
    
    Contrary to the typechecker in Checker.v, retyping can handle terms with evars. *)

Section StructuralEquality.
  Context `{checker_flags} (evm : EvarMap.t).

  (** Equality of terms modulo alpha equivalence, universe equivalence and evar expansion. *)
  Fixpoint eq_term_evars (t u : term) {struct t} :=
    match whd_evars evm t, whd_evars evm u with
    | tRel n, tRel n' => Nat.eqb n n'
    | tEvar ev args, tEvar ev' args' => Nat.eqb ev ev' && forallb2 eq_term_evars args args'
    | tVar id, tVar id' => eqb id id'
    | tSort s, tSort s' => check_eqb_sort (EvarMap.evm_universes evm) s s'
    | tCast f k T, tCast f' k' T' => eq_term_evars f f' && eq_term_evars T T'
    | tApp f args, tApp f' args' => eq_term_evars f f' && forallb2 eq_term_evars args args'
    | tConst c u, tConst c' u' => eq_constant c c' && eqb_univ_instance (EvarMap.evm_universes evm) u u'
    | tInd i u, tInd i' u' => eq_inductive i i' && eqb_univ_instance (EvarMap.evm_universes evm) u u'
    | tConstruct i k u, tConstruct i' k' u' => eq_inductive i i' && Nat.eqb k k'
                                                      && eqb_univ_instance (EvarMap.evm_universes evm) u u'
    | tLambda _ b t, tLambda _ b' t' => eq_term_evars b b' && eq_term_evars t t'
    | tProd _ b t, tProd _ b' t' => eq_term_evars b b' && eq_term_evars t t'
    | tLetIn _ b t c, tLetIn _ b' t' c' => eq_term_evars b b' && eq_term_evars t t' && eq_term_evars c c'
    | tCase ci p c brs,
      tCase ci' p' c' brs' =>
      eq_case_info ci ci' &&
      eqb_predicate (eqb_univ_instance (EvarMap.evm_universes evm)) eq_term_evars p p' && eq_term_evars c c' && forallb2 (fun br br' => eq_term_evars br.(bbody) br'.(bbody)) brs brs'
    | tProj p c, tProj p' c' => eq_projection p p' && eq_term_evars c c'
    | tFix mfix idx, tFix mfix' idx' =>
      forallb2 (fun x y =>
                  eq_term_evars x.(dtype) y.(dtype) && eq_term_evars x.(dbody) y.(dbody)) mfix mfix' &&
      Nat.eqb idx idx'
    | tCoFix mfix idx, tCoFix mfix' idx' =>
      forallb2 (fun x y =>
                  eq_term_evars x.(dtype) y.(dtype) && eq_term_evars x.(dbody) y.(dbody)) mfix mfix' &&
      Nat.eqb idx idx'
    | _, _ => false
    end.
  
  Fixpoint leq_term_evars (t u : term) {struct t} :=
    match whd_evars evm t, whd_evars evm u with
    | tRel n, tRel n' => Nat.eqb n n'
    | tEvar ev args, tEvar ev' args' => Nat.eqb ev ev' && forallb2 eq_term_evars args args'
    | tVar id, tVar id' => eqb id id'
    | tSort s, tSort s' => check_leqb_sort (EvarMap.evm_universes evm) s s'
    | tApp f args, tApp f' args' => eq_term_evars f f' && forallb2 eq_term_evars args args'
    | tCast f k T, tCast f' k' T' => eq_term_evars f f' && eq_term_evars T T'
    | tConst c u, tConst c' u' => eq_constant c c' && eqb_univ_instance (EvarMap.evm_universes evm) u u'
    | tInd i u, tInd i' u' => eq_inductive i i' && eqb_univ_instance (EvarMap.evm_universes evm) u u'
    | tConstruct i k u, tConstruct i' k' u' => eq_inductive i i' && Nat.eqb k k' &&
                                                      eqb_univ_instance (EvarMap.evm_universes evm) u u'
    | tLambda _ b t, tLambda _ b' t' => eq_term_evars b b' && eq_term_evars t t'
    | tProd _ b t, tProd _ b' t' => eq_term_evars b b' && leq_term_evars t t'
    | tLetIn _ b t c, tLetIn _ b' t' c' => eq_term_evars b b' && eq_term_evars t t' && leq_term_evars c c'
    | tCase ci p c brs, tCase ci' p' c' brs' =>
      eq_case_info ci ci' &&
      eqb_predicate (eqb_univ_instance (EvarMap.evm_universes evm)) eq_term_evars p p' && eq_term_evars c c' && forallb2 (fun br br' => eq_term_evars br.(bbody) br'.(bbody)) brs brs'
    | tProj p c, tProj p' c' => eq_projection p p' && eq_term_evars c c'
    | tFix mfix idx, tFix mfix' idx' =>
      forallb2 (fun x y =>
                  eq_term_evars x.(dtype) y.(dtype) && eq_term_evars x.(dbody) y.(dbody)) mfix mfix' &&
      Nat.eqb idx idx'
    | tCoFix mfix idx, tCoFix mfix' idx' =>
      forallb2 (fun x y =>
                  eq_term_evars x.(dtype) y.(dtype) && eq_term_evars x.(dbody) y.(dbody)) mfix mfix' &&
      Nat.eqb idx idx'
    | _, _ => false
    end.

End StructuralEquality.

(* Beware : retyping uses reduction and conversion on ground terms (i.e. terms
   without evars), which requires calling [nf_evars] before reduction and is 
   possibly inefficient. If this becomes a bottleneck we could rewrite the reduction
   functions we need to expand evars on the fly.  *)
Section Retyping.
  Context {cf : checker_flags} {F : Fuel}.
  Context (evm : EvarMap.t) (Σ : global_env) (Δ : named_context).

  Definition convert_leq Γ (t u : term) : typing_result unit :=
    if eq_term_evars evm t u then ret tt
    else
      match isconv Σ (EvarMap.evm_universes evm) Δ fuel Cumul Γ (nf_evars evm t) [] (nf_evars evm u) [] with
      | Some b =>
        if b then ret tt
        else raise (NotConvertible Γ t u t u)
      | None => (* fallback *)
        t' <- reduce Σ Δ Γ (nf_evars evm t) ;;
        u' <- reduce Σ Δ Γ (nf_evars evm u) ;;
        if leq_term_evars evm t' u' then ret tt
        else raise (NotConvertible Γ t u t' u')
      end.

  Section RetypeAux.
    Variable (retype : context -> term -> typing_result term).

    Fixpoint retype_spine (Γ : context) (ty : term) (l : list term)
             {struct l} : typing_result term :=
    match l with
    | nil => ret ty
    | cons x xs =>
       pi <- reduce_to_prod Σ Δ Γ (nf_evars evm ty) ;;
       let '(_, b1) := pi in
       retype_spine Γ (subst10 x b1) xs
    end.

    Definition retype_type Γ t :=
      tx <- retype Γ t ;;
      reduce_to_sort Σ Δ Γ (nf_evars evm tx).

    Definition retype_cumul Γ t t' :=
      tx <- retype Γ t ;;
      convert_leq Γ tx t'.

  End RetypeAux.

  Fixpoint retype (Γ : context) (t : term) : typing_result term :=
    (* We don't call [whd_evars], but instead handle evars explicitly below. *)
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
      ty <- retype Γ c ;;
      '(ind, u, args) <- reduce_to_ind Σ Δ Γ (nf_evars evm ty) ;;
      (* [rebuild_case_predicate_ctx] handles evars correctly,
         so no need to expand evars or thread the evar map. *)
      let pctx := rebuild_case_predicate_ctx Σ ind p in
      let ptm := it_mkLambda_or_LetIn pctx p.(preturn) in
      ret (mkApps ptm (List.skipn ci.(ci_npar) args ++ [c]))
      
    | tProj p c => 
      ty <- retype Γ c ;;
      '(_, u, args) <- reduce_to_ind Σ Δ Γ ty ;;
      lookup_projection_type Σ p c args u
      
    | tFix mfix n
    | tCoFix mfix n =>
      match nth_error mfix n with
      | Some f => ret f.(dtype)
      | None => raise (IllFormedFix mfix n)
      end

    | tInt _ | tFloat _ | tString _ | tArray _ _ _ _ => raise (NotSupported "primitive types")
    end.

  Definition recheck (Γ : context) (t : term) (ty : term) : typing_result unit :=
    retype Γ ty ;;
    retype_cumul retype Γ t ty ;;
    ret tt.

End Retyping.