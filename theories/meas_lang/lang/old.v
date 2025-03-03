(*

  Lemma cfg_cover_is_cover : List.fold_right setU set0 cfg_cover = setT.
  Proof. by rewrite foldr_cons setvU. Qed.

  (** The top-level cover is measurable *)

  Lemma cover_rec_meas : measurable cover_rec.
  Proof. by apply NonStatefulS_meas_fun; eauto with measlang. Qed.
  Hint Resolve cover_rec_meas : measlang.

  Lemma cover_pair_meas : measurable cover_pair.
  Proof.
    apply NonStatefulS_meas_fun.
    apply 𝜋_PairU_meas; eauto with measlang.
    apply measurableX; by eauto with measlang.
  Qed.
  Hint Resolve cover_pair_meas : measlang.

  Lemma cover_injL_meas : measurable cover_injL.
  Proof.
    apply NonStatefulS_meas_fun.
    by apply 𝜋_InjLU_meas; eauto with measlang.
  Qed.

  Hint Resolve cover_injL_meas : measlang.

  Lemma cover_injR_meas : measurable cover_injR.
  Proof.
    apply NonStatefulS_meas_fun.
    by apply 𝜋_InjRU_meas; eauto with measlang.
  Qed.
  Hint Resolve cover_injR_meas : measlang.

  Lemma cover_app_meas : measurable cover_app.
  Proof.
    apply NonStatefulS_meas_fun.
    apply 𝜋_AppU_meas; eauto with measlang.
    apply measurableX.
    - by apply 𝜋_ValU_meas; eauto with measlang.
    - by eauto with measlang.
  Qed.
  Hint Resolve cover_app_meas : measlang.


  Lemma cover_unop_ok'_meas : measurable cover_unop_ok'.
  Proof.
    apply 𝜋_UnOpU_meas; eauto with measlang.
    eapply (measurable_fun_prod' fst (ssrfun.comp 𝜋_Val_v snd) (setX (setT : set <<discr un_op>>) ecov_val)).
    { apply measurableX; by eauto with measlang. }
    { apply mathcomp_measurable_fun_restiction_setT.
      { apply measurableX; by eauto with measlang. }
      by apply measurable_fst. }
    3: { by apply auxcov_unop_ok_meas. }
    2: { apply measurableX; by eauto with measlang. }
    eapply measurable_comp.
    3: { by eapply 𝜋_Val_v_meas. }
    - by apply ecov_val_meas_set.
    - rewrite /subset//=.
      by move=>?//=[?[??]]<-//=.
    - eapply (mathcomp_measurable_fun_restiction_setT ([set: <<discr un_op >>] `*` ecov_val) _ snd).
      simpl.
      apply (@measurable_snd _ _ <<discr un_op>> expr).
    Unshelve.
    { apply measurableX; by eauto with measlang. }
  Qed.
  Hint Resolve cover_unop_ok'_meas : measlang.

  Lemma cover_unop_ok_meas : measurable cover_unop_ok.
  Proof. apply @measurable_fst; by eauto with measlang. Qed.
  Hint Resolve cover_unop_ok_meas : measlang.

  Lemma cover_unop_stuck_meas : measurable cover_unop_stuck.
  Proof.
    apply @measurable_fst; first by eauto with measlang.
    apply 𝜋_UnOpU_meas; eauto with measlang.
    eapply (measurable_fun_prod' fst (ssrfun.comp 𝜋_Val_v snd) (setX (setT : set <<discr un_op>>) ecov_val)).
    { apply measurableX; by eauto with measlang. }
    { apply mathcomp_measurable_fun_restiction_setT.
      { apply measurableX; by eauto with measlang. }
      by apply measurable_fst. }
    3: { by apply auxcov_unop_stuck_meas. }
    2: { apply measurableX; by eauto with measlang. }
    eapply measurable_comp.
    3: { by eapply 𝜋_Val_v_meas. }
    - by apply ecov_val_meas_set.
    - rewrite /subset//=.
      by move=>?//=[?[??]]<-//=.
    - eapply (mathcomp_measurable_fun_restiction_setT ([set: <<discr un_op >>] `*` ecov_val) _ snd).
      simpl.
      apply (@measurable_snd _ _ <<discr un_op>> expr).
    Unshelve.
    { apply measurableX; by eauto with measlang. }
  Qed.
  Hint Resolve cover_unop_stuck_meas : measlang.

  Lemma cover_binop_ok'_meas : measurable cover_binop_ok'.
  Proof.
    apply 𝜋_BinOpU_meas; eauto with measlang.
    eapply (measurable_fun_prod'
              (mProd (ssrfun.comp fst fst) (ssrfun.comp (ssrfun.comp 𝜋_Val_v snd) fst))
              (ssrfun.comp 𝜋_Val_v snd)
              (setX (setX setT ecov_val) ecov_val)).
    1,4: try by (apply measurableX; try by eauto with measlang; apply measurableX; by eauto with measlang).
    3: by eauto with measlang.
    { have H := (measurable_fun_prod'
                (ssrfun.comp fst fst)
                (ssrfun.comp (ssrfun.comp 𝜋_Val_v snd) fst)
                (setT `*` ecov_val `*` ecov_val)).
      apply H; clear H. (* Script hangs when I apply this directly *)
      { by (apply measurableX; try by eauto with measlang; apply measurableX; by eauto with measlang). }
      { eapply @mathcomp_measurable_fun_restiction_setT.
        { by (apply measurableX; try by eauto with measlang; apply measurableX; by eauto with measlang). }
        apply @measurable_compT.
        { by apply @measurableT. }
        { by apply measurable_fst. }
        by apply @measurable_fst.
      }
      eapply (@measurable_comp _ _ _ _ _ _ (setX setT ecov_val)).
      {  apply measurableX; by eauto with measlang. }
      { rewrite /subset//=.
        move=> [??[++]]//=.
        move=> [[??]?]//=.
        move=> [[??]?].
        move=> [+].
        by move=> ?<-//=. }
      { eapply @measurable_comp.
        3: { by apply 𝜋_Val_v_meas. }
        { by eauto with measlang. }
        { rewrite /subset//=.
          move=>?[[??]]//=.
          by move=>[??]<-//.
        }
        eapply @mathcomp_measurable_fun_restiction_setT.
        { apply measurableX; by eauto with measlang. }
        by apply @measurable_snd. }
      { eapply @mathcomp_measurable_fun_restiction_setT.
        { by (apply measurableX; try by eauto with measlang; apply measurableX; by eauto with measlang). }
        by apply @measurable_fst. }
    }
    { eapply measurable_comp.
      3: { by apply 𝜋_Val_v_meas. }
      1: by eauto with measlang.
      1: {
        rewrite /subset//=.
        move=>?[+[++]].
        move=>[[??]?].
        move=>[?[+]]//=.
        move=>??.
        move=>??<-//.
      }
      { eapply @mathcomp_measurable_fun_restiction_setT.
        { by (apply measurableX; try by eauto with measlang; apply measurableX; by eauto with measlang). }
        { by apply @measurable_snd. }
      }
    }
  Qed.
  Hint Resolve cover_binop_ok'_meas : measlang.

  Lemma cover_binop_ok_meas : measurable cover_binop_ok.
  Proof. apply @measurable_fst; by eauto with measlang. Qed.
  Hint Resolve cover_binop_ok_meas : measlang.

  Lemma cover_binop_stuck_meas : measurable cover_binop_stuck.
  Proof.
    apply @measurable_fst; first by eauto with measlang.
    apply 𝜋_BinOpU_meas; eauto with measlang.
    eapply (measurable_fun_prod'
              (mProd (ssrfun.comp fst fst) (ssrfun.comp (ssrfun.comp 𝜋_Val_v snd) fst))
              (ssrfun.comp 𝜋_Val_v snd)
              (setX (setX setT ecov_val) ecov_val)).
    1,4: try by (apply measurableX; try by eauto with measlang; apply measurableX; by eauto with measlang).
    3: by eauto with measlang.
    { have H := (measurable_fun_prod'
                (ssrfun.comp fst fst)
                (ssrfun.comp (ssrfun.comp 𝜋_Val_v snd) fst)
                (setT `*` ecov_val `*` ecov_val)).
      apply H; clear H. (* Script hangs when I apply this directly *)
      { by (apply measurableX; try by eauto with measlang; apply measurableX; by eauto with measlang). }
      { eapply @mathcomp_measurable_fun_restiction_setT.
        { by (apply measurableX; try by eauto with measlang; apply measurableX; by eauto with measlang). }
        apply @measurable_compT.
        { by apply @measurableT. }
        { by apply measurable_fst. }
        by apply @measurable_fst.
      }
      eapply (@measurable_comp _ _ _ _ _ _ (setX setT ecov_val)).
      {  apply measurableX; by eauto with measlang. }
      { rewrite /subset//=.
        move=> [??[++]]//=.
        move=> [[??]?]//=.
        move=> [[??]?].
        move=> [+].
        by move=> ?<-//=. }
      { eapply @measurable_comp.
        3: { by apply 𝜋_Val_v_meas. }
        { by eauto with measlang. }
        { rewrite /subset//=.
          move=>?[[??]]//=.
          by move=>[??]<-//.
        }
        eapply @mathcomp_measurable_fun_restiction_setT.
        { apply measurableX; by eauto with measlang. }
        by apply @measurable_snd. }
      { eapply @mathcomp_measurable_fun_restiction_setT.
        { by (apply measurableX; try by eauto with measlang; apply measurableX; by eauto with measlang). }
        by apply @measurable_fst. }
    }
    { eapply measurable_comp.
      3: { by apply 𝜋_Val_v_meas. }
      1: by eauto with measlang.
      1: {
        rewrite /subset//=.
        move=>?[+[++]].
        move=>[[??]?].
        move=>[?[+]]//=.
        move=>??.
        by move=>??<-//.
      }
      { eapply @mathcomp_measurable_fun_restiction_setT.
        { by (apply measurableX; try by eauto with measlang; apply measurableX; by eauto with measlang). }
        { by apply @measurable_snd. }
      }
    }
  Qed.
  Hint Resolve cover_binop_stuck_meas : measlang.





  Lemma auxcov_alloc_meas : measurable auxcov_alloc.
  Proof. Admitted.
  (*
    apply @measurable_fst.
    { by eauto with measlang. }
    apply 𝜋_AllocNU_meas.
    { by eauto with measlang. }
    apply measurableX.
    { by eauto with measlang. }
    { by eauto with measlang. }
  Qed. *)
  Hint Resolve auxcov_alloc_meas : measlang.

 *)

  (*
  Ltac subset_proof_simp_unfold :=
    match goal with
      | [ |- ∀ (a : expr_T) (b : (gmap loc val_T * gmap loc (nat * (nat * tapes.nf (option <<discr Z >>))) *
          gmap loc (nat * tapes.nf (option state.R)))), ?E ]        => move=>??//=
      | [ |- ∀ (x : expr_pre), ((?A = ?B) -> ?E) ]       => move=>?->//=
      | [ |- ∀ (x : val_pre), ((?A = ?B) -> ?E) ]        => move=>?->//=
      | [ |- ∀ (x : base_lit_pre), ((?A = ?B) -> ?E) ]   => move=>?->//=
      | [ |- ∀ x : @Measurable.sort default_measure_display TZ, ((?E = ?E1) → ?G)] => move=>?->//=
      | [ |- ∀ (x : expr_pre), ?E ]                      => move=>?//=
    end.

  Ltac subset_proof_simp_destruct := move=> [++].

  Ltac subset_proof_simp :=
    try rewrite/subset//=;
    move=>?;
    repeat (repeat subset_proof_simp_destruct; subset_proof_simp_unfold).
*)

(*
Section meas_semantics.
  Local Open Scope ereal_scope.
  Local Open Scope classical_set_scope.



  (*
  Lemma aux_allocN_Z_meas : measurable_fun auxcov_allocN aux_allocN_Z.
  Proof. Admitted.
    unfold aux_allocN_Z.
    unfold auxcov_allocN.
    eapply (@measurable_comp _ _ _ _ _ _ _ 𝜋_LitIntU).
    3: by eauto with measlang.
    1: by eauto with measlang.
    { subset_proof_simp.
      repeat move=>[++]; move=>??//=.
      rewrite /bcov_LitInt.
      move=><-//=.
      by eexists.
    }
    mcrunch_comp.
    { subset_proof_simp.
      repeat move=>[++]; move=>??//=.
      rewrite /vcov_lit.
      move=><-//=.
      by eexists.
    }
    mcrunch_comp.
    { subset_proof_simp.
      repeat move=>[++]; move=>??//=.
      rewrite /ecov_val.
      move=><-//=.
      by eexists.
    }
    mcrunch_comp.
    mcrunch_comp.
    {
      rewrite /subset//=.
      move=>?.
      repeat move=>[++]; subset_proof_simp_unfold.
      repeat move=>[++]; subset_proof_simp_unfold.
      repeat move=>[++]; subset_proof_simp_unfold.
      repeat move=>[++]; subset_proof_simp_unfold.
      repeat move=>[++]; subset_proof_simp_unfold.
      repeat move=>[++]; subset_proof_simp_unfold.
      repeat move=>[++]; subset_proof_simp_unfold.
      rewrite /ecov_alloc.
      move=><-//=.
      eexists _.
      eexists _.
      done.
    }
    mcrunch_fst.
  Qed.
  Hint Resolve aux_allocN_Z_meas : measlang.
*)

  Lemma aux_alloc_v_meas : measurable_fun auxcov_alloc aux_alloc_v.
  Proof. Admitted.
  (*
    unfold aux_allocN_v.
    unfold auxcov_allocN.
    eapply (@measurable_comp _ _ _ _ _ _ _ 𝜋_ValU).
    3: by eauto with measlang.
    1: by eauto with measlang.
    { rewrite /subset//=.
      move=>?.
      repeat move=>[++]; move=>??//=.
      repeat move=>[++]; move=>?//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>??//=.
      by move=>?<-//=.
    }
    mcrunch_comp.
    mcrunch_comp.
    { rewrite /subset//=.
      move=>?.
      repeat move=>[++]; move=>??//=.
      repeat move=>[++]; move=>?//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      rewrite /ecov_alloc//=.
      move=><-//=.
      eexists.
      by eexists.
    }
    by eapply @measurable_fst_restriction; eauto with measlang.
  Qed.*)
  Hint Resolve aux_alloc_v_meas : measlang.

  Lemma aux_alloc_σ_meas : measurable_fun auxcov_alloc aux_alloc_σ.
  Proof.
    by eapply @measurable_snd_restriction; eauto with measlang.
  Qed.
  Hint Resolve aux_alloc_σ_meas : measlang.

  Lemma aux_alloc_meas : measurable_fun auxcov_alloc aux_alloc.
  Proof.
    mcrunch_prod; try by eauto with measlang.
  Qed.
  Hint Resolve aux_alloc_meas : measlang.

  Lemma cover_alloc_ok_meas : measurable cover_alloc_ok.
  Proof.
    mcrunch_prod; try by eauto with measlang.
  Qed.
  Hint Resolve cover_alloc_ok_meas : measlang.

  Lemma cover_alloc_stuck_meas : measurable cover_alloc_stuck.
  Proof.
    mcrunch_prod; try by eauto with measlang.
  Qed.
  Hint Resolve cover_alloc_stuck_meas : measlang.

  Lemma auxcov_load_meas : measurable auxcov_load.
  Proof. unfold auxcov_load. by eauto with measlang. Qed.
  Hint Resolve auxcov_load_meas : measlang.

  Lemma aux_load_loc_meas : measurable_fun auxcov_load aux_load_loc.
  Proof.
    unfold aux_load_loc.
    unfold auxcov_load.
    eapply (@measurable_comp _ _ _ _ _ _ _ 𝜋_LitLocU).
    3: by apply 𝜋_LitLocU_meas.
    { by eauto with measlang. }
    { rewrite /subset//=.
      move=>?[++].
      move=>?[++].
      admit.
      (*
      move=>[?->]//=.
      move=>[++]//=.
      move=>[? _ <-]//=.
      move=>[++]//=.
      by move=>??//=<-//. *)
    }
    eapply (@measurable_comp _ _ _ _ _ _ _ 𝜋_LitV_v).
    3: by apply 𝜋_LitVU_meas.
    { by eauto with measlang. }
    { rewrite /subset//=.
      move=>?[++].
      move=>?[++].
      admit.
      (*  move=>[?->]//=.
      move=>[?->]//=.
      move=>[++].
      move=>[++].
      move=>[?->]//=.
      move=>[++].
      move=>[?->]//=.
      move=><-//.
      rewrite /vcov_lit/LitVC//=.
      by eexists _. *)
    }
    eapply (@measurable_comp _ _ _ _ _ _ _ 𝜋_Val_v).
    3: by apply 𝜋_ValU_meas.
    { by eauto with measlang. }
    { rewrite /subset//=.
      move=>?[++].
      move=>?[++].
      admit.
      (*
      move=>[?->]//=.
      move=>[++].
        move=>[?->]//=.
      move=>[++].
      move=>[?->]//=.
      move=>[++].
      move=>[?->]//=.
      move=><-//.
      rewrite /vcov_lit/LitVC//=.
      rewrite /ecov_val//=.
      by eexists _. *)
    }
    rewrite <-(setIid ecov_load).
    rewrite <-setIA.
    by apply measurable_fun_setI1; try by eauto with measlang.
  Admitted.
  Hint Resolve aux_load_loc_meas : measlang.

  Lemma cover_load_ok_meas : measurable cover_load_ok.
  Proof.
    have S1 : (expr_cyl.-sigma, _).-prod.-measurable (auxcov_load `*` [set: state]).
    { by apply measurableX; eauto with measlang. }
    (*
    apply (@measurable_fun_prod' _ _ _ _ _ _ (ssrfun.comp aux_load_loc fst) snd).
    1, 4: done.
    3: by eauto with measlang.
    { eapply @measurable_comp.
      3: by apply aux_load_loc_meas.
      1: by eauto with measlang.
      { rewrite /subset//=.
        move=>?[+[++]].
        by move=>???<-//. }
      eapply @mathcomp_measurable_fun_restiction_setT.
      { by eauto with measlang. }
      { by apply measurable_fst. }
    }
    { eapply @mathcomp_measurable_fun_restiction_setT.
      { by eauto with measlang. }
      { by apply measurable_snd. }
    }
  Qed. *)
  Admitted.
  Hint Resolve cover_load_ok_meas : measlang.

  Lemma cover_load_stuck_meas : measurable cover_load_stuck.
  Proof. Admitted.
  (*
    have S1 : (expr_cyl.-sigma, _).-prod.-measurable (auxcov_load `*` [set: state]).
    { by apply measurableX; eauto with measlang. }
    apply (@measurable_fun_prod' _ _ _ _ _ _ (ssrfun.comp aux_load_loc fst) snd).
    1, 4: done.
    3: eauto with measlang.
    { eapply @measurable_comp.
      3: by apply aux_load_loc_meas.
      1: by eauto with measlang.
      { rewrite /subset//=.
        move=>?[+[++]].
        by move=>???<-//. }
      eapply @mathcomp_measurable_fun_restiction_setT.
      { by eauto with measlang. }
      { by apply measurable_fst. }
    }
    { eapply @mathcomp_measurable_fun_restiction_setT.
      { by eauto with measlang. }
      { by apply measurable_snd. }
    }
  Qed. *)
  Hint Resolve cover_load_stuck_meas : measlang.


  Lemma auxcov_store_meas : measurable auxcov_store.
  Proof.
    apply @measurable_fst.
    { by eauto with measlang. }
    apply 𝜋_StoreU_meas.
    { by eauto with measlang. }
    apply measurableX.
    { by eauto with measlang. }
    { by eauto with measlang. }
  Qed.
  Hint Resolve auxcov_store_meas : measlang.

  Lemma aux_store_loc_meas : measurable_fun auxcov_store aux_store_loc.
  Proof.
    unfold aux_store_loc.
    unfold auxcov_store.
    eapply (@measurable_comp _ _ _ _ _ _ _ 𝜋_LitLocU).
    3: by eauto with measlang.
    1: by eauto with measlang.
    { rewrite /subset//=.
      move=>?.
      repeat move=>[++]; move=>??//=.
      repeat move=>[++]; move=>?//=.
      admit.
      (*
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>??//=.
      rewrite /bcov_LitLoc.
      move=><-//=.
      by eexists. *)
    }
    mcrunch_comp.
    { rewrite /subset//=.
      move=>?.
      repeat move=>[++]; move=>??//=.
      repeat move=>[++]; move=>?//=.
      admit.
        (*
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>??//=.
      rewrite /vcov_lit.
      move=><-//=.
      by eexists. *)
    }
    mcrunch_comp.
    {
      move=>?.
      repeat move=>[++]; move=>??//=.
      repeat move=>[++]; move=>?//=.
      admit.
      (*
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>??//=.
      rewrite /ecov_val.
      move=><-//=.
      by eexists. *)
    }
    mcrunch_comp.
    mcrunch_comp.
    {
      move=>?.
      repeat move=>[++]; move=>??//=.
      repeat move=>[++]; move=>?//=.
      admit.
      (*
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      rewrite /ecov_alloc.
      move=><-//=.
      eexists _.
      eexists _.
      done. *)
    }
  by eapply @measurable_fst_restriction; eauto with measlang.
  Admitted.
  Hint Resolve aux_store_loc_meas : measlang.

  Lemma aux_store_v_meas : measurable_fun auxcov_store aux_store_v.
  Proof.
    unfold aux_store_v.
    unfold auxcov_store.
    eapply (@measurable_comp _ _ _ _ _ _ _ 𝜋_ValU).
    3: by eauto with measlang.
    1: by eauto with measlang.
    { rewrite /subset//=.
      move=>?.
      repeat move=>[++]; move=>??//=.
      repeat move=>[++]; move=>?//=.
      admit.
      (*
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>??//=.
      by move=>?<-//=. *)
    }
    mcrunch_comp.
    mcrunch_comp.
    { rewrite /subset//=.
      move=>?.
      repeat move=>[++]; move=>??//=.
      repeat move=>[++]; move=>?//=.
      admit.
      (*
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      rewrite /ecov_alloc//=.
      move=><-//=.
      eexists.
      by eexists. *)
    }
    by eapply @measurable_fst_restriction; eauto with measlang.
  Admitted.
  Hint Resolve aux_store_v_meas : measlang.

  Lemma aux_store_σ_meas : measurable_fun auxcov_store aux_store_σ.
  Proof. by eapply @measurable_snd_restriction; eauto with measlang. Qed.
  Hint Resolve aux_store_σ_meas : measlang.

  Lemma aux_store_meas : measurable_fun auxcov_store aux_store.
  Proof.
    mcrunch_prod; try by eauto with measlang.
    mcrunch_prod; by eauto with measlang.
  Qed.
  Hint Resolve aux_store_meas : measlang.

  Lemma cover_store_ok_meas : measurable cover_store_ok.
  Proof.
    mcrunch_prod; try by eauto with measlang.
    mcrunch_prod; by eauto with measlang.
  Qed.
  Hint Resolve cover_store_ok_meas : measlang.

  Lemma cover_store_stuck_meas : measurable cover_store_stuck.
  Proof.
    mcrunch_prod; try by eauto with measlang.
    mcrunch_prod; by eauto with measlang.
  Qed.
  Hint Resolve cover_store_stuck_meas : measlang.

  Lemma cover_ifT_meas : measurable cover_ifT.
  Proof.
    apply NonStatefulS_meas_fun.
    apply 𝜋_If_c_meas; first by eauto with measlang.
    apply 𝜋_Val_v_meas; first by eauto with measlang.
    apply 𝜋_LitV_v_meas; first by eauto with measlang.
    apply 𝜋_LitBool_b_meas; first by eauto with measlang.
    by rewrite /measurable/discr_measurable//=.
  Qed.
  Hint Resolve cover_ifT_meas : measlang.

  Lemma cover_ifF_meas : measurable cover_ifF.
  Proof.
    apply NonStatefulS_meas_fun.
    apply 𝜋_If_c_meas; first by eauto with measlang.
    apply 𝜋_Val_v_meas; first by eauto with measlang.
    apply 𝜋_LitV_v_meas; first by eauto with measlang.
    apply 𝜋_LitBool_b_meas; first by eauto with measlang.
    by rewrite /measurable/discr_measurable//=.
  Qed.
  Hint Resolve cover_ifF_meas : measlang.

  Lemma cover_fst_meas : measurable cover_fst.
  Proof.
    apply NonStatefulS_meas_fun.
    apply 𝜋_Fst_e_meas; first by eauto with measlang.
    apply 𝜋_Val_v_meas; first by eauto with measlang.
    eauto with measlang.
  Qed.
  Hint Resolve cover_fst_meas : measlang.

  Lemma cover_snd_meas : measurable cover_snd.
  Proof.
    apply NonStatefulS_meas_fun.
    apply 𝜋_Snd_e_meas; first by eauto with measlang.
    apply 𝜋_Val_v_meas; first by eauto with measlang.
    eauto with measlang.
  Qed.
  Hint Resolve cover_snd_meas : measlang.

  Lemma cover_caseL_meas : measurable cover_caseL.
  Proof.
    apply NonStatefulS_meas_fun.
    apply 𝜋_Case_c_meas; first by eauto with measlang.
    apply 𝜋_Val_v_meas; first by eauto with measlang.
    eauto with measlang.
  Qed.
  Hint Resolve cover_caseL_meas : measlang.

  Lemma cover_caseR_meas : measurable cover_caseR.
  Proof.
    apply NonStatefulS_meas_fun.
    apply 𝜋_Case_c_meas; first by eauto with measlang.
    apply 𝜋_Val_v_meas; first by eauto with measlang.
    eauto with measlang.
  Qed.
  Hint Resolve cover_caseR_meas : measlang.

  Lemma cover_allocTape_meas : measurable cover_allocTape.
  Proof.
    apply NonStatefulS_meas_fun.
    apply 𝜋_AllocTapeU_meas; first by eauto with measlang.
    apply 𝜋_ValU_meas; first by eauto with measlang.
    apply 𝜋_LitVU_meas; first by eauto with measlang.
    by eauto with measlang.
  Qed.
  Hint Resolve cover_allocTape_meas : measlang.

  Lemma cover_allocUTape_meas : measurable cover_allocUTape.
  Proof.
    apply NonStatefulS_meas_fun.
    by eauto with measlang.
  Qed.
  Hint Resolve cover_allocUTape_meas : measlang.

  Lemma cover_rand_meas : measurable cover_rand.
  Proof.
    apply NonStatefulS_meas_fun.
    apply 𝜋_RandU_meas; first by eauto with measlang.
    apply measurableX.
    { apply 𝜋_ValU_meas; first by eauto with measlang.
      apply 𝜋_LitVU_meas; first by eauto with measlang.
      by eauto with measlang. }
    { apply 𝜋_ValU_meas; first by eauto with measlang.
      apply 𝜋_LitVU_meas; first by eauto with measlang.
      by eauto with measlang. }
  Qed.
  Hint Resolve cover_rand_meas : measlang.

  Lemma cover_urand_meas : measurable cover_urand.
  Proof.
    apply NonStatefulS_meas_fun.
    apply 𝜋_URandU_meas; first by eauto with measlang.
    apply 𝜋_ValU_meas; first by eauto with measlang.
    apply 𝜋_LitVU_meas; first by eauto with measlang.
    by eauto with measlang.
  Qed.
  Hint Resolve cover_urand_meas : measlang.

  Lemma cover_randT_meas : measurable cover_randT.
  Proof.
    apply NonStatefulS_meas_fun.
    apply 𝜋_RandU_meas; first by eauto with measlang.
    apply measurableX.
    { apply 𝜋_ValU_meas; first by eauto with measlang.
      apply 𝜋_LitVU_meas; first by eauto with measlang.
      by eauto with measlang. }
    { apply 𝜋_ValU_meas; first by eauto with measlang.
      apply 𝜋_LitVU_meas; first by eauto with measlang.
      by eauto with measlang. }
  Qed.
  Hint Resolve cover_randT_meas : measlang.

  Lemma cover_urandT_meas : measurable cover_urandT.
  Proof.
    apply NonStatefulS_meas_fun.
    apply 𝜋_URandU_meas; first by eauto with measlang.
    apply 𝜋_ValU_meas; first by eauto with measlang.
    apply 𝜋_LitVU_meas; first by eauto with measlang.
    by eauto with measlang.
  Qed.
  Hint Resolve cover_urandT_meas : measlang.

  Lemma cover_tick_meas : measurable cover_tick.
  Proof.
    apply NonStatefulS_meas_fun.
    apply 𝜋_Tick_e_meas; first by eauto with measlang.
    apply 𝜋_Val_v_meas; first by eauto with measlang.
    apply 𝜋_LitV_v_meas; first by eauto with measlang.
    eauto with measlang.
  Qed.
  Hint Resolve cover_tick_meas : measlang.


  Lemma cover_maybe_stuck_meas : measurable cover_maybe_stuck.
  Proof.
    apply measurableC.
    rewrite //=.
    repeat (eapply (@measurableU _ cfg _); first by eauto with measlang).
    by eapply @measurable0.
  Qed.
  Hint Resolve cover_maybe_stuck_meas : measlang.

  (**  Top-level functions *)

  (* Generic lifting of a curried constructor on expr to a curried constructor on states *)
  Definition NonStatefulU {A : Type} (C : A -> expr) : (A * state) -> cfg := fun x => (C x.1, x.2).

  Lemma NonStatefulU_meas {d} {A : measurableType d} (C : A -> expr) (S : set A) (HS : measurable S)
      (HC : measurable_fun S C) : measurable_fun (NonStatefulS S) (NonStatefulU C).
  Proof.
    rewrite /NonStatefulU//=.
    have H1 : measurable_fun (T:=A) (U:=A) S (fun x => x).
    { apply mathcomp_measurable_fun_restiction_setT; [done|].
      by apply measurable_id.
    }
    apply (measurable_fun_prod' (ssrfun.comp C fst) snd (NonStatefulS S) (NonStatefulS_meas_fun S HS)).
    - eapply measurable_comp.
      3: { by apply HC. }
      + by apply HS.
      + by rewrite /NonStatefulS/preimage/subset//=; move=> t [??<-].
      + apply (mathcomp_measurable_fun_restiction_setT (NonStatefulS S) (NonStatefulS_meas_fun S HS) fst).
        by eapply @measurable_fst_restriction; eauto with measlang.
    - apply (mathcomp_measurable_fun_restiction_setT (NonStatefulS S) (NonStatefulS_meas_fun S HS) snd).
        by eapply @measurable_snd_restriction; eauto with measlang.
  Qed.

  (** Top-level functions *)
  (* | Rec f x e => gRet ((Val $ RecV f x e, σ1) : cfg)  *)
  Definition head_stepM_rec : cfg -> giryM cfg :=
    ssrfun.comp gRet $
    NonStatefulU $
    ssrfun.comp ValU $
    ssrfun.comp RecVU 𝜋_RecU.

  (* | Pair (Val v1) (Val v2) => gRet ((Val $ PairV v1 v2, σ1) : cfg)   *)
  Definition head_stepM_pair : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    NonStatefulU $
    ssrfun.comp ValU $
    ssrfun.comp PairVU $
    mProd
      (ssrfun.comp 𝜋_Val_v 𝜋_Pair_l)
      (ssrfun.comp 𝜋_Val_v $ 𝜋_Pair_r).

  (* | InjL (Val v) => gRet ((Val $ InjLV v, σ1) : cfg) *)
  Definition head_stepM_injL : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    NonStatefulU $
    ssrfun.comp ValU $
    ssrfun.comp InjLVU $
    ssrfun.comp 𝜋_ValU $
    𝜋_InjLU.

  (* | InjR (Val v) => gRet ((Val $ InjRV v, σ1) : cfg) *)
  Definition head_stepM_injR : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    NonStatefulU $
    ssrfun.comp ValU $
    ssrfun.comp InjRVU $
    ssrfun.comp 𝜋_ValU $
    𝜋_InjRU.

  (* | App (Val (RecV f x e1)) (Val v2) => gRet ((subst' x v2 (subst' f (RecV f x e1) e1) , σ1) : cfg)  *)
  Definition head_stepM_app : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    NonStatefulU $
    ssrfun.comp substU' $ (* subst' ...  *)
    mProd
      (ssrfun.comp 𝜋_RecV_x $ ssrfun.comp 𝜋_Val_v $ 𝜋_App_l) (* x *)
    (mProd
      (ssrfun.comp 𝜋_Val_v $ 𝜋_App_r) (* v2 *)
    (ssrfun.comp substU' $ (* subst' ...  *)
    mProd
      (ssrfun.comp 𝜋_RecV_f $ ssrfun.comp 𝜋_Val_v $ 𝜋_App_l) (* f *)
    (mProd
       (ssrfun.comp 𝜋_Val_v $ 𝜋_App_l) (* RecV f x e1 *)
       (ssrfun.comp 𝜋_RecV_e $ ssrfun.comp 𝜋_Val_v $ 𝜋_App_l)))) (* e1 *).

  (* | UnOp op (Val v) =>
        match un_op_eval op v with
          | Some w => gRet ((Val w, σ1) : cfg)
          | _ => gZero
        end
   *)

  (* The function (on configurations) to do when the cfg is a UnOp that is valid *)
  Definition head_stepM_unop_ok : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    mProd
      ( ssrfun.comp ValU $
        ssrfun.comp un_op_evalC $
        ssrfun.comp
          (mProd
            𝜋_UnOp_op
            (ssrfun.comp 𝜋_Val_v 𝜋_UnOp_e)) $
        fst )
      snd.

  (* TODO: Delete *)
  Definition head_stepM_unop_stuck : cfg -> giryM cfg :=
    cst gZero.

  (* The function (on configurations) to do when the cfg is a BinOp that is valid *)
  Definition head_stepM_binop_ok : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    mProd
      ( ssrfun.comp ValU $
        ssrfun.comp bin_op_evalC $
        ssrfun.comp
          (mProd
              (mProd
                 𝜋_BinOp_op
                 (ssrfun.comp 𝜋_Val_v 𝜋_BinOp_l))
              (ssrfun.comp 𝜋_Val_v 𝜋_BinOp_r)) $
        fst )
      snd.

  (* TODO: Delete *)
  Definition head_stepM_binop_stuck : cfg -> giryM cfg :=
    cst gZero.


  (*
    | AllocN (Val (LitV (LitInt N))) (Val v) =>
        if bool_decide (0 < Z.to_nat N)%nat
          then
            let ℓ := fresh_loc σ1.(heap) in
            gRet ((Val $ LitV $ LitLoc ℓ, state_upd_heap_N ℓ (Z.to_nat N) v σ1) : cfg)
          else gZero

   *)
  Definition head_stepM_alloc_ok : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    mProd
      (ssrfun.comp ValU $
       ssrfun.comp LitVU $
       ssrfun.comp LitLocU $
       ssrfun.comp state_allocNCE $
       aux_alloc)
      (ssrfun.comp state_allocNCS $
       aux_alloc).

  (* TODO: Delete *)
  Definition head_stepM_alloc_stuck: cfg -> giryM cfg :=
    cst gZero.

  (*
    | Load (Val (LitV (LitLoc l))) =>
        match σ1.(heap) !! l with
          | Some v => gRet ((Val v, σ1) : cfg)
          | None => gZero
        end
   *)
  Definition head_stepM_load_ok : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    mProd
      ( ssrfun.comp ValU $
        ssrfun.comp state_loadC $
        (mProd (ssrfun.comp aux_load_loc fst) snd) )
      snd.

  (* TODO: Delete *)
  Definition head_stepM_load_stuck: cfg -> giryM cfg :=
    cst gZero.

  Definition head_stepM_store_ok : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    mProd
      (ssrfun.comp state_storeE $ aux_store)
      (ssrfun.comp state_storeS $ aux_store).

  (* TODO: Delete *)
  Definition head_stepM_store_stuck: cfg -> giryM cfg :=
    cst gZero.

  (* | If (Val (LitV (LitBool true))) e1 e2  => gRet ((e1 , σ1) : cfg) *)
  Definition head_stepM_ifT : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    NonStatefulU $
    𝜋_If_l.

  (* | If (Val (LitV (LitBool false))) e1 e2 => gRet ((e2 , σ1) : cfg) *)
  Definition head_stepM_ifF : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    NonStatefulU $
    𝜋_If_r.

  (* | Fst (Val (PairV v1 v2)) => gRet ((Val v1, σ1) : cfg) *)
  Definition head_stepM_fst : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    NonStatefulU $
    ssrfun.comp ValU $
    ssrfun.comp 𝜋_PairV_l $
    ssrfun.comp 𝜋_ValU $
    𝜋_Fst_e.

  (* | Snd (Val (PairV v1 v2)) => gRet ((Val v2, σ1) : cfg) *)
  Definition head_stepM_snd : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    NonStatefulU $
    ssrfun.comp ValU $
    ssrfun.comp 𝜋_PairV_r $
    ssrfun.comp 𝜋_ValU $
    𝜋_Snd_e.

  (* | Case (Val (InjLV v)) e1 e2 => gRet ((App e1 (Val v), σ1) : cfg) *)
  Definition head_stepM_caseL : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    NonStatefulU $
    ssrfun.comp AppU $
    mProd
      𝜋_Case_l
      ( ssrfun.comp ValU $
        ssrfun.comp 𝜋_InjLV_v $
        ssrfun.comp 𝜋_Val_v $
        𝜋_Case_c ).

  (* | Case (Val (InjRV v)) e1 e2 => gRet ((App e2 (Val v), σ1) : cfg) *)
  Definition head_stepM_caseR : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    NonStatefulU $
    ssrfun.comp AppU $
    mProd
      𝜋_Case_r
      ( ssrfun.comp ValU $
        ssrfun.comp 𝜋_InjRV_v $
        ssrfun.comp 𝜋_Val_v $
        𝜋_Case_c ).


  Definition head_stepM_allocTape_aux : cfg -> (<<discr Z>> * state)%type :=
    mProd
      (ssrfun.comp 𝜋_LitInt_z $
       ssrfun.comp 𝜋_LitV_v $
       ssrfun.comp 𝜋_Val_v $
       ssrfun.comp 𝜋_AllocTape_e $
       fst)
      snd.
  (*
    | AllocTape (Val (LitV (LitInt z))) =>
        let ι := fresh_loc σ1.(tapes) in
        gRet ((Val $ LitV $ LitLbl ι, state_upd_tapes <[ι := {| btape_tape := emptyTape ; btape_bound := (Z.to_nat z) |} ]> σ1) : cfg)
      destruct and apply RandAllcoTapeE/S
  *)
  Definition head_stepM_allocTape : cfg -> giryM cfg :=
    if_in (ssrfun.comp rand_allocTape_ok_cov head_stepM_allocTape_aux)
      (ssrfun.comp (gRet) $
        mProd
        (ssrfun.comp ValU $
          ssrfun.comp LitVU $
          ssrfun.comp LitLblU $
          ssrfun.comp rand_allocTapeE $
          head_stepM_allocTape_aux)
        (ssrfun.comp rand_allocTapeS $
          head_stepM_allocTape_aux))
        (cst gZero).


  (*
    | AllocUTape =>
        let ι := fresh_loc σ1.(utapes) in
        gRet ((Val $ LitV $ LitLbl ι, state_upd_utapes <[ ι := emptyTape ]> σ1) : cfg)
   *)
  Definition head_stepM_allocUTape : cfg -> giryM cfg :=
    if_in (ssrfun.comp rand_allocUTape_ok_cov snd)
      (ssrfun.comp (gRet) $
      mProd
        (ssrfun.comp ValU $
         ssrfun.comp LitVU $
         ssrfun.comp LitLblU $
         ssrfun.comp rand_allocUTapeE $
         snd)
        (ssrfun.comp rand_allocUTapeS $
         snd))
      (cst gZero).

  (* Rand (Val (LitInt N)) (Val LitUnit) -> ... *)
  Definition head_stepM_aux_rand : cfg -> (<<discr Z>> * state)%type :=
    mProd
      (ssrfun.comp 𝜋_LitInt_z $
       ssrfun.comp 𝜋_LitV_v $
       ssrfun.comp 𝜋_Val_v $
       ssrfun.comp 𝜋_Rand_N $
       fst)
      snd.

  Definition head_stepM_rand : cfg -> giryM cfg :=
    ssrfun.comp rand_rand head_stepM_aux_rand.

  Definition head_stepM_aux_urand : cfg -> state :=
    snd.

  Definition head_stepM_urand : cfg -> giryM cfg :=
    ssrfun.comp rand_urand head_stepM_aux_urand.

  (* Rand (Val (LitInt N)) (Val (LitLbl t)) -> ... *)
  Definition head_stepM_aux_randT : cfg -> (<<discr Z >> * <<discr loc >> * state)%type :=
    mProd
      (mProd
        (ssrfun.comp 𝜋_LitInt_z $
         ssrfun.comp 𝜋_LitV_v $
         ssrfun.comp 𝜋_Val_v $
         ssrfun.comp 𝜋_Rand_N $
         fst)
        (ssrfun.comp 𝜋_LitLbl_l $
         ssrfun.comp 𝜋_LitV_v $
         ssrfun.comp 𝜋_Val_v $
         ssrfun.comp 𝜋_Rand_t $
         fst))
      snd.

  Definition head_stepM_randT : cfg -> giryM cfg :=
    ssrfun.comp rand_randT head_stepM_aux_randT.

  (* URand  (Val (LitLbl t)) -> ... *)
  Definition head_stepM_aux_urandT : cfg -> (<<discr loc >> * state)%type :=
    mProd
      (ssrfun.comp 𝜋_LitLbl_l $
       ssrfun.comp 𝜋_LitV_v $
       ssrfun.comp 𝜋_Val_v $
       ssrfun.comp 𝜋_URand_e $
       fst)
      snd.

  Definition head_stepM_urandT : cfg -> giryM cfg :=
    ssrfun.comp rand_urandT head_stepM_aux_urandT.

  (* | Tick (Val (LitV (LitInt n))) => gRet ((Val $ LitV $ LitUnit, σ1) : cfg) *)
  Definition head_stepM_tick : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    NonStatefulU $
    ssrfun.comp ValU $
    ssrfun.comp LitVU $
    cst LitUnit.

  Definition head_stepM_stuck : cfg -> giryM cfg :=
    cst gZero.


  (** Measurability of head_step restricted to the different sets in the cover *)
  Lemma head_stepM_rec_meas : measurable_fun cover_rec head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_rec head_stepM).
    - solve_toplevel_meas.
  Admitted.
  (*
      { eapply @gRet_meas_fun. }
      apply @NonStatefulU_meas; solve_toplevel_meas. (* How to integrate this into the tactic w/o stack overflow?*)
      (* Why do these not get applied form the hintdb? *)
      - by apply ValU_meas_fun.
      - by apply RecVU_meas_fun.
    - (* The trick: the two functions are equal on this set. *)
      move=>[??].
  Admitted. *)
  (*
      do 3 (move=>[+]; move=>?).
      by move=>/=->/=.
    Unshelve. by eauto with measlang.
  Qed. *)
  Hint Resolve head_stepM_rec_meas : measlang.

  Lemma head_stepM_pair_meas : measurable_fun cover_pair head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_pair head_stepM).
    - (* FIXME: Duplicate proof from above *)
      have S : expr_cyl.-sigma.-measurable (ecov_pair `&` 𝜋_PairU @^-1` (ecov_val `*` ecov_val)).
      { apply 𝜋_PairU_meas; last apply measurableX; by eauto with measlang.  }
      apply measurable_compT.
      { by apply cover_pair_meas. }
      { by apply gRet_meas_fun. }
      apply @NonStatefulU_meas; try done.
      (*  solve_toplevel_meas. *)
      (* FIXME: Remove whatever hint is making this overapproximate the cover set
          I think it's measurable_compT, which we only want to use for certain compositions... *)
      apply measurable_compT; try by eauto with measlang.
      + by apply ValU_meas_fun.
      apply measurable_compT; try by eauto with measlang.
      + by apply PairVU_meas_fun.
      apply measurable_fun_prod'_expr; try by eauto with measlang.
      + eapply measurable_comp.
        3: by apply 𝜋_Val_v_meas.
        * by eauto with measlang.
        * rewrite /subset//=.
          move=>?[+[+[++]]].
          move=>????<-.
          by rewrite /ecov_val//=.
        * rewrite <-(setIid ecov_pair).
          rewrite <-setIA.
          by apply measurable_fun_setI1; try by eauto with measlang.
      + eapply measurable_comp.
        3: { by apply 𝜋_Val_v_meas. }
        * by eauto with measlang.
        * rewrite /subset//=.
          move=>?[+[+[++]]].
          move=>????<-.
          by rewrite /ecov_val//=.
        * rewrite <-(setIid ecov_pair).
          rewrite <-setIA.
          by apply measurable_fun_setI1; try by eauto with measlang.
        all: try (by eauto with measlang).
    - move=>[e?].
  Admitted.
  (*
      move=>/=[+].
      move=>[?[?+]].
      move=>//=->//=.
      move=>[++].
      rewrite /ecov_val//=.
      do 2 move=>[?->].
      by rewrite //=.
    Unshelve. by eauto with measlang.
  Qed. *)
  Hint Resolve head_stepM_pair_meas : measlang.

  Lemma head_stepM_injL_meas : measurable_fun cover_injL head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_injL head_stepM).
    - apply measurable_compT.
      { by apply cover_injL_meas. }
      { by apply gRet_meas_fun. }
      have S : (expr_cyl.-sigma.-measurable (ecov_injl `&` 𝜋_InjLU @^-1` ecov_val)).
      { apply 𝜋_InjLU_meas; by eauto with measlang. }
      apply @NonStatefulU_meas; first done.
      apply measurable_compT; try by eauto with measlang.
      + by apply ValU_meas_fun.
      apply measurable_compT; try by eauto with measlang.
      + by apply InjLVU_meas_fun.
      eapply measurable_comp.
      3: { by apply 𝜋_Val_v_meas. }
      * by eauto with measlang.
      * rewrite /subset//=.
        move=>?[+[+[++]]].
        admit.
        (*  move=>???-><-.
        by eexists _; eauto. *)
      * rewrite <-(setIid ecov_injl).
        rewrite <-setIA.
        apply measurable_fun_setI1; try by eauto with measlang.
    - move=>[e?].
      move=>/=[+].

      admit.
      (*
      move=>[?+].
      move=>//=->//=.
      move=>[?->].
      rewrite /ecov_val//=.
    Unshelve. by eauto with measlang. *)
  Admitted.
  Hint Resolve head_stepM_injL_meas : measlang.

  Lemma head_stepM_injR_meas : measurable_fun cover_injR head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_injR head_stepM).
    - apply measurable_compT.
      { by apply cover_injR_meas. }
      { by apply gRet_meas_fun. }
      have S : (expr_cyl.-sigma.-measurable (ecov_injr `&` 𝜋_InjRU @^-1` ecov_val)).
      { apply 𝜋_InjRU_meas; by eauto with measlang. }
      apply @NonStatefulU_meas; first done.
      apply measurable_compT; try by eauto with measlang.
      + by apply ValU_meas_fun.
      apply measurable_compT; try by eauto with measlang.
      + by apply InjRVU_meas_fun.
      eapply measurable_comp.
      3: { by apply 𝜋_Val_v_meas. }
      * by eauto with measlang.
      * rewrite /subset//=.
        move=>?[+[+[++]]].
        admit.
        (*
        move=>???-><-.
        by eexists _; eauto. *)
      * rewrite <-(setIid ecov_injr).
        rewrite <-setIA.
        apply measurable_fun_setI1; try by eauto with measlang.
    - move=>[e?].
      move=>/=[+].
  Admitted.
  (*
      move=>[?+].
      move=>//=->//=.
      move=>[?->].
      rewrite /ecov_val//=.
    Unshelve. by eauto with measlang.
  Qed. *)
  Hint Resolve head_stepM_injR_meas : measlang.

  (* FIXME: Many of the subproofs here are repetitive *)
  Lemma head_stepM_app_meas : measurable_fun cover_app head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_app head_stepM).
    - apply measurable_compT.
      { by apply cover_app_meas. }
      { by apply gRet_meas_fun. }
      have S : expr_cyl.-sigma.-measurable (ecov_app `&` 𝜋_AppU @^-1` ((ecov_val `&` 𝜋_Val_v @^-1` vcov_rec) `*` ecov_val)).
      { apply 𝜋_AppU_meas; try by eauto with measlang.
        apply measurableX; by eauto with measlang. }
      apply @NonStatefulU_meas; first done.
      apply measurable_compT; try by eauto with measlang.
      { by apply substU'_measurable. }
      apply measurable_fun_prod'_expr; try by eauto with measlang.
      { eapply measurable_comp.
        3: { by eapply 𝜋_RecV_x_meas. }
        * by eauto with measlang.
        * rewrite /subset//=.
          move=>?[+[+[++]]].
          admit.
          (*
          move=>?[+].
          move=>?[+]; move=>?->//=.
          move=>[[++]+]; move=>?->//=.
          move=>[+[+[++]]]; move=>???->.
          move=>[++]; move=>??.
          move=><-//=.
          rewrite/vcov_rec/RecVC//=.
          by do 3 eexists. *)
        rewrite <-(setIid ecov_app).
        rewrite <-setIA.
        apply measurable_fun_setI2; try by eauto with measlang.
        eapply measurable_comp.
        3: { by eapply 𝜋_Val_v_meas. }
        * by eauto with measlang.
        * rewrite /subset//=.
          move=>?.
          move=>[+[+[++]]].
          move=>?.
          admit.
          (*
          move=> [+[++[++]]].
          move=>??->//=.
          move=>[++]; move=>?->//=.
          move=>[+[+[++]]]; move=>???->.
          move=>[++]; move=>??<-.
          rewrite /ecov_val/ValC//=.
          by eexists. *)
        rewrite <-(setIid ecov_app).
        rewrite <-setIA.
        apply measurable_fun_setI1; try by eauto with measlang.
      }
      apply measurable_fun_prod'_expr; try by eauto with measlang.
      { eapply measurable_comp.
        3: { by eapply 𝜋_Val_v_meas. }
        * by eauto with measlang.
        * rewrite /subset//=.
          move=>?.
          move=>[+[+[++]]].
          move=>?.
          move=> [+[++[++]]].
          admit.
          (*
          move=>[++]; move=>?->//=.
          move=>[+[+[++]]]; move=>????.
          by move=>?<-. *)
        rewrite <-(setIid ecov_app).
        rewrite <-setIA.
        by apply measurable_fun_setI1; try by eauto with measlang.
      }
      apply measurable_compT; try by eauto with measlang.
      { by apply substU'_measurable. }
      apply measurable_fun_prod'_expr; try by eauto with measlang.
      { eapply measurable_comp.
        3: { by eapply 𝜋_RecV_f_meas. } (* FIXME: Literally one charachter changed between this an a prior case lol *)
        * by eauto with measlang.
        * rewrite /subset//=.
          move=>?[+[+[++]]].
          move=>?[+].
          admit.
          (*
          move=>?[+]; move=>?->//=.
          move=>[[++]+]; move=>?->//=.
          move=>[+[+[++]]]; move=>???->.
          move=>[++]; move=>??.
          move=><-//=.
          rewrite/vcov_rec/RecVC//=.
          by do 3 eexists. *)
        rewrite <-(setIid ecov_app).
        rewrite <-setIA.
        apply measurable_fun_setI2; try by eauto with measlang.
        eapply measurable_comp.
        3: { by eapply 𝜋_Val_v_meas. }
        * by eauto with measlang.
        * rewrite /subset//=.
          move=>?.
          move=>[+[+[++]]].
          move=>?.
          admit.
          (*
          move=> [+[++[++]]].
          move=>??->//=.
          move=>[++]; move=>?->//=.
          move=>[+[+[++]]]; move=>???->.
          move=>[++]; move=>??<-.
          rewrite /ecov_val/ValC//=.
          by eexists. *)
        rewrite <-(setIid ecov_app).
        rewrite <-setIA.
        apply measurable_fun_setI1; try by eauto with measlang.
      }
      apply measurable_fun_prod'_expr; try by eauto with measlang.
      { eapply measurable_comp.
        3: { by eapply 𝜋_Val_v_meas. }
        * by eauto with measlang.
        * rewrite /subset//=.
          move=>?.
          move=>[+[+[++]]].
          move=>?.
          admit.
          (*
          move=> [+[++[++]]].
          move=>??->//=.
          move=>[++]; move=>?->//=.
          move=>[+[+[++]]]; move=>????.
          move=>?<-.
          rewrite /ecov_val/ValC//=.
          by eexists. *)
        rewrite <-(setIid ecov_app).
        rewrite <-setIA.
        by apply measurable_fun_setI1; try by eauto with measlang.
      }
      { eapply measurable_comp.
        3: { by eapply 𝜋_RecV_e_meas. }
        * by eauto with measlang.
        * rewrite /subset//=.
          move=>?[+[+[++]]].
          admit.
          (*
          move=>?[+].
          move=>?[+]; move=>?->//=.
          move=>[[++]+]; move=>?->//=.
          move=>[+[+[++]]]; move=>???->.
          move=>[++]; move=>??.
          move=><-//=.
          rewrite/vcov_rec/RecVC//=.
          by do 3 eexists. *)
       eapply measurable_comp.
       3: { by eapply 𝜋_Val_v_meas. }
       * by eauto with measlang.
       * rewrite /subset//=.
         move=>?.
         move=>[+[+[++]]].
         move=>?.
         admit.
         (*
         move=> [+[++[++]]].
         move=>??->//=.
         move=>[++]; move=>?->//=.
         move=>[+[+[++]]]; move=>????.
         move=>?<-.
         rewrite /ecov_val/ValC//=.
         by eexists. *)
        rewrite <-(setIid ecov_app).
        rewrite <-setIA.
        by apply measurable_fun_setI1; try by eauto with measlang.
      }
    - move=>[e?].
      admit.
      (*
      move=>[[++]+].
      move=>?[++]; move=>?//=->.
      move=>[+[++]]//=.
      move=>[++]//=; move=>[+].
      move=>?//=->.
      move=>[+[++]].
      move=>??//=[+].
      move=>?->//=.
      by move=>?->//=. *)
    Unshelve. by eauto with measlang.
  Admitted.
  Hint Resolve head_stepM_app_meas : measlang.

  Lemma head_stepM_unop_ok_meas : measurable_fun cover_unop_ok head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_unop_ok head_stepM).
    - apply measurable_compT.
      { by apply cover_unop_ok_meas. }
      { by apply gRet_meas_fun. }
      eapply @measurable_fun_prod'.
      { by eauto with measlang. }
      2: { eapply @mathcomp_measurable_fun_restiction_setT.
           - by eauto with measlang.
           - by eapply @measurable_snd_restriction; eauto with measlang.
      }
      apply measurable_compT; try by eauto with measlang.
      { by apply ValU_meas_fun. }
      eapply @measurable_comp.
      3: { by eapply un_op_evalC_meas. }
      + by eauto with measlang.
      + rewrite /subset//=.
        move=>[??][[??]+]//=.
        move=>[++]//=.
        move=>?[++]//=.
        admit.
        (*
        move=>[?[+]]//=.
        move=>?->//=.
        move=>[[?+]+]//=.
        move=>[?->]//=.
        move=>[?+]//=.
        rewrite//=.
        move=>?<-.
        rewrite /auxcov_unop_ok//=.
        by eexists _. *)
      apply (@measurable_comp _ _ _ _ _ _ cover_unop_ok').
      { by eauto with measlang. }
      { rewrite /subset/cover_unop_ok//=.
        move=>?[++].
        move=>?[?+].
        by move=>?<-//.
      }
      2: { eapply @mathcomp_measurable_fun_restiction_setT.
           - by eauto with measlang.
           - by eapply @measurable_fst_restriction; eauto with measlang.
      }
      eapply @measurable_fun_prod'.
      { by eauto with measlang. }
      { unfold cover_unop_ok'.
        rewrite <-(setIid ecov_unop).
        rewrite <-setIA.
        by apply measurable_fun_setI1; try by eauto with measlang. }
      eapply @measurable_comp.
      3: { by apply 𝜋_Val_v_meas. }
      { by eauto with measlang. }
      { rewrite /subset//=.
        move=>?[++].
        move=>?[++].
        admit.
        (*
        move=>[?[++]].
        move=>?->//=.
        move=>[[?+]+].
        move=>[?+].
        move=>->//=.
        move=>[?+]//=.
        simpl.
        move=> ? <- //=.
        rewrite /ecov_val//=.
        by eexists. *)
      }
      { unfold cover_unop_ok'.
        rewrite <-(setIid ecov_unop).
        rewrite <-setIA.
        by apply measurable_fun_setI1; try by eauto with measlang. }
    - move=> [e?].
      move=>[?[+]]//=.
      admit.
      (*
      move=>[++]; move=>?//=.
      move=>[?->].
      move=>[[_[++]][++]]//=.
      move=>?//=->.
      move=>?//=.
      move=>->//=.
    Unshelve. by eauto with measlang. *)
  Admitted.
  Hint Resolve head_stepM_unop_ok_meas : measlang.

  Lemma head_stepM_unop_stuck_meas : measurable_fun cover_unop_stuck head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_unop_stuck head_stepM).
    - by apply measurable_cst.
    - move=>[e?].
      move=>[?[+]]//=.
      admit.
      (*
      move=>[?[++]]//=.
      move=>?//=->.
      move=>[[++]+]//=.
      move=>?.
      move=>[+]; move=>?//=->//=.
      rewrite /auxcov_unop_stuck//=.
      by move=>->//=.
    Unshelve. by eauto with measlang.
  Qed.*)
      Admitted.
  Hint Resolve head_stepM_unop_stuck_meas : measlang.

  Lemma head_stepM_binop_ok_meas : measurable_fun cover_binop_ok head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_binop_ok head_stepM).
    - apply measurable_compT.
      { by apply cover_binop_ok_meas. }
      { by apply gRet_meas_fun. }
  Admitted.
  (*
      eapply (@measurable_fun_prod' _ _ _ _ _ _
              (ssrfun.comp ValU (ssrfun.comp bin_op_evalC (ssrfun.comp (Package3 𝜋_BinOp_op (ssrfun.comp 𝜋_Val_v 𝜋_BinOp_l) (ssrfun.comp 𝜋_Val_v 𝜋_BinOp_r)) fst)))
              snd).
      { by eauto with measlang. }
      2: { eapply @mathcomp_measurable_fun_restiction_setT.
           - by eauto with measlang.
           - by apply measurable_snd.
      }
      apply measurable_compT; try by eauto with measlang.
      { by apply ValU_measurable. }
      eapply @measurable_comp.
      3: { by eapply bin_op_evalC_meas. }
      + by eauto with measlang.
      + rewrite /subset//=.
        move=> [[??]?][[??]+]//=.
        move=> [++]//=.
        move=> ?[++]//=.
        move=> [?[?[?+]]]//=.
        move=>//=->//=.
        move=> [[[?+]+]+]//=.
        move=> [?->]//=.
        move=> [?->]//=.
        by move=> +<-//=.
      eapply (@measurable_comp _ _ _ _ _ _ cover_binop_ok').
      4: { eapply @mathcomp_measurable_fun_restiction_setT.
           - by eauto with measlang.
           - by apply measurable_fst.
      }
      { by eauto with measlang. }
      { rewrite /subset//=.
        move=>?[[??]+]//=.
        move=>[++]//=.
        move=>?.
        by move=>+<-//=.
      }
      apply @measurable_fun_prod'.
      { by eauto with measlang. }
      { apply @measurable_fun_prod'.
        { by eauto with measlang. }
        { unfold cover_binop_ok'.
          rewrite <-(setIid ecov_binop).
          rewrite <-setIA.
          by apply measurable_fun_setI1; try by eauto with measlang. }
        { eapply @measurable_comp.
          3: { by apply 𝜋_Val_v_meas. }
          { by eauto with measlang. }
          2: { rewrite /cover_binop_ok'.
               rewrite <-(setIid ecov_binop).
               rewrite <-setIA.
               by apply measurable_fun_setI1; try by eauto with measlang. }
          { rewrite /subset//=.
            move=>?[++].
            move=>?[++].
            move=>[?[?[?+]]]//=.
            move=>->//=.
            move=>[[[?+]+][++]]//=.
            move=>[?->]//=.
            move=>[?->]//=.
            move=>??<-//=.
            rewrite /ecov_val//=.
            by eexists _.
          }
        }
      }
      { eapply @measurable_comp.
        3: { by apply 𝜋_Val_v_meas. }
        { by eauto with measlang. }
        { rewrite /subset//=.
          move=>?[++].
          move=>?+<-//=.
          rewrite /ecov_val//=.
          move=>[++]//=.
          move=>[?[?[?+]]]//=.
          move=>->//=.
          by move=>[[[?+]+]+]//=.
        }
        rewrite /cover_binop_ok'.
        rewrite <-(setIid ecov_binop).
        rewrite <-setIA.
        by apply measurable_fun_setI1; try by eauto with measlang.
      }
    - move=>[e?].
      move=>[++].
      move=>?//=.
      move=>[++]//=.
      move=>[+[+[++]]].
      move=>???->//=.
      move=>[[[?+]+]+].
      move=>[?->]//=.
      move=>[?->]//=.
      by move=>[?->]//=.
    Unshelve. by eauto with measlang.
  Qed.

*)
  Hint Resolve head_stepM_binop_ok_meas : measlang.

  Lemma head_stepM_binop_stuck_meas : measurable_fun cover_binop_stuck head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_binop_stuck head_stepM).
    - by apply measurable_cst.
    - move=>[e?].
      move=>[?+]//=.
      move=>[++]//=.
      move=>[++]//=.
      move=>?[++]//=.
(*
      move=>?[?+]//=.
      rewrite //=; move=>->//=.
      move=>[[[?+]+]+]//=.

      move=>[?+]//=; move=>->//=.
      move=>[?+]//=; move=>->//=.
      rewrite /auxcov_binop_stuck//=.
      by move=>->.
    Unshelve. by eauto with measlang.
  Qed. *)
  Admitted.
  Hint Resolve head_stepM_binop_stuck_meas : measlang.

  Lemma head_stepM_alloc_ok_meas : measurable_fun cover_alloc_ok head_stepM.
  Proof. Admitted.
  (*
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_alloc_ok).
    - mcrunch_comp.
      mcrunch_prod.
      { mcrunch_compC ValU_measurable.
        mcrunch_compC LitVU_measurable.
        mcrunch_compC LitLocU_measurable.
        mcrunch_comp.
        { rewrite /subset/cover_alloc_ok/auxcov_allocN_ok//=.
          move=> [??].
          repeat move=>[++]; move=>??//=.
          repeat move=>[++]; move=>?//=.
          repeat move=>[++]; move=>?->//=.
          repeat move=>[++]; move=>?->//=.
          repeat move=>[++]; move=>?->//=.
          repeat move=>[++]; move=>?->//=.
          repeat move=>[++]; move=>?->//=.
          repeat rewrite /aux_allocN_Z/aux_allocN_v/aux_allocN//=.
          move=>?.
          by move=>[?<-].
        }
        unfold cover_allocN_ok.
        rewrite <-(setIid auxcov_allocN).
        rewrite <-setIA.
        apply (measurable_fun_setI1 aux_allocN auxcov_allocN); by eauto with measlang.
      }
      { mcrunch_comp.
        { rewrite /subset/cover_allocN_ok/auxcov_allocN_ok//=.
          move=> [??].
          repeat move=>[++]; move=>??//=.
          repeat move=>[++]; move=>?//=.
          repeat move=>[++]; move=>?->//=.
          repeat move=>[++]; move=>?->//=.
          repeat move=>[++]; move=>?->//=.
          repeat move=>[++]; move=>?->//=.
          repeat move=>[++]; move=>?->//=.
          repeat rewrite /aux_allocN_Z/aux_allocN_v/aux_allocN//=.
          move=>?.
          by move=>[?<-].
        }
        unfold cover_allocN_ok.
        rewrite <-(setIid auxcov_allocN).
        rewrite <-setIA.
        apply (measurable_fun_setI1 aux_allocN auxcov_allocN); by eauto with measlang.
      }
    - move=> [??].
      repeat move=>[++]; move=>?//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat rewrite /auxcov_allocN_ok/aux_allocN_Z///=.
      move=> H.
      rewrite ifIn_eq_left; [done|].
      rewrite /cover_allocN_ok//=.
      split; [|done].
      rewrite /auxcov_allocN/ecov_alloc/ecov_val/vcov_lit/bcov_LitInt //=.
      split; [done|].
      split; [eexists _; eexists _; done|].
      split; [|eexists _; done].
      split; [eexists _; done|].
      split; eexists _; done.
    Unshelve. by eauto with measlang.
  Qed. *)
  Hint Resolve head_stepM_alloc_ok_meas : measlang.

  Lemma head_stepM_alloc_stuck_meas : measurable_fun cover_alloc_stuck head_stepM.
  Proof. Admitted.
  (*
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_alloc_stuck).
    - by apply measurable_cst.
    - move=> [??].
      repeat move=>[++]; move=>?//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat rewrite /auxcov_allocN_stuck/aux_allocN_Z///=.
      move=> H.
      rewrite ifIn_eq_right; [done|].
      (* Easy *)
    Admitted.
    (*
    Unshelve. by eauto with measlang.
  Qed.
*) *)
  Hint Resolve head_stepM_alloc_stuck_meas : measlang.

  Lemma head_stepM_load_ok_meas : measurable_fun cover_load_ok head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_load_ok).
    - mcrunch_comp.
      mcrunch_prod.
      2: by eapply @measurable_snd_restriction; eauto with measlang.
      mcrunch_compC ValU_meas_fun.
      mcrunch_comp.
      { rewrite /subset/auxcov_load_ok/aux_load_loc//=.
        move=>[??].
        do 3 (move=>[+]/=; move=>?//=; try move=>->//=).
        move=>?.
        do 1 (move=>[+]/=; try move=>->//=).
        do 2 move=><-//=.
        by eexists _.
      }
      mcrunch_prod; last by eapply @measurable_snd_restriction; eauto with measlang.
      mcrunch_comp; last by eapply @measurable_fst_restriction; eauto with measlang.
      { rewrite /subset/cover_load_ok/auxcov_load//=.
        move=>?.
        (repeat move=>[++]); move=>??//=.
        admit.
        (*
        (repeat move=>[++]); move=>?->//=.
        (repeat move=>[++]); move=>?->//=.
        (repeat move=>[++]); move=>?->//=.
        (repeat move=>[++]); move=>?->//=.
        move=>?//=.
        (repeat move=>[++]); move=>?//=.
        move=>?<-//=.
        rewrite /ecov_load/ecov_val/vcov_lit/bcov_LitLoc//=.
        split; first by eexists _.
        split; first by eexists _.
        split; first by eexists _.
        by eexists. *)
      }
    - move=>[??].
      repeat ((repeat move=>[++]//=); move=>?//=->//=).
      move=>?//=.
      rewrite /auxcov_load_ok//=.
      rewrite ifIn_eq_left; last first.
  Admitted.
 (*

        by repeat ((repeat move=>[++]//=); move=>?//=->//=). }
    Unshelve. by eauto with measlang.
  Qed.*)
  Hint Resolve head_stepM_load_ok_meas : measlang.

  Lemma head_stepM_load_stuck_meas : measurable_fun cover_load_stuck head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_load_stuck head_stepM).
    - by apply measurable_cst.
    - move=>[e?].
  Admitted.
  (*
      by repeat ((repeat move=>[++]//=); move=>?//=->//=).
    Unshelve. by eauto with measlang.
  Qed.
*)
  Hint Resolve head_stepM_load_stuck_meas : measlang.

  Lemma head_stepM_store_ok_meas : measurable_fun cover_store_ok head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_store_ok).
    - mcrunch_comp.
      mcrunch_prod.
      { mcrunch_comp.
        { rewrite /subset/cover_store_ok/auxcov_store//=.
          move=>[[??]?].
          (repeat move=>[++]); move=>??//=.
          (repeat move=>[++]); move=>?//=.
          admit.
          (*
          (repeat move=>[++]); move=>?->//=.
          (repeat move=>[++]); move=>?->//=.
          (repeat move=>[++]); move=>?->//=.
          (repeat move=>[++]); move=>?->//=.
          (repeat move=>[++]); move=>?->//=.
          repeat (rewrite /auxcov_store_ok/aux_store_loc/aux_store/aux_store_v//=).
          (repeat move=>[++]); move=>?//=.
          move=>?.
          move=>[+].
          move=><-?<-.
          by eexists _.
*)
        }
        unfold cover_store_ok.
        rewrite <-(setIid auxcov_store).
        rewrite <-setIA.
        apply (measurable_fun_setI1 aux_store auxcov_store); by eauto with measlang.
      }
      { mcrunch_comp.
        { rewrite /subset/cover_store_ok/auxcov_store//=.
          move=>[[??]?].
          (repeat move=>[++]); move=>??//=.
          (repeat move=>[++]); move=>?//=.
          admit.
          (*
          (repeat move=>[++]); move=>?->//=.
          (repeat move=>[++]); move=>?->//=.
          (repeat move=>[++]); move=>?->//=.
          (repeat move=>[++]); move=>?->//=.
          (repeat move=>[++]); move=>?->//=.
          repeat (rewrite /auxcov_store_ok/aux_store_loc/aux_store/aux_store_v//=).
          (repeat move=>[++]); move=>?//=.
          move=>?.
          move=>[+].
          move=><-?<-.
          by eexists _.
          *)
        }
        unfold cover_store_ok.
        rewrite <-(setIid auxcov_store).
        rewrite <-setIA.
        apply (measurable_fun_setI1 aux_store auxcov_store); by eauto with measlang.
      }
    - move=>[e?].
      (repeat move=>[++]); move=>?//=.
      admit.
      (*
      (repeat move=>[++]); move=>?->//=.
      (repeat move=>[++]); move=>?->//=.
      (repeat move=>[++]); move=>?->//=.
      (repeat move=>[++]); move=>?->//=.
      (repeat move=>[++]); move=>?->//=.
      rewrite /auxcov_store_ok//=. *)
    Admitted.
  (*
      by (repeat move=>[++]); move=>?->//=.
    Unshelve. by eauto with measlang.
  Qed.
*)
  Hint Resolve head_stepM_store_ok_meas : measlang.

  Lemma head_stepM_store_stuck_meas : measurable_fun cover_store_stuck head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_store_stuck).
    - by apply measurable_cst.
    - move=>[e?].
      (repeat move=>[++]); move=>?//=.
      (*
      (repeat move=>[++]); move=>?->//=.
      (repeat move=>[++]); move=>?->//=.
      (repeat move=>[++]); move=>?->//=.
      (repeat move=>[++]); move=>?->//=.
      (repeat move=>[++]); move=>?->//=.
      rewrite /auxcov_store_stuck//=.
      *)
    Admitted.
  (*
      by move=>->.
    Unshelve. by eauto with measlang.
  Qed.
*)
  Hint Resolve head_stepM_load_stuck_meas : measlang.


  Lemma head_stepM_ifT_meas : measurable_fun cover_ifT head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_ifT head_stepM).
    - apply measurable_compT.
      { by apply cover_ifT_meas. }
      { by apply gRet_meas_fun. }
      have S : expr_cyl.-sigma.-measurable (ecov_if `&` 𝜋_If_c @^-1` (ecov_val `&` 𝜋_Val_v @^-1` (vcov_lit `&` 𝜋_LitV_v @^-1` (bcov_LitBool `&` 𝜋_LitBool_b @^-1` [set true])))).
     { apply 𝜋_If_c_meas; first by eauto with measlang.
       apply 𝜋_Val_v_meas; first by eauto with measlang.
       apply 𝜋_LitV_v_meas; first by eauto with measlang.
       apply 𝜋_LitBool_b_meas; first by eauto with measlang.
       by rewrite /measurable/discr_measurable//=.
      }
      apply @NonStatefulU_meas; first done.
      rewrite <-(setIid ecov_if).
      rewrite <-setIA.
      by apply measurable_fun_setI1; eauto with measlang.
    - move=>[e?].
    Admitted.
  (*
      move=>/=[+]; do 3 move=>[?+].
      move=>//=->.
      move=>[+[+[++]]]/=.
      move=>/=[+]; move=>?->.
      move=>/=[+]; move=>?->.
      move=>/=[+]; move=>?->.
      move=>/=->//=.
    Unshelve. by eauto with measlang.
  Qed. *)
  Hint Resolve head_stepM_ifT_meas : measlang.

  Lemma head_stepM_ifF_meas : measurable_fun cover_ifF head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_ifT head_stepM).
    - apply measurable_compT.
      { by apply cover_ifF_meas. }
      { by apply gRet_meas_fun. }
      have S : expr_cyl.-sigma.-measurable (ecov_if `&` 𝜋_If_c @^-1` (ecov_val `&` 𝜋_Val_v @^-1` (vcov_lit `&` 𝜋_LitV_v @^-1` (bcov_LitBool `&` 𝜋_LitBool_b @^-1` [set false])))).
     { apply 𝜋_If_c_meas; first by eauto with measlang.
       apply 𝜋_Val_v_meas; first by eauto with measlang.
       apply 𝜋_LitV_v_meas; first by eauto with measlang.
       apply 𝜋_LitBool_b_meas; first by eauto with measlang.
       by rewrite /measurable/discr_measurable//=.
      }
      apply @NonStatefulU_meas; first done.
      rewrite <-(setIid ecov_if).
      rewrite <-setIA.
      by apply measurable_fun_setI1; eauto with measlang.
    - move=>[e?].
  Admitted.
  (*
      move=>/=[+]; do 3 move=>[?+].
      move=>//=->.
      move=>[+[+[++]]]/=.
      move=>/=[+]; move=>?->.
      move=>/=[+]; move=>?->.
      move=>/=[+]; move=>?->.
      move=>/=->//=.
    Unshelve. by eauto with measlang.
  Qed. *)
  Hint Resolve head_stepM_ifF_meas : measlang.

  Lemma head_stepM_fst_meas : measurable_fun cover_fst head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_fst head_stepM).
    - apply measurable_compT.
      { by apply cover_fst_meas. }
      { by apply gRet_meas_fun. }
      have S : expr_cyl.-sigma.-measurable (ecov_fst `&` 𝜋_Fst_e @^-1` (ecov_val `&` 𝜋_Val_v @^-1` vcov_pair)).
      { apply 𝜋_Fst_e_meas; first by eauto with measlang.
        apply 𝜋_Val_v_meas; first by eauto with measlang.
        by eauto with measlang. }
      apply @NonStatefulU_meas; first done.
      apply measurable_compT; try by eauto with measlang.
      + by apply ValU_meas_fun.
      eapply measurable_comp.
      3: { by apply 𝜋_PairV_l_meas. }
      * by eauto with measlang.
      * rewrite /subset//=.
        move=>?[+[+[++]]].
        by move=>????<-//=.
      eapply measurable_comp.
      3: { by apply 𝜋_ValU_meas. }
      * by eauto with measlang.
      * rewrite /subset//=.
        move=>?[+[+[++]]].
        by move=>????<-//=.
      * rewrite <-(setIid ecov_fst).
        rewrite <-setIA.
        apply measurable_fun_setI1; try by eauto with measlang.
    - move=>[e?].
      move=>/=[+]; move=>[?+].
  Admitted.
  (*
      move=>//=->.
      move=>[++]/=.
      move=>/=[+]; move=>?->.
      move=>[+]/=; move=>?.
      move=>[+]/=; move=>?.
      by move=>->/=.
    Unshelve. by eauto with measlang.
  Qed. *)
  Hint Resolve head_stepM_fst_meas : measlang.

  Lemma head_stepM_snd_meas : measurable_fun cover_snd head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_snd head_stepM).
    - apply measurable_compT.
      { by apply cover_snd_meas. }
      { by apply gRet_meas_fun. }
      have S : expr_cyl.-sigma.-measurable (ecov_snd `&` 𝜋_Snd_e @^-1` (ecov_val `&` 𝜋_Val_v @^-1` vcov_pair)).
      { apply 𝜋_Snd_e_meas; first by eauto with measlang.
        apply 𝜋_Val_v_meas; first by eauto with measlang.
        by eauto with measlang. }
      apply @NonStatefulU_meas; first done.
      apply measurable_compT; try by eauto with measlang.
      + by apply ValU_meas_fun.
      eapply measurable_comp.
      3: { by apply 𝜋_PairV_r_meas. }
      * by eauto with measlang.
      * rewrite /subset//=.
        move=>?[+[+[++]]].
        by move=>????<-//=.
      eapply measurable_comp.
      3: { by apply 𝜋_ValU_meas. }
      * by eauto with measlang.
      * rewrite /subset//=.
        move=>?[+[+[++]]].
        by move=>????<-//=.
      * rewrite <-(setIid ecov_snd).
        rewrite <-setIA.
        apply measurable_fun_setI1; try by eauto with measlang.
    - move=>[e?].
      move=>/=[+]; move=>[?+].
  Admitted.
  (*
      move=>//=->.
      move=>[++]/=.
      move=>/=[+]; move=>?->.
      move=>[+]/=; move=>?.
      move=>[+]/=; move=>?.
      by move=>->/=.
    Unshelve. by eauto with measlang.
  Qed. *)
  Hint Resolve head_stepM_snd_meas : measlang.

  Lemma head_stepM_caseL_meas : measurable_fun cover_caseL head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_caseL head_stepM).
    - apply measurable_compT.
      { by apply cover_caseL_meas. }
      { by apply gRet_meas_fun. }
      have S : expr_cyl.-sigma.-measurable (ecov_case `&` 𝜋_Case_c @^-1` (ecov_val `&` 𝜋_Val_v @^-1` vcov_injlv)).
      { apply 𝜋_Case_c_meas; first by eauto with measlang.
        apply 𝜋_Val_v_meas; first by eauto with measlang.
        by eauto with measlang.
      }
      apply @NonStatefulU_meas; first done.
      apply measurable_compT; try by eauto with measlang.
      + by apply AppU_meas_fun.
      apply measurable_fun_prod'_expr; try by eauto with measlang.
      + rewrite <-(setIid ecov_case).
        rewrite <-setIA.
        apply measurable_fun_setI1; try by eauto with measlang.
        apply measurable_compT; try by eauto with measlang.
        + by apply ValU_meas_fun.
        eapply measurable_comp.
        3: { by apply 𝜋_InjLV_v_meas. }
        * by eauto with measlang.
        * rewrite /subset//=.
          move=>?[+[+[++]]].
          by move=>????<-//=.
        eapply measurable_comp.
        3: { by apply 𝜋_Val_v_meas. }
        * by eauto with measlang.
        * rewrite /subset//=.
          move=>?[+[+[++]]].
          by move=>????<-//=.
        rewrite <-(setIid ecov_case).
        rewrite <-setIA.
        by apply measurable_fun_setI1; try by eauto with measlang.
    - move=>[e?].
      move=>/=[+]; move=>[?+].
  Admitted.
  (*
      move=>/=[?[?->]]/=.
      move=>[[++][++]]//=.
      do 2 move=>?//=->.
      by move=>//=.
    Unshelve. by eauto with measlang.
  Qed. *)
  Hint Resolve head_stepM_caseL_meas : measlang.

  Lemma head_stepM_caseR_meas : measurable_fun cover_caseR head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_caseR head_stepM).
    - apply measurable_compT.
      { by apply cover_caseR_meas. }
      { by apply gRet_meas_fun. }
      have S : expr_cyl.-sigma.-measurable (ecov_case `&` 𝜋_Case_c @^-1` (ecov_val `&` 𝜋_Val_v @^-1` vcov_injrv)).
      { apply 𝜋_Case_c_meas; first by eauto with measlang.
        apply 𝜋_Val_v_meas; first by eauto with measlang.
        by eauto with measlang.
      }
      apply @NonStatefulU_meas; first done.
      apply measurable_compT; try by eauto with measlang.
      + by apply AppU_meas_fun.
      apply measurable_fun_prod'_expr; try by eauto with measlang.
      + rewrite <-(setIid ecov_case).
        rewrite <-setIA.
        apply measurable_fun_setI1; try by eauto with measlang.
        apply measurable_compT; try by eauto with measlang.
        + by apply ValU_meas_fun.
        eapply measurable_comp.
        3: { by apply 𝜋_InjRV_v_meas. }
        * by eauto with measlang.
        * rewrite /subset//=.
          move=>?[+[+[++]]].
          by move=>????<-//=.
        eapply measurable_comp.
        3: { by apply 𝜋_Val_v_meas. }
        * by eauto with measlang.
        * rewrite /subset//=.
          move=>?[+[+[++]]].
          by move=>????<-//=.
        rewrite <-(setIid ecov_case).
        rewrite <-setIA.
        by apply measurable_fun_setI1; try by eauto with measlang.
    - move=>[e?].
      move=>/=[+]; move=>[?+].
  Admitted.

  (*
      move=>/=[?[?->]]/=.
      move=>[[++][++]]//=.
      do 2 move=>?//=->.
      by move=>//=.
    Unshelve. by eauto with measlang.
  Qed. *)
  Hint Resolve head_stepM_caseR_meas : measlang.

  Lemma head_stepM_allocTape_meas : measurable_fun cover_allocTape head_stepM.
  Proof.
  Admitted.
  Hint Resolve head_stepM_allocTape_meas : measlang.

  Lemma head_stepM_allocUTape_meas : measurable_fun cover_allocUTape head_stepM.
  Proof.
  Admitted.
  Hint Resolve head_stepM_allocUTape_meas : measlang.

  Lemma head_stepM_rand_meas : measurable_fun cover_rand head_stepM.
  Proof.
  Admitted.
  Hint Resolve head_stepM_rand_meas : measlang.

  Lemma head_stepM_urand_meas : measurable_fun cover_urand head_stepM.
  Proof.
  Admitted.
  Hint Resolve head_stepM_urand_meas : measlang.

  Lemma head_stepM_randT_meas : measurable_fun cover_randT head_stepM.
  Proof.
  Admitted.
  Hint Resolve head_stepM_randT_meas : measlang.

  Lemma head_stepM_urandT_meas : measurable_fun cover_urandT head_stepM.
  Proof.
  Admitted.
  Hint Resolve head_stepM_urandT_meas : measlang.

  Lemma head_stepM_tick_meas : measurable_fun cover_tick head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_tick head_stepM).
    - apply measurable_compT.
      { by apply cover_tick_meas. }
      { by apply gRet_meas_fun. }
      have S : expr_cyl.-sigma.-measurable (ecov_tick `&` 𝜋_Tick_e @^-1` (ecov_val `&` 𝜋_Val_v @^-1` (vcov_lit `&` 𝜋_LitV_v @^-1` bcov_LitInt))).
      { apply 𝜋_Tick_e_meas; first by eauto with measlang.
        apply 𝜋_Val_v_meas; first by eauto with measlang.
        apply 𝜋_LitV_v_meas; first by eauto with measlang.
        by eauto with measlang. }
      apply @NonStatefulU_meas; first done.
      apply measurable_compT; try by eauto with measlang.
      + by apply ValU_meas_fun.
      apply measurable_compT; try by eauto with measlang.
      + by apply LitVU_meas_fun.
    - move=>[e?].
      move=>/=[+]; move=>[?+].
  Admitted.
  (*
      move=>//=->.
      move=>[+[++]]/=.
      move=>/=[+]; move=>?->.
      move=>[+]/=; move=>?->.
      move=>[+]/=; move=>?->.
      by move=>//=.
    Unshelve. by eauto with measlang.
  Qed. *)
  Hint Resolve head_stepM_tick_meas : measlang.

  Lemma head_stepM_stuck_meas : measurable_fun cover_maybe_stuck head_stepM.
  Proof.
    unfold cover_maybe_stuck.
    (* Need to show that, if its not in any of the prior cases, its in the last case
       Probably the easiest way to do this:
          Unfold foldr
          Distribute ~` over disjunction, destruct conjunction
          Case split on expr, by cases get false
     *)
  Admitted.
  Hint Resolve head_stepM_stuck_meas : measlang.

*)

(*

  (**  Head step measurability *)
  Lemma cfg_cover_measurable :
      Forall (fun S => measurable S) cfg_cover.
  Proof.
    repeat (try apply Forall_cons; split); last by apply List.Forall_nil.
    - by apply cover_maybe_stuck_meas.
    - by apply cover_rec_meas.
    - by apply cover_pair_meas.
    - by apply cover_injL_meas.
    - by apply cover_injR_meas.
    - by apply cover_app_meas.
    - by apply cover_unop_ok_meas.
    - by apply cover_unop_stuck_meas.
    - by apply cover_binop_ok_meas.
    - by apply cover_binop_stuck_meas.
    - by apply cover_ifT_meas.
    - by apply cover_ifF_meas.
    - by apply cover_fst_meas.
    - by apply cover_snd_meas.
    - by apply cover_caseL_meas.
    - by apply cover_caseR_meas.
    - by apply cover_alloc_ok_meas.
    - by apply cover_alloc_stuck_meas.
    - by apply cover_load_ok_meas.
    - by apply cover_load_stuck_meas.
    - by apply cover_store_ok_meas.
    - by apply cover_store_stuck_meas.
    - by apply cover_allocTape_meas.
    - by apply cover_allocUTape_meas.
    - by apply cover_rand_meas.
    - by apply cover_urand_meas.
    - by apply cover_randT_meas.
    - by apply cover_urandT_meas.
    - by apply cover_tick_meas.
  Qed.

  Lemma head_stepM_restricted_measurable :
      Forall (fun S => measurable_fun S head_stepM) cfg_cover.
  Proof.
    repeat (try apply Forall_cons; split); last by apply List.Forall_nil.
    - by apply head_stepM_stuck_meas.
    - by apply head_stepM_rec_meas.
    - by apply head_stepM_pair_meas.
    - by apply head_stepM_injL_meas.
    - by apply head_stepM_injR_meas.
    - by apply head_stepM_app_meas.
    - by apply head_stepM_unop_ok_meas.
    - by apply head_stepM_unop_stuck_meas.
    - by apply head_stepM_binop_ok_meas.
    - by apply head_stepM_binop_stuck_meas.
    - by apply head_stepM_ifT_meas.
    - by apply head_stepM_ifF_meas.
    - by apply head_stepM_fst_meas.
    - by apply head_stepM_snd_meas.
    - by apply head_stepM_caseL_meas.
    - by apply head_stepM_caseR_meas.
    - by apply head_stepM_alloc_ok_meas.
    - by apply head_stepM_alloc_stuck_meas.
    - by apply head_stepM_load_ok_meas.
    - by apply head_stepM_load_stuck_meas.
    - by apply head_stepM_store_ok_meas.
    - by apply head_stepM_store_stuck_meas.
    - by apply head_stepM_allocTape_meas.
    - by apply head_stepM_allocUTape_meas.
    - by apply head_stepM_rand_meas.
    - by apply head_stepM_urand_meas.
    - by apply head_stepM_randT_meas.
    - by apply head_stepM_urandT_meas.
    - by apply head_stepM_tick_meas.
  Qed.

  Lemma head_stepM_measurable :
    @measurable_fun _ _ cfg (giryM cfg) setT head_stepM.
  Proof.
    apply (@measurable_by_cover_list _ _ _ _ head_stepM cfg_cover).
    - by apply cfg_cover_measurable.
    - by apply cfg_cover_is_cover.
    - suffices HFdep :
          (Forall (λ l : set cfg,
                     elem_of_list l cfg_cover ->
                     measurable_fun (T:=cfg) (U:=giryM cfg) l (head_stepM \_ l)) cfg_cover).
      { apply Forall_forall.
        intros x Hx.
        by apply (iffLR (Forall_forall _ _) HFdep x Hx Hx).
      }
      eapply (Forall_impl _ _ _ head_stepM_restricted_measurable).
      intros S H HS.

      (*
      apply @mathcomp_restriction_is_measurable in H.
      { eapply @Forall_forall; last first.

        - admit.
        - (*  by apply cfg_cover_measurable. *) admit.
        - by apply HS. }
      by apply mathcomp_restriction_setT.
      *)
  Admitted.

End meas_semantics.
*)

(*


(** UnOp  *)

Definition un_op_evalC (x : (<<discr un_op >> * val)%type) : val
  := match (un_op_eval x.1 x.2) with
     | Some v => v
     | None => inhabitant
     end.

Definition auxcov_unop_ok : set (<<discr un_op>> * val)%type :=
  [set x | ∃ w, un_op_eval x.1 x.2 = Some w].

Definition auxcov_unop_stuck : set (<<discr un_op>> * val)%type :=
  [set x | un_op_eval x.1 x.2 = None].

Definition aux_aux_unop_1 : set (<<discr un_op>> * val)%type :=
  setX [set NegOp] (setI vcov_lit $ preimage 𝜋_LitV_v $ bcov_LitBool).

Definition aux_aux_unop_2 : set (<<discr un_op>> * val)%type :=
  setX [set NegOp] (setI vcov_lit $ preimage 𝜋_LitV_v $ bcov_LitInt).

Definition aux_aux_unop_3 : set (<<discr un_op>> * val)%type :=
  setX [set MinusUnOp] (setI vcov_lit $ preimage 𝜋_LitV_v $ bcov_LitInt).

Definition aux_aux_unop_4 : set (<<discr un_op>> * val)%type :=
  setX [set MinusUnOp] (setI vcov_lit $ preimage 𝜋_LitV_v $ bcov_LitReal).

Lemma aux_aux_unop_1_meas : measurable aux_aux_unop_1.
Proof. apply measurableX; [by rewrite /measurable//= |]. apply 𝜋_LitV_v_meas; by eauto with measlang. Qed.

Lemma aux_aux_unop_2_meas : measurable aux_aux_unop_2.
Proof. apply measurableX; [by rewrite /measurable//= |]. apply 𝜋_LitV_v_meas; by eauto with measlang. Qed.

Lemma aux_aux_unop_3_meas : measurable aux_aux_unop_3.
Proof. apply measurableX; [by rewrite /measurable//= |]. apply 𝜋_LitV_v_meas; by eauto with measlang. Qed.

Lemma aux_aux_unop_4_meas : measurable aux_aux_unop_4.
Proof. apply measurableX; [by rewrite /measurable//= |]. apply 𝜋_LitV_v_meas; by eauto with measlang. Qed.

Lemma aux_unop : auxcov_unop_ok = aux_aux_unop_1 `|` aux_aux_unop_2 `|` aux_aux_unop_3 `|` aux_aux_unop_4.
Proof.
  rewrite /auxcov_unop_ok/aux_aux_unop_1/aux_aux_unop_2/aux_aux_unop_3/aux_aux_unop_4/setU/=.
  apply /predeqP =>[[y1 y2]] /=.
  split.
  { repeat move=> [+]; move=>?//=.
    destruct y1.
    all: move=>//=.
    all: destruct y2.
    all: move=>//=.
    all: destruct l.
    all: move=>//=?.
    1: left; left; right.
    2: left; left; left.
    3: left; right.
    4: right.
    all: split; rewrite //.
    all: rewrite /vcov_lit/bcov_LitInt/bcov_LitBool/bcov_LitReal//=.
    all: by split; eexists. }
  { move=>[[[[->[++]]|[->[++]]]|[->[++]]]|[->[++]]].
Admitted.
(*
    all: repeat move=> [+]; move=>?->.
    all: repeat move=> [+]; move=>?//=->.
    all: by eexists _; move=>//=. }
Qed.
 *)
Lemma auxcov_unop_ok_meas : measurable auxcov_unop_ok.
Proof.
  rewrite aux_unop.
  eapply @measurableU; last by apply aux_aux_unop_4_meas.
  eapply @measurableU; last by apply aux_aux_unop_3_meas.
  eapply @measurableU; last by apply aux_aux_unop_2_meas.
  by apply aux_aux_unop_1_meas.
Qed.
Hint Resolve auxcov_unop_ok_meas : measlang.

Lemma aux_unop' : auxcov_unop_stuck = ~` auxcov_unop_ok.
Proof.
  rewrite /auxcov_unop_stuck/setC/auxcov_unop_ok.
  apply /predeqP =>[[y1 y2]] /=.
  split.
  { all: rewrite/un_op_eval//=.
    all: destruct y1.
    all: move=>//=.
    all: destruct y2.
    all: move=>//=.
    all: try by move=>? [? HK]; inversion HK.
    all: destruct l.
    all: move=>//=?.
    all: by move=> [? HK]; inversion HK. }
  { all: rewrite/un_op_eval//=.
    all: destruct y1.
    all: move=>//=.
    all: destruct y2.
    all: move=>//=.
    all: destruct l.
    all: move=>//= H.
    all: exfalso; apply H.
    all: by eexists _. }
Qed.

Lemma auxcov_unop_stuck_meas : measurable auxcov_unop_stuck.
Proof. by rewrite aux_unop'; eapply @measurableC, auxcov_unop_ok_meas. Qed.
Hint Resolve auxcov_unop_stuck_meas : measlang.

Lemma un_op_evalC_meas : measurable_fun auxcov_unop_ok un_op_evalC.
Proof.
(* Cover argument *)
Admitted.
Hint Resolve un_op_evalC_meas : measlang.


(** BinOp  *)

Definition auxcov_binop_ok : set (<<discr bin_op>> * val * val)%type :=
  [set x | ∃ w, bin_op_eval x.1.1 x.1.2 x.2 = Some w].

Definition auxcov_binop_stuck : set (<<discr bin_op>> * val * val)%type :=
  [set x | bin_op_eval x.1.1 x.1.2 x.2 = None].

Definition bin_op_evalC (x : (<<discr bin_op >> * val * val)%type) : val
  := match (bin_op_eval x.1.1 x.1.2 x.2) with
     | Some v => v
     | None => inhabitant
     end.

Lemma auxcov_binop_ok_meas : measurable auxcov_binop_ok.
Proof.
Admitted.
Hint Resolve auxcov_binop_ok_meas : measlang.

Lemma auxcov_binop_stuck_meas : measurable auxcov_binop_stuck.
Proof.
Admitted.
Hint Resolve auxcov_binop_stuck_meas : measlang.

Lemma bin_op_evalC_meas : measurable_fun auxcov_binop_ok bin_op_evalC.
Proof.
Admitted.
Hint Resolve bin_op_evalC_meas : measlang.


(*


Definition is_unop :


Definition unop_matcher_cover : list (set (<<discr un_op>> * val)) :=
  [ [set x | ∃ w, un_op_eval x.1 x.2 = Some w ];
    [set x | un_op_eval x.1 x.2 = None ] ].



Definition head_stepM_unop_destructor : expr -> (<<discr un_op>> * val)%type :=
  (mProd
    𝜋_UnOp_op
    (ssrfun.comp 𝜋_Val_v 𝜋_UnOp_e)).

(* TODO: delete *)
Definition Some_get {T : Type} [_ : Inhabited T] (x : option T) : T :=
  match x with
  | Some w => w
  | None => inhabitant
  end.

Definition head_stepM_unop_matcher_ok : <<discr un_op>> * val -> giryM expr :=
  ssrfun.comp (giryM_ret R) $
  ssrfun.comp ValC $
  ssrfun.comp (@Some_get val _)
  (uncurry un_op_eval).

Definition head_stepM_unop_matcher_stuck : <<discr un_op>> * val -> giryM expr :=
  cst giryM_zero.

Definition head_stepM_unop_matcher (x : <<discr un_op>> * val) : giryM expr :=
  match (un_op_eval x.1 x.2) with
  | Some _ => head_stepM_unop_matcher_ok x
  | None => head_stepM_unop_matcher_stuck x
  end.

(*  Plan: Split the implmenetation into a projection and two construction part(s)
      Do a different construction part depending on if unop_ok

  (* [set (op, Val v) | un_op_eval op v = Some _ ]*)
  Definition unop_cover_ok : set (<<discr un_op >> * expr) :=
    setI
      (setX setT ecov_val)
      [set x | ∃ w, un_op_eval x.1 (𝜋_Val_v x.2) = Some w ].

  (* [set (op, Val v) | un_op_eval op v = Some _ ]*)
  Definition unop_cover_stuck : set (<<discr un_op >> * expr) :=
    setD
      (setX setT ecov_val)
      [set x | un_op_eval x.1 (𝜋_Val_v x.2) = None ].

  (* [set c | ∃ v op w σ,     c = (UnOp op (Val v), σ) /\ un_op_eval op v = Some w] *)
  Program Definition cover_unop_ok : set cfg :=
    setI cover_unop_ok

  (*
     [set c | ∃ v op σ,       c = (UnOp op (Val v), σ) /\ un_op_eval op v = None ].
     [set c | ∃ v1 v2 op w σ, c = (BinOp op (Val v1) (Val v2), σ) /\ bin_op_eval op v1 v2 = Some w].
     [set c | ∃ v1 v2 op σ,   c = (BinOp op (Val v1) (Val v2), σ) /\ bin_op_eval op v1 v2 = None].
   *)
    _.
   *)


  Lemma unop_matcher_cover_ok_meas :
    (default_measure_display, val_cyl.-sigma).-prod.-measurable ([set x | ∃ w : val, un_op_eval x.1 x.2 = Some w] : (set (<<discr un_op>> * val))).
  Proof. Admitted.

  Lemma unop_matcher_cover_stuck_meas :
    (default_measure_display, val_cyl.-sigma).-prod.-measurable ([set x | un_op_eval x.1 x.2 = None] : (set (<<discr un_op>> * val))).
  Proof. Admitted.

  Lemma unop_matcher_cover_measurable :
      Forall ((default_measure_display, val_cyl.-sigma).-prod.-measurable) unop_matcher_cover.
  Proof.
    repeat (try apply Forall_cons; split); last by apply List.Forall_nil.
    + by apply unop_matcher_cover_ok_meas.
    + by apply unop_matcher_cover_stuck_meas.
  Qed.

  Lemma head_stepM_unop_matcher_restricted_measurable :
      Forall (fun S => measurable_fun S head_stepM_unop_matcher) unop_matcher_cover.
  Proof.
    repeat (try apply Forall_cons; split); last by apply List.Forall_nil.
    + eapply (mathcomp_measurable_fun_ext _ _ head_stepM_unop_matcher_ok head_stepM_unop_matcher).
      - rewrite /head_stepM_unop_matcher_ok.
        apply measurable_compT; try by eauto with measlang.
        { by apply unop_matcher_cover_ok_meas. }
        { apply measurable_compT; try by eauto with measlang.
          - admit. (*  by apply unop_matcher_cover_ok_meas.  *) }
        admit.
      - move=> [e?]//=.
        move=> [?+].
        rewrite /head_stepM_unop_matcher//=.
        by move=>->//=.
    + eapply (mathcomp_measurable_fun_ext _ _ head_stepM_unop_matcher_stuck head_stepM_unop_matcher).
      - by eapply measurable_cst.
      - move=> [e?]//=.
        rewrite /head_stepM_unop_matcher//=.
        by move=>->//=.
  Admitted.

  Lemma head_stepM_matcher_meas : measurable_fun setT head_stepM_unop_matcher.
  Proof.
    apply (@measurable_by_cover_list _ _ _ _ head_stepM_unop_matcher unop_matcher_cover).
    - by apply unop_matcher_cover_measurable.
    - rewrite /unop_matcher_cover//=.
      apply /predeqP =>y /=.
      split.
      + by move=>?.
      + move=>_.
        remember (un_op_eval y.1 y.2) as X.
        rewrite -HeqX; clear HeqX.
        destruct X; simpl.
        * left; by eexists.
        * by right; left.
    - suffices HFdep : (Forall (λ l, elem_of_list l unop_matcher_cover ->
                     measurable_fun  l (head_stepM_unop_matcher \_ l)) unop_matcher_cover).
      { apply Forall_forall.
        intros x Hx.
        by apply (iffLR (Forall_forall _ _) HFdep x Hx Hx).
      }
      eapply (Forall_impl _ _ _ head_stepM_unop_matcher_restricted_measurable).
      intros S H HS.
      eapply @mathcomp_restriction_is_measurable in H; last first.
     { eapply @Forall_forall; last by eapply HS.
        by apply unop_matcher_cover_measurable. }
      eapply @mathcomp_restriction_setT.
      by eapply H.
  Qed.

  Definition head_stepM_unop_destructor_domain : set expr :=
    setI ecov_unop $
    preimage 𝜋_UnOpU $
    setX setT ecov_val.

  Lemma head_stepM_unop_destructor_domain_meas : measurable head_stepM_unop_destructor_domain.
  Proof.
    apply 𝜋_UnOpU_meas; try by eauto with measlang.
    apply measurableX ; by eauto with measlang.
  Qed.

  Lemma head_stepM_destructor_meas :
    measurable_fun head_stepM_unop_destructor_domain head_stepM_unop_destructor.
  Proof.
    apply measurable_fun_prod'_expr; first by apply head_stepM_unop_destructor_domain_meas.
    rewrite /head_stepM_unop_destructor_domain.
    rewrite <-(setIid ecov_unop).
    rewrite <-setIA.
    apply measurable_fun_setI1; try by eauto with measlang.
    { apply 𝜋_UnOpU_meas; try by eauto with measlang.
      apply measurableX ; by eauto with measlang. }
    rewrite /head_stepM_unop_destructor_domain.
    eapply measurable_comp.
    3: { by eapply 𝜋_Val_v_meas. }
    + by eauto with measlang.
    + rewrite /subset//=.
      move=>?[++].
      move=>?[[+[++]]+].
      move=>??->[++].
      move=>_[++]//=.
      move=>?//=.
      move=>-><-//=.
      rewrite /ecov_val//=.
      by eexists.
    rewrite <-(setIid ecov_unop).
    rewrite <-setIA.
    apply measurable_fun_setI1; try by eauto with measlang.
    apply 𝜋_UnOpU_meas; try by eauto with measlang.
    apply measurableX ; by eauto with measlang.
  Qed.
*)
*)

(*


(*
    | AllocTape (Val (LitV (LitInt z))) =>
        let ι := fresh_loc σ1.(tapes) in
        giryM_ret R ((Val $ LitV $ LitLbl ι, state_upd_tapes <[ι := {| btape_tape := emptyTape ; btape_bound := (Z.to_nat z) |} ]> σ1) : cfg)
*)

Definition rand_allocTapeE : (<<discr Z>> * state)%type -> <<discr loc>> :=
  ssrfun.comp fresh $ ssrfun.comp tapes snd.


Definition new_btape : <<discr Z>> -> btape :=
  fun z => (Z.to_nat z, emptyTape).

Lemma new_btape_meas : measurable_fun setT new_btape.
Proof.
  (* <<discr Z>> is discrete *)
Admitted.


Definition rand_allocTapeS : (<<discr Z>> * state)%type -> state :=
  ssrfun.comp state_of_prod $
  mProd
    (mProd (ssrfun.comp heap snd)
      (ssrfun.comp hp_updateC $
        mProd
          (ssrfun.comp fresh $ ssrfun.comp tapes snd)
          (mProd
            (ssrfun.comp Some $ ssrfun.comp new_btape fst)
            (ssrfun.comp tapes snd))))
    (ssrfun.comp utapes snd).


Definition rand_allocTape_ok_cov : set (<<discr Z>> * state) :=
  setX setT $ preimage tapes (hp_finite _).

Lemma rand_allocTape_ok_cov_meas : measurable rand_allocTape_ok_cov.
Proof. Admitted.

(*  state_upd_tapes <[ (fresh_loc x.2.(tapes)) := {| btape_tape := emptyTape ; btape_bound := Z.to_nat x.1 |} ]> x.2. *)

Lemma rand_allocTapeE_meas : measurable_fun rand_allocTape_ok_cov  rand_allocTapeE. Admitted.
Hint Resolve rand_allocTapeE_meas : measlang.

Lemma rand_allocTapeS_meas : measurable_fun rand_allocTape_ok_cov  rand_allocTapeS. Admitted.
Hint Resolve rand_allocTapeS_meas : measlang.

(*
    | AllocUTape =>
        let ι := fresh_loc σ1.(utapes) in
        giryM_ret R ((Val $ LitV $ LitLbl ι, state_upd_utapes <[ ι := emptyTape ]> σ1) : cfg)
*)

Definition rand_allocUTapeE : state -> <<discr loc>> :=
  ssrfun.comp fresh utapes.

Definition rand_allocUTapeS : state -> state :=
  ssrfun.comp state_of_prod $
  mProd (mProd heap tapes)
  (ssrfun.comp hp_updateC $
    mProd
      (ssrfun.comp fresh utapes)
      (mProd (ssrfun.comp Some $ cst emptyTape) utapes)).


Definition rand_allocUTape_ok_cov : set state :=
  preimage tapes (hp_finite _).

Lemma rand_allocUTape_ok_cov_meas : measurable rand_allocTape_ok_cov.
Proof. Admitted.

(*   state_upd_utapes <[ (fresh_loc x.(utapes)) := emptyTape ]> x. *)

Lemma rand_allocUTapeE_meas : measurable_fun rand_allocUTape_ok_cov rand_allocUTapeE. Admitted.
Hint Resolve rand_allocUTapeE_meas : measlang.

Lemma rand_allocUTapeS_meas : measurable_fun rand_allocUTape_ok_cov  rand_allocUTapeS. Admitted.
Hint Resolve rand_allocUTapeS_meas : measlang.





(**  Rand no tape *)

(*
    | Rand (Val (LitV (LitInt N))) (Val (LitV LitUnit)) =>
        giryM_map
          (m_discr (fun (n : 'I_(S (Z.to_nat N))) => ((Val $ LitV $ LitInt $ fin_to_nat n, σ1) : cfg)))
          (giryM_unif (Z.to_nat N))
*)
(*
Definition rand_rand_E (x : (<<discr Z>> * state)%type) : <<discr Z>>. Admitted.

Definition rand_rand_S (x : (<<discr Z>> * state)%type) : state. Admitted.

Lemma rand_rand_E_meas : measurable_fun setT rand_rand_E. Admitted.
Hint Resolve rand_rand_E_meas : measlang.

Lemma rand_rand_S_meas : measurable_fun setT rand_rand_S. Admitted.
Hint Resolve rand_rand_S_meas : measlang.
*)


Definition ZtoNat' : <<discr Z>> -> <<discr nat>> := Z.to_nat.

Lemma ZtoNat'_measurable : measurable_fun setT ZtoNat'.
Proof. (* Discrete *) Admitted.

Definition giryM_unif' : <<discr Z>> -> giryM <<discr Z>>. Admitted.

Lemma giryM_unif'_meas : measurable_fun setT giryM_unif'. (* Discrete *) Admitted.

Definition rand_rand_aux : <<discr Z>> -> giryM expr :=
  ssrfun.comp
    (gMap' (ssrfun.comp ValU $ ssrfun.comp LitVU $ LitIntU ))
    giryM_unif'.
(*
  m_discr (fun z =>
    giryM_map (giryM_unif' (Z.to_nat z)) $
    ssrfun.comp ValU $
    ssrfun.comp LitVU $
    LitIntU).
*)

Lemma rand_rand_aux_meas : measurable_fun setT rand_rand_aux.
Proof.
  have H : (measurable_fun [set: <<discr Z>>] (ValU \o (LitVU \o LitIntU))).
  { mcrunch_compC ValU_meas_fun.
    mcrunch_compC LitVU_meas_fun.
    by eauto with measlang.
  }
  eapply (@measurable_comp _ _ _ _ _ _ setT).
  { by eapply @measurableT. }
  { by eapply subsetT. }
  { have -> : ((gMap' (ValU \o (LitVU \o LitIntU))) = (gMap H));
      last by eapply @gMap_meas_fun.
    admit.
    (* Don't do this here
    rewrite /giryM_map_external/extern_if.
    admit. *)
  }
  { by eauto with measlang. }
Admitted.
Hint Resolve rand_rand_aux_meas : measlang.

Definition rand_rand : (<<discr Z>> * state)%type -> giryM cfg :=
  ssrfun.comp gProd $
  mProd
    (ssrfun.comp rand_rand_aux fst)
    (ssrfun.comp gRet snd).

Lemma rand_rand_meas : measurable_fun setT rand_rand.
Proof.
  unfold rand_rand.
  eapply (@measurable_comp _ _ _ _ _ _ setT).
  { by eapply @measurableT. }
  { by eapply subsetT. }
  { by eapply @gProd_meas_fun. }
  mcrunch_prod.
  { eapply (@measurable_comp _ _ _ _ _ _ setT).
    { by eapply @measurableT. }
    { by eapply subsetT. }
    { by apply rand_rand_aux_meas. }
    { by eauto with measlang. }
  }
  eapply (@measurable_comp _ _ _ _ _ _ setT).
  { by eapply @measurableT. }
  { by eapply subsetT. }
  { by apply gRet_meas_fun. }
  by eauto with measlang.
Qed.
Hint Resolve rand_rand_meas : measlang.

(**  URand no tape *)


(** Uniform distrubtion over real number literal expressions on the interval *)
Definition rand_urand_aux : giryM expr :=
  gMap'
    (ssrfun.comp ValU $ ssrfun.comp LitVU $ LitRealU )
    unif_base_ax.

Definition rand_urand : state -> giryM cfg :=
  ssrfun.comp gProd $
  mProd (cst $ rand_urand_aux) gRet.

Lemma rand_urand_meas : measurable_fun setT rand_urand.
Proof.
  eapply (@measurable_comp _ _ _ _ _ _ setT).
  { by eapply @measurableT. }
  { by eapply subsetT. }
  { by eapply @gProd_meas_fun. }
  mcrunch_prod.
  { by eauto with measlang. }
  { by apply gRet_meas_fun. }
Qed.
Hint Resolve rand_urand_meas : measlang.

(**  Rand with tape *)
(*
  Definition cover_randE           : set cfg := [set c | ∃ N σ,          c = (Rand (Val (LitV (LitInt N))) (Val (LitV LitUnit)), σ) ].
  Definition cover_randT_notape    : set cfg := [set c | ∃ N l σ,        c = (Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))), σ) /\ σ.(tapes) !! l = None ].
  Definition cover_randT_mismatch  : set cfg := [set c | ∃ N l b σ,      c = (Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))), σ) /\ σ.(tapes) !! l = Some b /\ (bool_decide (b.(btape_bound) = Z.to_nat N) = false)].
  Definition cover_randT_empty     : set cfg := [set c | ∃ N l b σ,      c = (Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))), σ) /\ σ.(tapes) !! l = Some b /\ (bool_decide (b.(btape_bound) = Z.to_nat N) = true) /\ (b.(btape_tape) !! 0) = None].
  Definition cover_randT           : set cfg := [set c | ∃ N l b n σ,    c = (Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))), σ) /\ σ.(tapes) !! l = Some b /\ (bool_decide (b.(btape_bound) = Z.to_nat N) = true) /\ (b.(btape_tape) !! 0) = Some n].
 *)


(* Looking up gives None when the tape is not allocated *)
Definition auxcov_randT_noTape : set (<<discr Z>> * <<discr loc>> * state)%type :=
  (preimage (ssrfun.comp hp_evalC $ mProd (ssrfun.comp snd fst) (ssrfun.comp heap snd)) option_cov_None).
(*
  [set x | tapes x.2 !! x.1.2 = None ].
*)




Definition auxcov_randT_boundMismatch : set (<<discr Z>> * <<discr loc>> * state)%type. Admitted.


(*
  [set x | ∃ b, tapes x.2 !! x.1.2 = Some b /\
                (bool_decide (btape_bound b = Z.to_nat x.1.1) = false) ].
*)
Definition auxcov_randT_nextEmpty : set (<<discr Z>> * <<discr loc>> * state)%type. Admitted.
(*
  [set x | ∃ b, x.2.(tapes) !! x.1.2 = Some b /\
            (bool_decide (btape_bound b = Z.to_nat x.1.1) = false) /\
            (btape_tape b !! 0) = None ].
*)
Definition auxcov_randT_ok : set (<<discr Z>> * <<discr loc>> * state)%type. Admitted.
(*
  [set x | ∃ b, x.2.(tapes) !! x.1.2 = Some b /\
            (bool_decide (b.(btape_bound) = Z.to_nat x.1.1) = false) /\
            ∃ v, (b.(btape_tape) !! 0) = Some v ].
*)

Lemma auxcov_randT_noTape_meas : measurable auxcov_randT_noTape.
Proof. (* Preimage of measurable set under measurable function *) Admitted.
Hint Resolve auxcov_randT_noTape_meas : measlang.

Lemma auxcov_randT_boundMismatch_meas : measurable auxcov_randT_boundMismatch.
Proof. Admitted.
Hint Resolve auxcov_randT_boundMismatch_meas : measlang.

Lemma auxcov_randT_nextEmpty_meas : measurable auxcov_randT_nextEmpty.
Proof. Admitted.
Hint Resolve auxcov_randT_nextEmpty_meas : measlang.

Lemma auxcov_randT_ok_meas : measurable auxcov_randT_ok.
Proof. Admitted.
Hint Resolve auxcov_randT_ok_meas : measlang.


Definition rand_randT_noTape (x : (<<discr Z>> * <<discr loc>> * state)%type) : giryM cfg :=
  gZero.

(*
giryM_map
(m_discr (fun (n : 'I_(S (Z.to_nat N))) => (((Val $ LitV $ LitInt $ fin_to_nat n) : <<discr expr>>), σ1) : cfg))
(giryM_unif (Z.to_nat N))
*)



(* Measurable for each z and l *)
Definition rand_randT_boundMismatch' (z : <<discr Z>>) (l : <<discr loc>>) : (state)%type -> giryM cfg :=
  ssrfun.comp gProd $
  mProd
    (ssrfun.comp (gMap' (ssrfun.comp ValU $ ssrfun.comp LitVU $ LitIntU)) $ (cst (giryM_unif' z)))
    gRet.

(* Measurable because z and l and discrete and countable *)
Definition rand_randT_boundMismatch : (<<discr Z>> * <<discr loc>> * state)%type -> giryM cfg :=
  uncurry (uncurry rand_randT_boundMismatch').


(*
  ssrfun.comp rand_rand $
  mProd (ssrfun.comp fst fst) snd.
*)

(*
giryM_map
  (m_discr (fun (v : 'I_(S (Z.to_nat N))) =>
     (* Fill the tape head with new sample *)
     let τ' := <[ (0 : nat) := Some (v : nat) ]> τ in
     (* Advance the tape *)
     let σ' := state_upd_tapes <[ l := {| btape_tape := (tapeAdvance τ'); btape_bound := M |} ]> σ1 in
     (* Return the new sample and state *)
     ((Val $ LitV $ LitInt $ Z.of_nat v, σ') : cfg)))
 (giryM_unif (Z.to_nat N))
*)

(* Uniform distribution over the states with loc with one sample on the end *)

Definition get_btape : (<<discr loc>> * state)%type -> option btape :=
  ssrfun.comp hp_evalC $
  mProd fst ( ssrfun.comp tapes snd ).

(* Update the tape a location l with a new uniform sample under its tape head *)

(* FIXME: I mean... just look at it *)
Definition tape_sample' (z : <<discr Z>>) (l : <<discr loc>>) : state -> giryM state :=
  ssrfun.comp
    (gMap'
       ((ssrfun.comp state_of_prod $
         mProd
          (mProd
            (ssrfun.comp heap snd)
            (* Update the tape swith label l...*)
            (ssrfun.comp hp_updateC $
             mProd
              (cst l)
              (mProd
                (* new tape is ... get the tape at l, set it to the unif sample *)
                 (ssrfun.comp Some $
                  (* btape *)
                  mProd
                    (* The btape bound *)
                    (ssrfun.comp btape_bound $ of_option $ ssrfun.comp get_btape $ mProd (cst l) snd)
                    (* The btape tape: shifted *)
                    ( mProd
                        (* The position is the old position *)
                        ( ssrfun.comp btape_position $ of_option $ ssrfun.comp get_btape $ mProd (cst l) snd)
                        (* The new tape: Update the old tape *)
                        ( ssrfun.comp sequence_updateC $
                          (mProd
                            (* Update at the tape head position *)
                            ( ssrfun.comp btape_position $ of_option $ ssrfun.comp get_btape $ mProd (cst l) snd)
                            (mProd
                              (* ... to Some of whatever we sampled *)
                              (ssrfun.comp Some fst )
                              ( ssrfun.comp btape_contents $ of_option $ ssrfun.comp get_btape $ mProd (cst l) snd))))))
                (ssrfun.comp tapes snd))))
          (ssrfun.comp utapes snd)) : (<<discr Z>> * state)%type -> state)) $
  ssrfun.comp gProd $
  mProd (cst (giryM_unif' z)) gRet.

Definition tape_sample : (<<discr Z>> * <<discr loc>> * state)%type -> giryM state :=
  uncurry $ uncurry tape_sample'.


(* Tape -> next slot on tape*)
Definition tape_advance : (<<discr loc>> * state)%type -> state :=
  ssrfun.comp state_of_prod $
  mProd
    (mProd
      (ssrfun.comp heap snd)
      (* Update the "tapes" map in the state *)
      (ssrfun.comp hp_updateC $
        (mProd
          fst (* at location l *)
          (mProd
           (* to be the btape at location l but shifted *)
           (ssrfun.comp Some $
            mProd
              (* Bound stays the same *)
              (ssrfun.comp btape_bound $ of_option $ get_btape )
              (* Tape gets advanced *)
              (ssrfun.comp tapeAdvance $ ssrfun.comp snd $  of_option $ get_btape ))
           (ssrfun.comp tapes snd)))))
  (ssrfun.comp utapes snd).

(* Tape -> next item on tape, junk when the next item is none.
   Measurable out of the set of tapes with next item Some, i.e. the range of tape_advance.
 *)


Definition tape_read : (<<discr loc>> * state)%type -> <<discr Z>> :=
  of_option $
  ssrfun.comp sequence_evalC $
  mProd
    (* Get the next position of the tape at loc *)
    (ssrfun.comp fst $ of_option get_btape )
    (* Get the tape at loc *)
    (ssrfun.comp snd $ ssrfun.comp snd $ of_option get_btape).

(*
let σ' := state_upd_tapes <[ l := {| btape_tape := (tapeAdvance τ); btape_bound := M |} ]> σ1 in
(giryM_ret R ((Val $ LitV $ LitInt $ Z.of_nat v, σ') : cfg))
*)
(* Read from and advance the tape *)
Definition rand_randT_ok : (<<discr Z>> * <<discr loc>> * state)%type -> giryM cfg :=
  ssrfun.comp gRet $
  mProd
    ( ssrfun.comp ValU $
      ssrfun.comp LitVU $
      ssrfun.comp LitInt $
      ssrfun.comp tape_read $
      mProd (ssrfun.comp snd fst) snd )
    (ssrfun.comp tape_advance $ mProd (ssrfun.comp snd fst) snd ).


(* When the next tape slot is empty, fill it, and advance. *)
Definition rand_randT_nextEmpty : (<<discr Z>> * <<discr loc>> * state)%type -> giryM cfg :=
  ssrfun.comp
    (gMap' (
      mProd
        (ssrfun.comp ValU $ ssrfun.comp LitVU $ ssrfun.comp LitInt $ snd) (* The expression *)
        (* The state*)
        (ssrfun.comp state_of_prod $
         (mProd (mProd (ssrfun.comp heap $ ssrfun.comp snd fst)
            (* The updated tapes *)
            (ssrfun.comp hp_updateC $
              (* Update the tape at loc... *)
              mProd (ssrfun.comp snd (ssrfun.comp fst fst))
              (mProd
                 (ssrfun.comp Some $
                  (* The new btape *)
                  mProd
                    (* Bound is unchanged *)
                    (ssrfun.comp btape_bound $ of_option $ ssrfun.comp get_btape $ mProd (ssrfun.comp snd (ssrfun.comp fst fst)) (ssrfun.comp snd fst) )
                    (* Tape is the advanced version of.. *)
                    ( mProd
                        (ssrfun.comp Nat.succ $ ssrfun.comp btape_position $ of_option $ ssrfun.comp get_btape $ mProd (ssrfun.comp snd (ssrfun.comp fst fst)) (ssrfun.comp snd fst) )
                        (ssrfun.comp sequence_updateC $
                          mProd
                            (* Update at current tape head *)
                            (ssrfun.comp btape_position $ of_option $ ssrfun.comp get_btape $ mProd (ssrfun.comp snd (ssrfun.comp fst fst)) (ssrfun.comp snd fst) )
                            (mProd
                              (* With value...*)
                              (ssrfun.comp Some snd)
                              (ssrfun.comp btape_contents $ of_option $ ssrfun.comp get_btape $ mProd (ssrfun.comp snd (ssrfun.comp fst fst)) (ssrfun.comp snd fst) )))))
                 (ssrfun.comp tapes $ ssrfun.comp snd fst))
              )
            )
          (ssrfun.comp utapes $ ssrfun.comp snd fst))))) $
  ssrfun.comp gProd $
  (mProd gRet (ssrfun.comp giryM_unif' $ ssrfun.comp fst fst)).

Lemma randT_noTape_meas : measurable_fun auxcov_randT_noTape rand_randT_noTape.
Proof. Admitted.
Hint Resolve randT_noTape_meas : measlang.

Lemma randT_boundMismatch_meas : measurable_fun auxcov_randT_boundMismatch rand_randT_boundMismatch.
Proof. Admitted.
Hint Resolve randT_boundMismatch_meas : measlang.

Lemma randT_nextEmpty_meas : measurable_fun auxcov_randT_nextEmpty rand_randT_nextEmpty.
Proof. Admitted.
Hint Resolve randT_nextEmpty_meas : measlang.

Lemma randT_ok_meas : measurable_fun auxcov_randT_ok rand_randT_ok.
Proof. Admitted.
Hint Resolve randT_ok_meas : measlang.

Definition rand_randT : (<<discr Z>> * <<discr loc>> * state)%type -> giryM cfg :=
  if_in auxcov_randT_noTape rand_randT_noTape $
  if_in auxcov_randT_boundMismatch rand_randT_boundMismatch $
  if_in auxcov_randT_nextEmpty rand_randT_boundMismatch $
  rand_randT_ok.

(*
  let N := x.1.1 in
  let l := x.1.2 in
  let σ1 := x.2 in
  match σ1.(tapes) !! l with
  | Some btape =>
      (* There exists a tape with label l *)
      let τ := btape.(btape_tape) in
      let M := btape.(btape_bound) in
      if (bool_decide (M = Z.to_nat N)) then
        (* Tape bounds match *)
        match (τ !! 0) with
        | Some v => rand_randT_ok x
        | None => rand_randT_nextEmpty x
        end
      else rand_randT_boundMismatch x
        (* Tape bounds do not match *)
        (* Do not advance the tape, but still generate a new sample *)
  | None => rand_randT_noTape x
  end.
*)
(* Covering argument *)
Lemma rand_randT_meas : measurable_fun setT rand_randT.
Proof. Admitted.
Hint Resolve rand_randT_meas : measlang.


(** Urand with tape *)
Definition auxcov_urandT_noTape : set (<<discr loc>> * state)%type. Admitted.
(*
  [set x | tapes x.2 !! x.1 = None ].
*)

Definition auxcov_urandT_nextEmpty : set (<<discr loc>> * state)%type. Admitted.
(*
  [set x | ∃ b, x.2.(tapes) !! x.1 = Some b /\
            (b.(btape_tape) !! 0) = None ].
*)
Definition auxcov_urandT_ok : set (<<discr loc>> * state)%type. Admitted.
(*
  [set x | ∃ b, x.2.(tapes) !! x.1 = Some b /\
            ∃ v, (b.(btape_tape) !! 0) = Some v ].
*)
Lemma auxcov_urandT_noTape_meas : measurable auxcov_urandT_noTape.
Proof. Admitted.
Hint Resolve auxcov_urandT_noTape_meas : measlang.

Lemma auxcov_urandT_nextEmpty_meas : measurable auxcov_urandT_nextEmpty.
Proof. Admitted.
Hint Resolve auxcov_urandT_nextEmpty_meas : measlang.

Lemma auxcov_urandT_ok_meas : measurable auxcov_urandT_ok.
Proof. Admitted.
Hint Resolve auxcov_urandT_ok_meas : measlang.


Definition rand_urandT_noTape (x : (<<discr loc>> * state)%type) : giryM cfg :=
  gZero.

Definition get_utape : (<<discr loc>> * state)%type -> option utape :=
  ssrfun.comp hp_evalC $
  mProd fst ( ssrfun.comp utapes snd ).



Definition rand_urandT_nextEmpty : (<<discr loc>> * state)%type -> giryM cfg :=
  ssrfun.comp (gMap' $
    mProd
      (* The expression *)
      (ssrfun.comp ValU $ ssrfun.comp LitVU $ ssrfun.comp LitReal $ snd)
      (* The state *)
      (ssrfun.comp state_of_prod $
        mProd (mProd (ssrfun.comp (ssrfun.comp heap snd) fst) (ssrfun.comp (ssrfun.comp tapes snd) fst))
        (* Update the utapes *)
        (ssrfun.comp hp_updateC $
          (* At location l*)
         mProd (ssrfun.comp fst fst) (
           mProd
             (ssrfun.comp Some $
                mProd
                  (* Head shifts forward by one*)
                  (ssrfun.comp Nat.succ $ ssrfun.comp fst $ of_option $ ssrfun.comp get_utape fst )
                  (* Tape at old head is updated with sample *)
                  (ssrfun.comp sequence_updateC $
                   mProd (ssrfun.comp fst $ of_option $ ssrfun.comp get_utape fst)
                   (mProd
                      (ssrfun.comp Some snd) (* snd, even though it doesn't typecheck atm *)
                      (ssrfun.comp snd $ of_option $ ssrfun.comp get_utape fst))))
             (ssrfun.comp (ssrfun.comp utapes snd) fst)
          ))
      )
    ) $
  ssrfun.comp gProd $
  mProd gRet (cst (@unif_base_ax R)).


(*
let σ' := state_upd_utapes <[ l := (tapeAdvance τ) ]> σ1 in
(giryM_ret R ((Val $ LitV $ LitReal u, σ') : cfg))
 *)
Definition rand_urandT_ok : (<<discr loc>> * state)%type -> giryM cfg :=
  ssrfun.comp gProd $
  mProd
    (ssrfun.comp gRet $ ssrfun.comp ValU $ ssrfun.comp LitVU $ ssrfun.comp LitReal $
     of_option $ ssrfun.comp sequence_evalC $
     mProd
      (ssrfun.comp fst $ of_option get_utape )
      (ssrfun.comp snd $ of_option get_utape))
  ( ssrfun.comp gRet $
    ssrfun.comp state_of_prod $
    mProd (mProd (ssrfun.comp heap snd) (ssrfun.comp tapes snd) )
    (ssrfun.comp hp_updateC $
     mProd fst
     (mProd
        (ssrfun.comp Some $
          mProd
            (ssrfun.comp Nat.succ $ ssrfun.comp fst $ of_option get_utape )
            ( ssrfun.comp snd $ of_option get_utape ) )
        (ssrfun.comp utapes snd)))).

Lemma urandT_noTape_meas : measurable_fun auxcov_urandT_noTape rand_urandT_noTape.
Proof. Admitted.
Hint Resolve urandT_noTape_meas : measlang.

Lemma urandT_nextEmpty_meas : measurable_fun auxcov_urandT_nextEmpty rand_urandT_nextEmpty.
Proof. Admitted.
Hint Resolve urandT_nextEmpty_meas : measlang.

Lemma urandT_ok_meas : measurable_fun auxcov_urandT_ok rand_urandT_ok.
Proof. Admitted.
Hint Resolve urandT_ok_meas : measlang.

Definition rand_urandT : (<<discr loc>> * state)%type -> giryM cfg :=
  if_in auxcov_urandT_noTape rand_urandT_noTape $
  if_in auxcov_urandT_nextEmpty rand_urandT_nextEmpty $
  rand_urandT_ok .

(*
  let l := x.1 in
  let σ1 := x.2 in
  match utapes σ1 !! l with
  | Some τ =>
      match (τ !! 0) with
      | Some u => rand_urandT_ok x
      | None => rand_urandT_nextEmpty x
      end
  | None => rand_urandT_noTape x
  end.
*)

Lemma rand_urandT_meas : measurable_fun setT rand_urandT.
Proof. Admitted.
Hint Resolve rand_urandT_meas : measlang.
*)
