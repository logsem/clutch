From clutch.elton Require Import elton. 

Definition flip := (λ: "x", rand #1=#1)%E.
Definition dflip :=(λ: "x", drand #1=#1)%E.
Lemma flip_dflip:
  remove_drand_expr dflip = Some flip.
Proof. done. Qed.

Section specs.
  Context `{eltonGS Σ}.

  Definition flip_urn l (s:gset bool):=
    (l ↪ urn_unif (set_map Z.b2z s) )%I.
  
  Definition flip_v l:=
    (LitLbl l =ᵥ 1)%V.

  Lemma flip_v_type l:
    base_lit_type_check (flip_v l) = Some BLTBool.
  Proof. done. Qed.

  Lemma flip_v_not_simple l:
    is_simple_base_lit (flip_v l) = false.
  Proof. done. Qed. 
  
  Lemma wp_dflip E:
    {{{ True }}} dflip #()@E{{{l, RET #(flip_v l); flip_urn l {[true; false]}}}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /dflip.
    wp_pures.
    wp_apply (wp_drand_thunk _ 1 _ _ _ (True)).
    { rewrite rupd_unseal/rupd_def.
      iIntros (?) "$".
      iPureIntro. naive_solver. }
    iIntros (?) "[_ Hl]".
    simpl.
    replace (_∪ (_∪_)) with ({[0%Z; 1%Z]} : gset Z); last set_solver.
    wp_pures.
    by iApply "HΦ".
  Qed.

  Lemma flip_urn_resolve (ε2: _ -> nonnegreal) ε l E:
    (ε2 true + ε2 false <= 2* ε)%R ->
    ↯ε -∗
    flip_urn l {[true; false]} -∗
    pupd E E (∃ b, ↯ (ε2 b) ∗ flip_urn l {[b]}).
  Proof.
    iIntros (?) "??".
    iMod (pupd_resolve_urn _ _ (λ x, if bool_decide (x∈[0%Z;1%Z]) then ε2 (bool_decide (x=1%Z)) else 1%NNR) with "[$][$]") as "H".
    - done.
    - rewrite SeriesC_list; simpl.
      + replace (size _) with 2%nat; last first.
        * by vm_compute.
        * replace (INR 2) with 2%R by done.
          replace (elements _) with ([1%Z; 0%Z]); last first.
          -- by vm_compute.
          -- simpl. rewrite Rcomplements.Rle_div_l; simpl in *; lra. 
      + replace (elements _) with ([1%Z; 0%Z]); last by vm_compute.
        repeat rewrite NoDup_cons. repeat split; try set_solver.
        by apply NoDup_nil.
    - exists (Rmax 1 (Rmax (ε2 true) (ε2 false))).
      intros. case_bool_decide.
      + case_bool_decide.
        * etrans; last apply Rmax_r. apply Rmax_l.
        * etrans; last apply Rmax_r. apply Rmax_r.
      + apply Rmax_l.
    - iDestruct "H" as "(%&Herr&Hl&_)".
      case_bool_decide as H1; last by iDestruct (ec_contradict with "[$]") as "[]".
      iFrame.
      set_unfold in H1.
      destruct!/=.
      + iModIntro.
        rewrite /flip_urn.
        rewrite /set_map.
        rewrite elements_singleton/=.
        by rewrite union_empty_r_L.
      + iModIntro.
        rewrite /flip_urn.
        rewrite /set_map.
        rewrite elements_singleton/=.
        by rewrite union_empty_r_L.
  Qed.

  Lemma flip_v_promote l b:
    flip_urn l {[b]} -∗
    (rupd (λ x, x=LitBool b) (flip_urn l {[b]}) ((flip_v l))).
  Proof.
    iIntros "H".
  Admitted. 
    
  
  Local Lemma test E x:
    base_lit_type_check x = Some BLTBool->
    is_simple_base_lit x = false ->
    {{{ True }}} #x=#x @E{{{RET #(true); True }}}.
  Proof.
    iIntros (H' H'' Φ) "HΦ _".
    (** Need a lemma to allow delay at the end *)
    wp_pure.
    - rewrite /bin_op_eval//=.
      rewrite H'. repeat case_match; simplify_eq; done.
    - admit. 
  Admitted. 
End specs.
