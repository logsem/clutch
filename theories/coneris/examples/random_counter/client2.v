From clutch.prelude Require Import fin.
From clutch.coneris Require Import coneris par spawn.
From clutch.coneris.examples Require Import random_counter.random_counter.

Set Default Proof Using "Type*".

Section client.
  Context `{rc:random_counter} {L: counterG Σ}.
  Definition con_prog : expr :=
    λ: "_", let: "c" := new_counter #() in
    let: "lbl" := allocate_tape #() in
    (incr_counter_tape "c" "lbl");;
    let: "v" := read_counter "c" in
    incr_counter_tape "c" "lbl";;
    let: "v'" := read_counter "c" - "v" in
    #4*"v" + "v'"
  .
  
  Context `{!spawnG Σ}.
  
  Lemma con_prog_spec P E N:
    E ## ↑N -> 
    {{{ |={E,∅}=>
          ∃ ε (ε2 : fin 16%nat -> R),
              ↯ ε ∗ ⌜(∀ x, 0<=ε2 x)%R⌝∗
              ⌜(SeriesC (λ n, 1 / 16 * ε2 n)%R <= ε)%R ⌝ ∗
              (∀ n, ↯ (ε2 n) ={∅, E}=∗ P ε ε2 n ) }}}
      con_prog #()@ (E ∪ ↑N)
      {{{ (n:fin 16%nat), RET #(fin_to_nat n); ∃ ε ε2, P ε ε2 n }}}.
  Proof.
    iIntros (Hnotin Φ) "Hvs HΦ".
    rewrite /con_prog. wp_pures.
    wp_apply (new_counter_spec (L:=L) _ N with "[//]") as (c) "(%γ & #Hcounter & Hfrag)".
    wp_pures.
    wp_apply (allocate_tape_spec with "[$]") as (lbl) "Htape"; first apply union_subseteq_r.
    wp_pures.
    iAssert (state_update (E∪_) (E∪_) (∃ ε ε2 (n1 n2:fin 4) n,
                   ⌜(fin_to_nat n= 4*fin_to_nat n1 + fin_to_nat n2)%nat⌝ ∗
                   counter_tapes lbl [fin_to_nat n1; fin_to_nat n2] ∗
                   P ε ε2 n))%I with "[Hvs Htape]" as ">(%&%&%&%&%&%Heq&Htape&HP)".
    { iDestruct (fupd_mask_frame_r with "[$]") as "Hvs"; first done.
      rewrite union_empty_l_L.
      iApply state_update_mono_fupd'; last iMod "Hvs" as "(%&%&Herr&%&%Hsum&Hvs)"; first done.
      iMod (counter_tapes_presample _ _ _ _ _ _ _ (λ x, SeriesC (λ (y:fin 4), 1/4*  ε2 (fin_force _ (4*fin_to_nat x+ fin_to_nat y))))%R with "[//][$][$]") as "(%n &Herr & Htape)".
      - done.
      - intros. apply SeriesC_ge_0'. intros. apply Rmult_le_pos; [lra|naive_solver].
      - rewrite SeriesC_finite_foldr/=.
        rewrite !SeriesC_finite_foldr/=.
        rewrite /fin_force/=.
        rewrite SeriesC_finite_foldr/= in Hsum. lra.
      - iMod (counter_tapes_presample _ _ _ _ _ _ _ (λ x, ε2 (fin_force _ (4*fin_to_nat n+ fin_to_nat x )))%R with "[//][$][$]") as "(%n' &Herr & Htape)".
        + done.
        + by intros.
        + done.
        + simpl.
          iDestruct (fupd_mask_frame_r with "[Herr Hvs]") as "Hvs"; [|iApply ("Hvs" with "Herr") |]; first apply namespaces.coPset_disjoint_empty_l.
          rewrite union_empty_l_L.
          iMod "Hvs". iFrame.
          iPureIntro.
          pose proof fin_to_nat_lt n.
          pose proof fin_to_nat_lt n'.
          rewrite /fin_force; case_match; try lia.
          rewrite fin_to_nat_to_fin. lia.
    }
    wp_apply (incr_counter_tape_spec_some _ _ _ _ (λ _, counter_content_frag γ 1 (fin_to_nat n1)) with "[$Hcounter $Htape Hfrag]").
    { apply union_subseteq_r. }
    { iIntros. by iMod (counter_content_update with "[$][$]") as "[$$]". }
    iIntros (?) "[Htape Hfrag]".
    wp_pures.
    wp_apply (read_counter_spec _ _ _ _ (λ n, counter_content_frag _ _ _∗ ⌜(n=fin_to_nat n1)%nat⌝)%I with "[$Hcounter Hfrag]"); first apply union_subseteq_r.
    { iIntros.
      iDestruct (counter_content_agree with "[$][$]") as "->".
      by iFrame.
    }
    iIntros (?) "[Hfrag ->]".
    wp_pures.
    wp_apply (incr_counter_tape_spec_some _ _ _ _ (λ _, counter_content_frag γ 1 (fin_to_nat n1 + fin_to_nat n2)) with "[$Hcounter $Htape Hfrag]"); first apply union_subseteq_r.
    { iIntros. by iMod (counter_content_update with "[$][$]") as "[$$]". }
    iIntros (?) "[Htape Hfrag]".
    wp_pures.
    wp_apply (read_counter_spec _ _ _ _ (λ n, counter_content_frag _ _ _∗ ⌜(n=fin_to_nat n1+fin_to_nat n2)%nat⌝)%I with "[$Hcounter Hfrag]"); first apply union_subseteq_r.
    { iIntros.
      iDestruct (counter_content_agree with "[$][$]") as "->".
      by iFrame.
    }
    iIntros (?) "[Hfrag ->]".
    wp_pures. replace (4*_+_)%Z with (Z.of_nat (fin_to_nat n))%Z; first (iApply "HΦ"; by iFrame).
    rewrite Heq. lia.
  Qed.
End client.
