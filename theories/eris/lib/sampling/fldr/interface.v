From Coq Require Import Arith.PeanoNat Lists.List Reals Psatz Lia ZArith.
From clutch.eris Require Import eris.
From clutch.common Require Import inject.
From clutch.eris.lib Require Import list.
From clutch.eris.lib.sampling Require Import utils distr_impl distribution_adequacy.
From clutch.eris.lib.sampling.fldr Require Import implementation model walk pure distribution list_total preprocessing walk_spec round tape loop presample presample_output.

Import ListNotations.
#[local] Open Scope R.

Definition fldr_val_distr (ws : list nat) (Hws : admissible ws) : distr val :=
  dmap (fun i : nat => #i) (fldr_distr ws Hws).

Lemma fldr_val_inj : Inj eq eq (fun i : nat => #i).
Proof.
  move=> i j Hij.
  change (LitV (LitInt (Z.of_nat i)) = LitV (LitInt (Z.of_nat j))) in Hij.
  inversion Hij.
  now apply Nat2Z.inj.
Qed.

Global Instance fldr_val_inj_instance : Inj eq eq (fun i : nat => #i) := fldr_val_inj.

Lemma fldr_val_distr_nat (ws : list nat) (Hws : admissible ws) (i : nat) :
    fldr_val_distr ws Hws #i = target_mass ws i.
Proof.
  unfold fldr_val_distr.
  eapply (dmap_elem_eq (fldr_distr ws Hws) i #i (fun i : nat => #i)).
  reflexivity.
Qed.

Lemma fldr_val_distr_mass (ws : list nat) (Hws : admissible ws) :
    SeriesC (fldr_val_distr ws Hws) = 1%R.
Proof.
  unfold fldr_val_distr.
  rewrite dmap_mass.
  apply fldr_distr_mass.
Qed.

Definition fldr_sample (ws : list nat) : val :=
  (λ: "α", fldr_tape "α" (inject ws))%V.

Definition fldr_unit_loc : val := #().

Definition fldr_own_tape `{!erisGS Σ} (ws : list nat) (Δ : loc) (l : list val) : iProp Σ :=
  (∃ outs, own_fldr_tape ws Δ outs ∗ ⌜l = map (fun i : nat => #i) outs⌝)%I.

Definition fldr_is_abs_loc (Δ : loc) (α : val) : Prop := α = #lbl:Δ.

Section FldrFields.
  Context `{!erisGS Σ}.

  Lemma twp_fldr_sample_adv_comp (ws : list nat) (Hws : admissible ws)
      (Hnd : nondegenerate ws) (D : val -> R) (ε L : R) :
      (0 <= ε)%R -> (forall v : val, (0 <= D v <= L)%R) ->
      ε = SeriesC (fun v : val => fldr_val_distr ws Hws v * D v)%R ->
      [[{ ↯ ε }]] fldr_sample ws fldr_unit_loc
      [[{ (v : val), RET v; ↯ (D v) }]].
  Proof.
    iIntros (Hε HD Hsum Φ) "Herr HΦ".
    rewrite /fldr_sample /fldr_unit_loc /fldr_tape.
    wp_pures.
    wp_bind (fldr_table (inject_list ws)).
    wp_apply (twp_fldr_table _ ws (inject_list ws)) as (vrows) "Hrows";
      [exact Hws|iPureIntro; apply (is_list_inject ws (inject_list ws))|].
    all: try (change (inject_list ws = inject_list ws); reflexivity).
    wp_let.
    wp_bind (list_length (inject_list ws)).
    wp_apply (twp_list_length _ ws (inject_list ws)) as (n) "Hn";
      [iPureIntro; apply (is_list_inject ws (inject_list ws))|].
    all: try (change (inject_list ws = inject_list ws); reflexivity).
    iDestruct "Hn" as %Hn.
    rewrite Hn.
    set (Dn := fun i : nat => D #i).
    assert (HDn : forall i, (0 <= Dn i <= L)%R).
    { intros i. apply HD. }
    assert (Hsum' : ε = SeriesC (fun i : nat => target_mass ws i * Dn i)%R).
    { rewrite (dmap_expected_value (fldr_distr ws Hws)
          (fun i : nat => #i) D L) in Hsum.
      - exact Hsum.
      - intros i. apply HD. }
    symmetry in Hsum'.
    wp_apply (twp_fldr_loop_adv_comp _ ws vrows Dn L ε Hws Hnd HDn Hsum'
      with "[$Hrows Herr]") as (i) "[Herr _]".
    all: try done.
    iApply ("HΦ" $! #i).
    iExact "Herr".
  Qed.
  Lemma twp_fldr_sample_presample_adv_comp (ws : list nat) (Hws : admissible ws)
      (Hnd : nondegenerate ws) (e : expr) (ε : R) (Δ : loc) (l : list val)
      (D : val -> R) (L : R) (Φ : val -> iProp Σ) :
    to_val e = None -> (0 <= ε)%R -> (forall v : val, (0 <= D v <= L)%R) ->
    SeriesC (fun v : val => fldr_val_distr ws Hws v * D v)%R = ε ->
    ↯ ε ∗ fldr_own_tape ws Δ l ∗
    (∀ (v : val), fldr_own_tape ws Δ (l ++ [v]) ∗ ↯ (D v) -∗ WP e [{ v, Φ v }])
    ⊢ WP e [{ v, Φ v }].
  Proof.
    intros He Hε HD Hsum.
    iIntros "(Herr & (%outs & Htape & %Hl) & Hnext)".
    set (Dn := fun i : nat => D #i).
    assert (HDn : forall i, (0 <= Dn i <= L)%R).
    { intros i. apply HD. }
    assert (Hsum' : SeriesC (fun i : nat => target_mass ws i * Dn i)%R = ε).
    { rewrite (dmap_expected_value (fldr_distr ws Hws)
          (fun i : nat => #i) D L) in Hsum.
      - exact Hsum.
      - intros i. apply HD. }
    iApply (twp_fldr_presample_output ⊤ ws Δ outs e Φ Dn L ε
      Hws Hnd He HDn Hsum').
    iSplitL "Htape"; [iExact "Htape"|].
    iSplitL "Herr"; [iExact "Herr"|].
    iIntros (i) "(%Hi & Htape_i & Hcredit)".
    iApply ("Hnext" $! #i).
    iSplitL "Htape_i".
    - iExists (outs ++ [i]).
      iSplitL "Htape_i".
      + iExact "Htape_i".
      + iPureIntro.
        rewrite Hl. rewrite map_app. reflexivity.
    - iExact "Hcredit".
  Qed.
  Lemma twp_fldr_sample_alloc (ws : list nat) :
      [[{ True }]] fldr_alloc #()
      [[{ (Δ : loc) (α : val), RET α;
          ⌜fldr_is_abs_loc Δ α⌝ ∗ fldr_own_tape ws Δ [] }]].
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_apply (twp_fldr_alloc _ ws) as (Δ) "Htape".
    all: try done.
    iApply ("HΦ" $! Δ (#lbl:Δ)).
    iSplit.
    - iPureIntro. reflexivity.
    - iExists []. iFrame. iPureIntro. reflexivity.
  Qed.


  Lemma twp_fldr_sample_load (ws : list nat) (Hws : admissible ws)
      (α : val) (Δ : loc) (l : list val) (v : val) :
      [[{ fldr_own_tape ws Δ (v :: l) ∗ ⌜fldr_is_abs_loc Δ α⌝ }]]
        fldr_sample ws α
      [[{ RET v; fldr_own_tape ws Δ l }]].
  Proof.
    iIntros (Φ) "[(%outs & Htape & %Hl) %Hα] HΦ".
    destruct outs as [|i outs']; first by discriminate.
    simpl in Hl.
    injection Hl as Hv Hl.
    subst v.
    unfold fldr_is_abs_loc in Hα.
    subst α.
    rewrite /fldr_sample.
    wp_pures.
    wp_apply (twp_fldr_tape_load _ ws (inject_list ws) Δ i outs' Hws
      with "[Htape]") as "Htape".
    { iSplit.
      - iPureIntro. apply (proj2 (is_list_inject ws (inject_list ws))). reflexivity.
      - iExact "Htape". }
    all: try done.
    iApply "HΦ".
    iExists outs'.
    iSplit.
    - iExact "Htape".
    - iPureIntro. exact Hl.
  Qed.
End FldrFields.

Lemma fldr_prob_singleton (d : distr val) (v : val) :
    prob d (fun w => bool_decide (v = w)) = d v.
Proof.
  unfold prob.
  erewrite (SeriesC_ext
    (fun w : val => if bool_decide (v = w) then d w else 0%R)
    (fun w : val => if bool_decide (v = w) then d v else 0%R)); last first.
  { intros w. case_bool_decide; subst; [reflexivity|reflexivity]. }
  apply SeriesC_singleton'.
Qed.
