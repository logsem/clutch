(** Exact couplings  *)
From Coq Require Import Reals Psatz.
From Coquelicot Require Import Rcomplements.
From stdpp Require Export countable.

From clutch.prelude Require Import base Coquelicot_ext Reals_ext stdpp_ext classical.
From clutch.prob Require Export countable_sum distribution.

#[local] Open Scope R.

Section coupl.
  Context `{Countable A, Countable B}.
  Context (μ1 : distr A) (μ2 : distr B).

  Definition is_coupl (μ : distr (A * B)) :=
    lmarg μ = μ1 ∧ rmarg μ = μ2.

  Definition ex_coupl := ∃ (μ : distr (A * B)), is_coupl μ.
End coupl.

Section Rcoupl.
  Context `{Countable A, Countable B}.
  Context (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop).

  Definition is_Rcoupl (μ : distr (A * B)) :=
    is_coupl μ1 μ2 μ ∧ ∀ (p : A * B), μ p > 0 → R p.1 p.2.

  Definition Rcoupl := ∃ (μ : distr (A * B)), is_Rcoupl μ.
End Rcoupl.

Section is_coupl.
  Context `{Countable A, Countable B}.

  Lemma is_Rcoupl_is_coupl (μ1 : distr A) (μ2 : distr B) R μ :
    is_Rcoupl μ1 μ2 R μ → is_coupl μ1 μ2 μ.
  Proof. by intros []. Qed.

  Lemma is_coupl_mass_l (μ1 : distr A) (μ2 : distr B) μ :
    is_coupl μ1 μ2 μ → SeriesC μ = SeriesC μ1.
  Proof. intros (<- & _). rewrite dmap_mass //. Qed.

  Lemma is_coupl_mass_r (μ1 : distr A) (μ2 : distr B) μ :
    is_coupl μ1 μ2 μ → SeriesC μ = SeriesC μ2.
  Proof. intros (_ & <-). rewrite dmap_mass //. Qed.

  Lemma is_coupl_mass_eq (μ1 : distr A) (μ2 : distr B) μ :
    is_coupl μ1 μ2 μ → SeriesC μ1 = SeriesC μ2.
  Proof.
    intros. rewrite -(is_coupl_mass_l _ μ2 μ) // -(is_coupl_mass_r μ1 _ μ) //.
  Qed.

  Lemma is_coupl_dret (a : A) (b : B) :
    is_coupl (dret a) (dret b) (dret (a, b)).
  Proof. rewrite /is_coupl /lmarg /rmarg !dmap_dret //. Qed.

End is_coupl.

Section ex_coupl.
  Context `{Countable A, Countable B}.

  Lemma coupl_dret (a : A) (b : B) :
    ex_coupl (dret a) (dret b).
  Proof. eexists. apply is_coupl_dret. Qed.

  Lemma ex_coupl_sym (μ1 : distr A) (μ2 : distr B) :
    ex_coupl μ1 μ2 → ex_coupl μ2 μ1.
  Proof.
    intros (μ & HμL & HμR).
    exists (dmap (λ '(a, b), (b, a)) μ); split; apply distr_ext.
    + intro b.
      rewrite <- HμR.
      rewrite lmarg_pmf rmarg_pmf.
      apply SeriesC_ext; intro a.
      simpl.
      rewrite {1}/pmf /= /dbind_pmf /=.
      rewrite {2}/pmf /= /dret_pmf /=.
      assert (∀ a0, μ a0 * (if bool_decide ((b, a) = (let '(a1, b0) := a0 in (b0, a1))) then 1 else 0)
                    = if bool_decide ((a, b) = a0 ) then μ (a, b) else 0) as Heq1.
      { intros (a' & b').
        case_bool_decide; case_bool_decide; simplify_eq; try lra.
      }
      rewrite (SeriesC_ext _ _ Heq1).
      apply SeriesC_singleton'.
    + intro a.
      rewrite <- HμL.
      rewrite lmarg_pmf rmarg_pmf.
      apply SeriesC_ext; intro b.
      simpl.
      rewrite {1}/pmf /= /dbind_pmf /=.
      rewrite {2}/pmf /= /dret_pmf /=.
      assert (∀ a0, μ a0 * (if bool_decide ((b, a) = (let '(a1, b0) := a0 in (b0, a1))) then 1 else 0)
                    = if bool_decide ((a, b) = a0 ) then μ (a, b) else 0) as Heq1.
      { intros (a' & b').
        case_bool_decide; case_bool_decide; simplify_eq; try lra. }
      rewrite (SeriesC_ext _ _ Heq1).
      apply SeriesC_singleton'.
  Qed.

  Lemma ex_coupl_dbind `{Countable A', Countable B'} (f : A → distr A') (g : B → distr B')
    (μ1 : distr A) (μ2 : distr B) :
    (∀ a b, ex_coupl (f a) (g b)) → ex_coupl μ1 μ2 → ex_coupl (μ1 ≫= f) (μ2 ≫= g).
  Proof.
    intros Hfg (μ & Hμ).
    rewrite /ex_coupl in Hfg.
    assert (∀ (p : A * B), ∃ μ : distr (A' * B'), is_coupl (f p.1) (g p.2) μ) as Hfg'; [done|].
    apply ClassicalEpsilon.choice in Hfg' as (Ch & HCh).
    rewrite /ex_coupl.
    exists (dbind Ch μ); split.
    + apply distr_ext; intro a'.
      rewrite lmarg_pmf.
      rewrite {1 2}/pmf/=/dbind_pmf.
      rewrite <- distr_double_swap_lmarg.
      setoid_rewrite SeriesC_scal_l.
      assert (∀ p , μ p * SeriesC (λ b' : B', Ch p (a', b')) = μ p * f p.1 a') as Heq2.
      { intros (a & b).
        specialize (HCh (a, b)) as (HChL & HChR).
        rewrite -HChL.
        rewrite lmarg_pmf //. }
      rewrite (SeriesC_ext _ _ Heq2).
      rewrite fubini_pos_seriesC_prod_lr.
      2: { simpl; intros; by apply Rmult_le_pos. }
      2: { apply (ex_seriesC_le _ μ); [|done].
           intros; split; [by apply Rmult_le_pos|].
           rewrite -{2}(Rmult_1_r (μ n)).
           by apply Rmult_le_compat. }
      assert (∀ a : A, SeriesC (λ b : B, μ (a, b) * f (a, b).1 a')
               = SeriesC (λ b : B, μ (a, b) ) * f a a') as Heq3.
      { intro a; simpl; apply SeriesC_scal_r. }
      rewrite (SeriesC_ext _ _ Heq3).
      assert (∀ a, SeriesC (λ b : B, μ (a, b)) = μ1 a) as Heq4.
      { intro a.
        destruct Hμ as (Hμ1 & Hμ2).
        rewrite <- Hμ1.
        rewrite lmarg_pmf //. }
      apply SeriesC_ext.
      intro a. rewrite Heq4 //.
    (* The second half is esentially the same as the first, can it be proven somehow by symmetry? *)
    + apply distr_ext; intro b'.
      rewrite rmarg_pmf.
      rewrite {1 2}/pmf/=/dbind_pmf.
      rewrite <- distr_double_swap_rmarg.
      setoid_rewrite SeriesC_scal_l.
      assert (∀ p , μ p * SeriesC (λ a' : A', Ch p (a', b')) = μ p * g p.2 b') as Heq2.
      { intros (a & b).
        specialize (HCh (a, b)) as (HChL & HChR).
        rewrite <- HChR.
        rewrite rmarg_pmf //. }
      rewrite (SeriesC_ext _ _ Heq2).
      rewrite fubini_pos_seriesC_prod_rl //.
      2:{ simpl; intros; by apply Rmult_le_pos. }
      2:{ apply (ex_seriesC_le _ μ); [|done].
          intros; split; [by apply Rmult_le_pos|].
          rewrite -{2}(Rmult_1_r (μ _)).
          by apply Rmult_le_compat. }
      assert (∀ b : B, SeriesC (λ a : A, μ (a, b) * g (a, b).2 b')
               = SeriesC (λ a : A, μ (a, b) ) * g b b') as Heq3.
      { intro b; simpl; apply SeriesC_scal_r. }
      rewrite (SeriesC_ext _ _ Heq3).
      assert (∀ b, SeriesC (λ a : A, μ (a, b)) = μ2 b) as Heq4.
      { intro b.
        destruct Hμ as (Hμ1 & Hμ2).
        rewrite -Hμ2 rmarg_pmf //. }
      apply SeriesC_ext.
      intro b. rewrite Heq4 //.
  Qed.

End ex_coupl.

Section is_Rcoupl.
  Context `{Countable A, Countable B}.

  Lemma is_Rcoupl_dret (a : A) (b : B) (R : A → B → Prop) :
    R a b → is_Rcoupl (dret a) (dret b) R (dret (a, b)).
  Proof.
    split; [apply is_coupl_dret|].
    by intros [? ?] [=-> ->]%dret_pos.
  Qed.

End is_Rcoupl.

Section Rcoupl.
  Context `{Countable A, Countable B}.

  Lemma Rcoupl_dret (a : A) (b : B) (R : A → B → Prop) :
    R a b → Rcoupl (dret a) (dret b) R.
  Proof. eexists. by apply is_Rcoupl_dret. Qed.

  Lemma Rcoupl_mass_eq (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) :
    Rcoupl μ1 μ2 R → SeriesC μ1 = SeriesC μ2.
  Proof. intros (?&?&?). by eapply is_coupl_mass_eq. Qed.

  Lemma Rcoupl_eq (μ1 : distr A) : Rcoupl μ1 μ1 (=).
  Proof.
    exists (ddiag μ1); repeat split_and!.
    - apply distr_ext.
      intro a.
      rewrite lmarg_pmf.
      rewrite {1}/pmf/=/dbind_pmf/=.
      rewrite SeriesC_singleton'; auto.
    - apply distr_ext.
      intro a.
      rewrite rmarg_pmf.
      rewrite {1}/pmf/=/dbind_pmf/=.
      rewrite (SeriesC_ext _ (λ a0 : A, if bool_decide (a0 = a) then μ1 a else 0));
        [rewrite SeriesC_singleton //| ].
      intro a'; case_bool_decide; by simplify_eq.
    - intros (a1 & a2) Hpos; simpl.
      rewrite /pmf/= in Hpos.
      case_bool_decide; simplify_eq=>//. lra.
  Qed.

  Lemma Rcoupl_dbind `{Countable A', Countable B'} (f : A → distr A') (g : B → distr B')
    (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) (S : A' → B' → Prop) :
    (∀ a b, R a b → Rcoupl (f a) (g b) S) →
    Rcoupl μ1 μ2 R →
    Rcoupl (μ1 ≫= f) (μ2 ≫= g) S.
  Proof.
    intros Hfg (μ & HμC & HμS).
    rewrite /Rcoupl /is_Rcoupl in Hfg.
    (* First we rewrite Hfg to be able to use Choice *)
    assert (∀ p, ∃ μ', R p.1 p.2 →
           (is_coupl (f p.1) (g p.2) μ' ∧ (∀ q : A' * B', μ' q > 0 → S q.1 q.2)))
      as Hfg'; auto.
    { intro p.
      specialize (HμS p).
      specialize (Hfg p.1 p.2).
      pose proof (ExcludedMiddle (R p.1 p.2)) as H3; destruct H3 as [HR | HnR].
      + specialize (Hfg HR).
        destruct Hfg as (μ' & Hμ'1 & Hμ'2).
        exists μ'; auto.
      + exists dzero; intro ; done. }
    apply ClassicalEpsilon.choice in Hfg' as (Ch & Hch).
    rewrite /Rcoupl /is_Rcoupl.
    exists (dbind Ch μ); split; try split.
    (* To prove that the marginal coincides is a matter of rearranging the sums and using the
       fact that μ and (Ch p) are couplings *)
    + apply distr_ext; intro a'.
      rewrite lmarg_pmf.
      rewrite {1 2}/pmf/=/dbind_pmf.
      rewrite <- distr_double_swap_lmarg.
      setoid_rewrite SeriesC_scal_l.
      erewrite (SeriesC_ext _ (λ p, μ p * f p.1 a')); last first.
      { intros (a & b).
        destruct (Rtotal_order (μ (a, b)) 0) as [Hlt | [Heqz | Hgt]].
        - pose proof (pmf_pos μ (a, b)); lra.
        - rewrite Heqz; lra.
        - specialize (Hch (a, b) (HμS (a, b) Hgt )) as ((HChL & HChR) & HChS).
          rewrite -HChL lmarg_pmf //=. }
      rewrite fubini_pos_seriesC_prod_lr; auto.
      2: { simpl; intros; by apply Rmult_le_pos. }
      2: { apply (ex_seriesC_le _ μ); [|done].
           intros; split; [by apply Rmult_le_pos| ].
           rewrite <- Rmult_1_r; by apply Rmult_le_compat. }
      erewrite (SeriesC_ext _ (λ a, SeriesC (λ b : B, μ (a, b) ) * f a a'));
        [| intro a; simpl; apply SeriesC_scal_r ].
      erewrite (SeriesC_ext _ (λ a, (μ1 a) * f a a')); [done|].
      intro a.
      destruct HμC as (Hμ1 & Hμ2).
      rewrite -Hμ1 lmarg_pmf //.
    + apply distr_ext; intro b'.
      rewrite rmarg_pmf.
      rewrite {1 2}/pmf/=/dbind_pmf.
      rewrite -distr_double_swap_rmarg.
      setoid_rewrite SeriesC_scal_l.
      erewrite (SeriesC_ext _ (λ p, μ p * g p.2 b')); last first.
      { intros (a & b).
        destruct (Rtotal_order (μ (a, b)) 0) as [Hlt | [Heqz | Hgt]].
        - pose proof (pmf_pos μ (a, b)); lra.
        - rewrite Heqz. lra.
        - specialize (Hch (a, b) (HμS (a, b) Hgt)) as ((HChL & HChR) & HChS).
          rewrite -HChR rmarg_pmf //=. }
      rewrite fubini_pos_seriesC_prod_rl.
      2: { simpl; intros; by apply Rmult_le_pos. }
      2: { apply (ex_seriesC_le _ μ); [|done].
           intros; split; [by apply Rmult_le_pos| ].
           rewrite <- Rmult_1_r; by apply Rmult_le_compat. }
      erewrite (SeriesC_ext _ (λ b, SeriesC (λ a : A, μ (a, b) ) * g b b'));
      [ | intro b; simpl; apply SeriesC_scal_r].
      erewrite (SeriesC_ext _ (λ b, (μ2 b) * g b b')); [done|].
      intro b.
      destruct HμC as (Hμ1 & Hμ2).
      rewrite -Hμ2 rmarg_pmf //.
    + intros (a' & b') H3; simpl.
      pose proof (dbind_pos Ch μ (a', b')) as (H4 & H5).
      specialize (H4 H3) as ((a0, b0) & H7 & H8).
      specialize (Hch (a0, b0) (HμS (a0, b0) H8)) as (HCh1 & HCh2).
      specialize (HCh2 (a', b') H7).
      done.
  Qed.

  Lemma Rcoupl_eq_elim (μ1 μ2 : distr A) :
    Rcoupl μ1 μ2 (=) → μ1 = μ2.
  Proof.
    intros (μ & (HμL & HμR) & HμS).
    rewrite <- HμL, <- HμR.
    apply distr_ext.
    intro a1.
    rewrite lmarg_pmf rmarg_pmf.
    apply SeriesC_ext.
    intro a2.
    specialize (HμS (a1, a2)) as HμS12.
    specialize (HμS (a2, a1)) as HμS21.
    simpl in HμS12.
    simpl in HμS21.
    pose proof (Rtotal_order (μ (a1, a2)) (μ (a2, a1))) as [Hlt | [Heq | Hgt]]; auto.
    + pose proof (pmf_pos μ (a1, a2)).
      assert (μ (a2, a1) > 0) as H'; try lra.
      specialize (HμS21 H'); destruct HμS21; auto.
    + pose proof (pmf_pos μ (a2, a1)).
      assert (μ (a1, a2) > 0) as H'; try lra.
      specialize (HμS12 H'); destruct HμS12; auto.
  Qed.

  Lemma Rcoupl_eq_sym (μ1 μ2: distr A) :
    Rcoupl μ1 μ2 eq → Rcoupl μ2 μ1 eq.
  Proof.
    intros Hc.
    apply Rcoupl_eq_elim in Hc as ->.
    apply Rcoupl_eq.
  Qed.

  Lemma Rcoupl_eq_trans (μ1 μ2 μ3 : distr A) :
    Rcoupl μ1 μ2 eq → Rcoupl μ2 μ3 eq → Rcoupl μ1 μ3 eq.
  Proof. by intros ->%Rcoupl_eq_elim ?. Qed.

  Lemma Rcoupl_mono (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) (S : A → B → Prop):
    Rcoupl μ1 μ2 R → (∀ a b, R a b → S a b) → Rcoupl μ1 μ2 S.
  Proof.
    intros [μ [[HμL HμR] HμSupp]] Hwk.
    exists μ; split; [split| ]; auto.
  Qed.

  Lemma Rcoupl_inhabited_l (μ1 : distr A) (μ2 : distr B) R :
    Rcoupl μ1 μ2 R →
    SeriesC μ1 > 0 →
    ∃ a b, R a b.
  Proof.
    intros [μ [Hcpl HR]] Hz.
    assert (SeriesC μ > 0) as Hsup by by erewrite is_coupl_mass_l.
    apply SeriesC_gtz_ex in Hsup as [[a b] Hμ]; [|done].
    eauto.
  Qed.

  Lemma Rcoupl_inhabited_r (μ1 : distr A) (μ2 : distr B) R :
    Rcoupl μ1 μ2 R →
    SeriesC μ2 > 0 →
    ∃ a b, R a b.
  Proof.
    intros [μ [Hcpl HR]] Hz.
    assert (SeriesC μ > 0) as Hsup by by erewrite is_coupl_mass_r.
    apply SeriesC_gtz_ex in Hsup as [[a b] Hμ]; [|done].
    eauto.
  Qed.

  Lemma Rcoupl_trivial (μ1 : distr A) (μ2 : distr B)    :
    SeriesC μ1 = 1 →
    SeriesC μ2 = 1 →
    Rcoupl μ1 μ2 (λ _ _, True).
  Proof.
    intros Hμ1 Hμ2.
    exists (dprod μ1 μ2). split; [|done].
    split; [apply lmarg_dprod|apply rmarg_dprod]; done.
  Qed.

  Lemma Rcoupl_pos_R (μ1 : distr A) (μ2 : distr B) R :
    Rcoupl μ1 μ2 R → Rcoupl μ1 μ2 (λ a b, R a b ∧ μ1 a > 0 ∧ μ2 b > 0).
  Proof.
    intros [μ [[Hμ1 Hμ2] HR]].
    exists μ. split; [done|].
    intros [a b] Hρ. split; [auto|].
    rewrite -Hμ1 -Hμ2.
    rewrite 2!dmap_pos.
    split; eauto.
  Qed.

  Lemma Rcoupl_dzero_dzero (R : A → B → Prop) :
    Rcoupl dzero dzero R.
  Proof.
    exists dzero. split; [|intros; inv_distr].
    split; [apply lmarg_dzero|apply rmarg_dzero].
  Qed.

  Lemma Rcoupl_dzero_r_inv μ1 (R : A → B → Prop) :
    Rcoupl μ1 dzero R → μ1 = dzero.
  Proof.
    intros Hz%Rcoupl_mass_eq.
    apply SeriesC_zero_dzero.
    rewrite Hz SeriesC_0 //.
  Qed.

  Lemma Rcoupl_dzero_l_inv μ2 (R : A → B → Prop) :
    Rcoupl dzero μ2 R → μ2 = dzero.
  Proof.
    intros Hz%Rcoupl_mass_eq.
    apply SeriesC_zero_dzero.
    rewrite -Hz SeriesC_0 //.
  Qed.
End Rcoupl.

Lemma Rcoupl_dmap `{Countable A, Countable B, Countable A', Countable B'}
  (f : A → A') (g : B → B') (μ1 : distr A) (μ2 : distr B) (R : A' → B' → Prop) :
  Rcoupl μ1 μ2 (λ a a', R (f a) (g a')) → Rcoupl (dmap f μ1) (dmap g μ2) R.
Proof.
  intros Hcoupl. rewrite /dmap.
  eapply Rcoupl_dbind; [|done].
  intros. by eapply Rcoupl_dret.
Qed.

Lemma Rcoupl_dunif (N : nat) f `{Bij (fin N) (fin N) f} :
  Rcoupl (dunif N) (dunif N) (λ n m, m = f n).
Proof.
  exists (dmap (λ x, (x, f x)) (dunif N)).
  split; [split|].
  - eapply distr_ext=> y1.
    rewrite lmarg_pmf.
    erewrite (SeriesC_ext _ (λ y2, if bool_decide (y2 = f y1) then /N else 0)); last first.
    { intro. case_bool_decide; simplify_eq.
      - eapply dmap_unif_nonzero; [|done]. intros ???; by simplify_eq.
      - apply dmap_unif_zero. intros ? [=]; simplify_eq. }
    rewrite dunif_pmf.
    apply SeriesC_singleton.
  - eapply distr_ext=> y2.
    rewrite rmarg_pmf.
    erewrite (SeriesC_ext _ (λ y1, if bool_decide (f y1 = y2) then /N else 0)); last first.
    { intro. case_bool_decide; simplify_eq.
      - eapply dmap_unif_nonzero; [|done]. intros ???; by simplify_eq.
      - apply dmap_unif_zero. intros ? [=]; simplify_eq. }
    rewrite dunif_pmf.
    apply (SeriesC_singleton_inj y2 f); [apply _|].
    apply (surj f).
  - intros (m1 & m2) (n & [=] & Hn)%dmap_pos =>/=. by simplify_eq.
Qed.

Section Rcoupl_strength.
  Context `{Countable A, Countable B, Countable D, Countable E}.
  Context (μ1 : distr A) (μ2 : distr B).

  Lemma Rcoupl_strength_l (R : A → B → Prop) (d : D)  :
    Rcoupl μ1 μ2 R →
    Rcoupl (strength_l d μ1) μ2 (λ '(d', a) b, d' = d ∧ R a b).
  Proof.
    rewrite /strength_l /dmap.
    intros Hcpl.
    rewrite -(dret_id_right μ2).
    eapply Rcoupl_dbind; [|done].
    intros. by apply Rcoupl_dret.
  Qed.

  Lemma Rcoupl_strength (R : A → B → Prop) (d : D) (e : E) :
    Rcoupl μ1 μ2 R →
    Rcoupl (strength_l d μ1) (strength_l e μ2)
      (λ '(d', a) '(e', b), d' = d ∧ e' = e ∧ R a b).
  Proof.
    rewrite /strength_l /dmap.
    eapply Rcoupl_dbind.
    intros. by apply Rcoupl_dret.
  Qed.

End Rcoupl_strength.

Section refcoupl.
  Context `{Countable A, Countable B}.
  Context (μ1 : distr A) (μ2 : distr B).

  Definition is_refcoupl (μ : distr (A * B)) : Prop :=
    lmarg μ = μ1 ∧ ∀ (b : B), rmarg μ b <= μ2 b.

  Definition ex_refcoupl :=
    ∃ (μ : distr (A * B)), is_refcoupl μ.
End refcoupl.

Section refRcoupl.
  Context `{Countable A, Countable B}.
  Context (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop).

  Definition is_refRcoupl (μ : distr (A * B)) : Prop :=
    is_refcoupl μ1 μ2 μ ∧ ∀ (p : A * B), μ p > 0 → R p.1 p.2.

  Definition refRcoupl :=
    ∃ (μ : distr (A * B)), is_refRcoupl μ.

End refRcoupl.

Section refcoupl.
  Context `{Countable A, Countable B}.
  Context (μ1 : distr A) (μ2 : distr B).

  Lemma is_refcoupl_dret (a : A) (b : B) :
    is_refcoupl (dret a) (dret b) (dret (a, b)).
  Proof. split; [rewrite /lmarg dmap_dret // | rewrite /rmarg dmap_dret //]. Qed.
End refcoupl.

Section is_refRcoupl.
  Context `{Countable A, Countable B}.
  Context (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) (μ : distr (A * B)).

  Lemma is_refRcoupl_mass_l : is_refRcoupl μ1 μ2 R μ → SeriesC μ = SeriesC μ1.
  Proof. intros ([<- Hr] & Hμ). rewrite /lmarg dmap_mass //. Qed.

  Lemma is_refRcoupl_mass_r : is_refRcoupl μ1 μ2 R μ → SeriesC μ <= SeriesC μ2.
  Proof.
    intros ([Hl Hr] & Hμ).
    rewrite -(dmap_mass μ snd).
    by apply SeriesC_le.
  Qed.

  Lemma is_refRcoupl_mass_eq : is_refRcoupl μ1 μ2 R μ → SeriesC μ1 <= SeriesC μ2.
  Proof.
    intro Hμ.
    rewrite -is_refRcoupl_mass_l; [|done].
    by apply is_refRcoupl_mass_r.
  Qed.

End is_refRcoupl.

Section refRcoupl.
  Context `{Countable A, Countable B}.

  Lemma refRcoupl_mass_eq (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) :
    refRcoupl μ1 μ2 R → SeriesC μ1 <= SeriesC μ2.
  Proof. intros (?&?&?). by eapply is_refRcoupl_mass_eq. Qed.

  Lemma refRcoupl_eq_elim (μ1 μ2 : distr A) :
    refRcoupl μ1 μ2 (=) → ∀ a, μ1 a <= μ2 a.
  Proof.
    intros (μ & (HμL & HμR) & HμS) a.
    eapply (Rle_Transitive _ (rmarg μ a) _); auto.
    rewrite <- HμL.
    rewrite lmarg_pmf rmarg_pmf.
    eapply SeriesC_le.
    { intro .  specialize (HμS (a,n)). simpl in HμS.
      destruct (Rtotal_order (μ (a,n)) 0) as [? | [? | H3]].
      - pose proof (pmf_pos μ (a, n)); lra.
      - pose proof (pmf_pos μ (n, a)); lra.
      - pose proof (HμS H3); simplify_eq; lra. }
    apply ex_distr_rmarg.
  Qed.

  Lemma refRcoupl_from_leq (μ1 μ2 : distr A) :
    (∀ a, μ1 a <= μ2 a) → refRcoupl μ1 μ2 (=).
  Proof.
    intro Hleq.
    exists (ddiag μ1). split;[ split  | ].
    - apply distr_ext; intro a.
      rewrite lmarg_pmf {2}/pmf/=.
      rewrite SeriesC_singleton'; auto.
    - intro a.
      rewrite ddiag_rmarg.
      auto.
    - intros p Hp.
      rewrite ddiag_pmf in Hp.
      case_bool_decide; auto; lra.
  Qed.

  Lemma refRcoupl_eq_refl (μ1 : distr A) :
    refRcoupl μ1 μ1 (=).
  Proof. by apply refRcoupl_from_leq. Qed.

  Lemma refRcoupl_eq_trans (μ1 μ2 μ3 : distr A):
    refRcoupl μ1 μ2 (=) → refRcoupl μ2 μ3 (=) → refRcoupl μ1 μ3 (=).
  Proof.
    intros H12 H23.
    pose proof (refRcoupl_eq_elim _ _ H12) as H12'.
    pose proof (refRcoupl_eq_elim _ _ H23) as H23'.
    apply refRcoupl_from_leq.
    intros; eapply Rle_trans; eauto.
  Qed.

  Lemma refRcoupl_eq_refRcoupl_unfoldl (μ1 μ2 μ3 : distr A) R :
    Rcoupl μ1 μ2 (=) → refRcoupl μ2 μ3 R → refRcoupl μ1 μ3 R.
  Proof. by intros ->%Rcoupl_eq_elim ?. Qed.

  Lemma refRcoupl_eq_refRcoupl_unfoldr (μ1 μ2 μ3 : distr A) R :
    refRcoupl μ1 μ2 R → Rcoupl μ2 μ3 (=) → refRcoupl μ1 μ3 R.
  Proof. by intros ? <-%Rcoupl_eq_elim. Qed.

  Lemma Rcoupl_refRcoupl (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) :
    Rcoupl μ1 μ2 R → refRcoupl μ1 μ2 R.
  Proof.
    rewrite /refRcoupl /Rcoupl.
    intros (μ & ((HμL & HμR) & HμSupp)).
    exists μ.
    split; [|done].
    split; [done|].
    intro. rewrite HμR; lra.
  Qed.

  Lemma refRcoupl_dret a b (R : A → B → Prop) :
    R a b → refRcoupl (dret a) (dret b) R.
  Proof.
    intros HR.
    eexists. split; [eapply is_refcoupl_dret|].
    intros [] [=<- <-]%dret_pos. done.
  Qed.

  Lemma refRcoupl_dbind  `{Countable A', Countable B'} (f : A → distr A') (g : B → distr B')
    (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) (S : A' → B' → Prop) :
    (∀ a b, R a b → refRcoupl (f a) (g b) S) →
    refRcoupl μ1 μ2 R →
    refRcoupl (μ1 ≫= f) (μ2 ≫= g) S.
  Proof.
    intros Hfg (μ & HμC & HμS).
    rewrite /Rcoupl /is_Rcoupl in Hfg.
    (* First we rewrite Hfg to be able to use Choice *)
    assert (∀ p, ∃ μ' , R p.1 p.2 → (is_refcoupl (f p.1) (g p.2) μ' ∧
                (∀ q : A' * B', μ' q > 0 → S q.1 q.2))) as Hfg'.
    {
      intro p.
      specialize (HμS p).
      specialize (Hfg p.1 p.2).
      pose proof (ExcludedMiddle (R p.1 p.2)) as H3; destruct H3 as [HR | HnR].
      + specialize (Hfg HR).
        destruct Hfg as (μ' & Hμ'1 & Hμ'2).
        exists μ'; auto.
      + exists dzero; intro ; done. }
    apply ClassicalEpsilon.choice  in Hfg' as (Ch & HCh).
    rewrite /Rcoupl /is_Rcoupl.
    exists (dbind Ch μ); split; try split.
    (* To prove that the first marginal coincides is a matter of rearranging the sums and using the
    fact that μ and (Ch p) are couplings *)
    + apply distr_ext; intro a'.
      rewrite lmarg_pmf.
      rewrite /pmf /= /dbind_pmf.
      rewrite <- distr_double_swap_lmarg.
      setoid_rewrite SeriesC_scal_l.
      erewrite (SeriesC_ext _ (λ p, μ p * f p.1 a')); last first.
      { intros (a & b).
        destruct (Rtotal_order (μ (a, b)) 0) as [Hlt | [Heqz | Hgt]].
        + pose proof (pmf_pos μ (a, b)); lra.
        + rewrite Heqz; lra.
        + specialize (HCh (a, b) (HμS (a, b) Hgt )) as ((HChL & HChR) & HChS).
          rewrite -HChL lmarg_pmf //=. }
      rewrite fubini_pos_seriesC_prod_lr; auto.
      2: { simpl; intros; by apply Rmult_le_pos. }
      2: { apply (ex_seriesC_le _ μ); [|done].
           intros; split; [by apply Rmult_le_pos|].
           rewrite <- Rmult_1_r; by apply Rmult_le_compat. }
      erewrite (SeriesC_ext _ (λ a, SeriesC (λ b : B, μ (a, b) ) * f a a'));
      [ | intro a; simpl; apply SeriesC_scal_r ].
      erewrite (SeriesC_ext _ (λ a, (μ1 a) * f a a')); auto.
      intro a.
      destruct HμC as (Hμ1 & Hμ2).
      rewrite -Hμ1 lmarg_pmf //.
    + intro b'.
      rewrite rmarg_pmf.
      rewrite /pmf/=/dbind_pmf.
      rewrite <- distr_double_swap_rmarg.
      erewrite (SeriesC_ext _ (λ b, μ b * SeriesC (λ a : A', Ch b (a, b'))) );
      [ | intro p; apply SeriesC_scal_l].
      apply (Rle_trans _ (SeriesC (λ p, μ p * g p.2 b')) _).
      { apply SeriesC_le; [ | ]; last first.
        - apply (ex_seriesC_le _ μ); [|done].
          intros; split.
          + by apply Rmult_le_pos.
          + rewrite -{2}(Rmult_1_r (μ _)). by apply Rmult_le_compat_l.
        - intros (a & b); split.
          + apply Rmult_le_pos; [done|].
            assert (SeriesC (λ a0 : A', Ch (a, b) (a0, b')) = rmarg (Ch (a, b)) b')
              as ->; [|done].
            rewrite rmarg_pmf //.
          + destruct (Rtotal_order (μ (a, b)) 0) as [Hlt | [Heqz | Hgt]].
            * pose proof (pmf_pos μ (a, b)); lra.
            * rewrite Heqz; lra.
            * specialize (HCh (a, b) (HμS (a, b) Hgt )) as ((HChL & HChR) & HChS).
              specialize (HChR b').
              rewrite (rmarg_pmf (Ch (a, b))) in HChR.
              by apply Rmult_le_compat_l. }
      rewrite fubini_pos_seriesC_prod_rl.
      2: { simpl; intros; by apply Rmult_le_pos. }
      2: { apply (ex_seriesC_le _ μ); [|done].
          intros. split; [by apply Rmult_le_pos|].
          rewrite <- Rmult_1_r; by apply Rmult_le_compat. }
      apply SeriesC_le; last first.
      { apply (ex_seriesC_le _ μ2); [|done].
        intros; split.
        - by apply Rmult_le_pos.
        - rewrite <- Rmult_1_r. by apply Rmult_le_compat_l. }
      intro b; split; simpl.
      * rewrite SeriesC_scal_r.
        apply Rmult_le_pos; [|done].
        rewrite -rmarg_pmf //.
      * destruct HμC as [HμCL HμCR].
        rewrite SeriesC_scal_r.
        apply Rmult_le_compat_r; [done|].
        specialize (HμCR b).
        by rewrite rmarg_pmf in HμCR.
    + intros (a' & b') H3; simpl.
      pose proof (dbind_pos Ch μ (a', b')) as (H4 & H5).
      specialize (H4 H3) as ((a0, b0) & H7 & H8).
      specialize (HCh (a0, b0) (HμS (a0, b0) H8)) as (HCh1 & HCh2).
      specialize (HCh2 (a', b') H7).
      done.
  Qed.

  Lemma refRcoupl_dzero (μ : distr B) (R: A → B → Prop):
    refRcoupl dzero μ R.
  Proof.
    exists dzero; split; try split.
    + rewrite /lmarg dmap_dzero; done.
    + intro a.
      rewrite rmarg_pmf {1}/pmf/=.
      rewrite SeriesC_0; auto.
    + rewrite /pmf/=; intros; lra.
  Qed.

  Lemma refRcoupl_mono (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) (S : A → B → Prop):
    (∀ a b, R a b → S a b) → refRcoupl μ1 μ2 R → refRcoupl μ1 μ2 S.
  Proof.
    intros Hwk [μ [[HμL HμR] HμSupp]].
    exists μ; split; [split| ]; auto.
  Qed.

  Lemma refRcoupl_trivial (μ1 :distr A) (μ2 :distr B):
    SeriesC μ1 <= SeriesC μ2 →
    refRcoupl μ1 μ2 (λ _ _, True).
  Proof.
    intros Hμ.
    pose proof (pmf_SeriesC_ge_0 μ1) as H3.
    destruct (Rlt_or_le 0 (SeriesC μ1)); last first.
    - destruct H3 ; try lra.
      rewrite (SeriesC_zero_dzero μ1); [ | apply Rle_antisym; auto].
      apply refRcoupl_dzero.
    - assert (0 < SeriesC μ2); [apply (Rlt_le_trans _ (SeriesC μ1))|];
        [done|done|].
      assert ( 0 <= / SeriesC μ2 ∧ / SeriesC μ2 * SeriesC (dprod μ1 μ2) <= 1) as Hle1.
      { split; auto.
        - left; apply Rinv_0_lt_compat; auto.
        - rewrite dprod_mass.
          rewrite Rmult_comm Rmult_assoc.
          rewrite Rinv_r; [|lra].
          rewrite Rmult_1_r.
          done. }
      eexists (distr_scal (/(SeriesC μ2)) (dprod μ1 μ2) Hle1).
      split; [|done]. split.
      + apply distr_ext. intro a.
        rewrite lmarg_pmf.
        rewrite SeriesC_scal_l -lmarg_pmf.
        rewrite lmarg_dprod_pmf.
        rewrite -Rmult_comm Rmult_assoc Rinv_r; lra.
      + intro b.
        rewrite rmarg_pmf SeriesC_scal_l.
        rewrite -rmarg_pmf rmarg_dprod_pmf.
        rewrite -Rmult_comm Rmult_assoc.
        rewrite -{2}(Rmult_1_r (μ2 b)).
        apply Rmult_le_compat_l; [done|].
        by apply (Rdiv_le_1 (SeriesC μ1)).
  Qed.

End refRcoupl.

Notation "μ1 '≾' μ2 ':' R" :=
  (refRcoupl μ1 μ2 R)
  (at level 100, μ2 at next level,
   R at level 200,
    format "'[hv' μ1  '/' '≾'  '/  ' μ2  :  R ']'").

Notation "μ1 '≿' μ2 ':' R" :=
  (refRcoupl μ2 μ1 R)
  (at level 100, μ2 at next level,
   R at level 200, only parsing).
