From clutch.prob_eff_lang.probblaze Require Import notation proofmode logic sem_def sem_types sem_row sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require Import valgroup ske fin_val_type valgroup_finval.
From mathcomp Require Import finset fintype.
Import fingroup.FinGroup.Exports.
Set Default Proof Using "Type*".

(** The one-time pad as an instance of [SYM].

    Key, message and cipher space are all the group [vgG]; encryption is
    [k^-1 * m] and decryption [k * m].  Under the [fin_val] interface the
    scheme's arguments are group *values*, not their integer codes, so --
    unlike the old integer-indexed [SYM_params] version -- neither [otp_enc]
    nor its correctness proofs ever decode, and there are no [NONE] cases. *)

Section otp.
  Context `{probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.

  Import valgroup_notation.
  Import valgroup_tactics.
  Import fingroup.

  (** The key, message and cipher space is the group itself: [valgroup_finval.v]
      packages a [clutch_group] as the [fin_val] triple [vg_fvt] / [vg_fvts] /
      [vg_fv], so nothing below has to decode. *)

  (** ** The scheme *)

  Definition otp_enc : val := λ: "k" "m", "k"^-1 · "m".
  Definition otp_dec : val := λ: "k" "m", SOME ("k" · "m").
  
  Lemma otp_enc_closed : is_closed_val otp_enc.
  Proof. is_closed. Qed.
  Lemma otp_dec_closed : is_closed_val otp_dec.
  Proof. is_closed. Qed.

  #[local] Instance vg_fvt_inhabited : Inhabited (fvt_sort vg_fvts) := populate (1%g : vgG).

  Global Instance otp_struct :
    @SYM_struct vg_fvt vg_fvts vg_fvt vg_fvts vg_fvt vg_fvts :=
    { enc := otp_enc 
    ; dec := otp_dec 
    ; enc_closed := otp_enc_closed
    ; dec_closed := otp_dec_closed }.

  Definition otp_enc_sem (k m : vgG) : vgG := (k^-1 * m)%g.

  Global Instance otp_enc_sem_bij m : Bij (λ k, otp_enc_sem k m).
  Proof.
    rewrite /otp_enc_sem. split.
    - intros x y Heq. apply (mulIg m) in Heq. exact (invg_inj Heq).
    - intros c. exists (m * c^-1)%g.
      by rewrite invMg invgK -mulgA mulVg mulg1.
  Qed.

  Definition otp_dec_sem (k m : vgG) : vgG := (k * m)%g.

  Lemma otp_dec_enc_correct k m : otp_dec_sem k (otp_enc_sem k m) = m.
  Proof. by rewrite /otp_dec_sem /otp_enc_sem mulgA mulgV mul1g. Qed.

  Lemma otp_enc_correct_l E K (k m : vgG) X R e :
    ⊢ (BREL fill K (vgval (otp_enc_sem k m)) ≤ e @ E <|X|> {{R}}) -∗
    (BREL fill K (otp_enc (vgval k) (vgval m)) ≤ e @ E <|X|> {{R}}).
  Proof with (repeat rewrite fill_app; simpl).
    iIntros "Hsem". rewrite /otp_enc /otp_enc_sem.
    brel_pures'...
    brel_mult_l...
    iApply "Hsem".
  Qed.

  Lemma otp_enc_correct_r E K (k m : vgG) X R e :
    ⊢ (BREL e ≤ fill K (vgval (otp_enc_sem k m)) @ E <|X|> {{R}}) -∗
    (BREL e ≤ fill K (otp_enc (vgval k) (vgval m)) @ E <|X|> {{R}}).
  Proof with (repeat rewrite fill_app; simpl).
    iIntros "Hsem". rewrite /otp_enc /otp_enc_sem.
    brel_pures'...
    brel_mult_r...
    iApply "Hsem".
  Qed.

  Lemma otp_dec_correct_l E K (k c : vgG) X R e :
    ⊢ (BREL fill K (SOMEV (vgval (otp_dec_sem k c))) ≤ e @ E <|X|> {{R}}) -∗
    (BREL fill K (otp_dec (vgval k) (vgval c)) ≤ e @ E <|X|> {{R}}).
  Proof with (repeat rewrite fill_app; simpl).
    iIntros "Hsem". rewrite /otp_dec /otp_dec_sem.
    brel_pures'... brel_pures_l.
    iApply "Hsem".
  Qed.

  Lemma otp_dec_correct_r E K (k c : vgG) X R e :
    ⊢ (BREL e ≤ fill K (SOMEV (vgval (otp_dec_sem k c))) @ E <|X|> {{R}}) -∗
    (BREL e ≤ fill K (otp_dec (vgval k) (vgval c)) @ E <|X|> {{R}}).
  Proof with (repeat rewrite fill_app; simpl).
    iIntros "Hsem". rewrite /otp_dec /otp_dec_sem.
    brel_pures'... brel_pures_r.
    iApply "Hsem".
  Qed.

  #[local] Notation Grp := (sem_τFT (fin_val := vg_fv)).
  #[local] Existing Instance multi_ty_fvt.

  Lemma sem_typed_mult Γ1 Γ2 Γ3 e1 e1' e2 e2' ρ :
    ⊢ sem_typed Γ1 e2 e2' ρ Grp Γ2 -∗ sem_typed Γ2 e1 e1' ρ Grp Γ3 -∗
      sem_typed Γ1 (e1 · e2)%E (e1' · e2')%E ρ Grp Γ3.
  Proof.
    iIntros "#He2 #He1 !# %γ HΓ1 /=".
    iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
    iApply (brel_wand with "[HΓ1]"); first by iApply "He2".
    iIntros "!# % % (Hm & HΓ2) /=". iDestruct "Hm" as (m) "(-> & ->)".
    iApply (brel_bind [AppLCtx _; AppRCtx _] [AppLCtx _; AppRCtx _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
    iApply (brel_wand with "[HΓ2]"); first by iApply "He1".
    iIntros "!# % % (Hk & HΓ3) /=". iDestruct "Hk" as (k) "(-> & ->)".
    iApply (brel_mult_l []). iApply (brel_mult_r []).
    iApply brel_value. iIntros "$ !>". iFrame. by iExists _.
  Qed.

  Lemma otp_dec_typed : ⊢ ⊨ᵥ otp_dec ≤ otp_dec : (Grp -{ ⊥ }-> Grp -{ ⊥ }-> Option Grp).
  Proof.
    iApply sem_typed_closure; first done. simpl.
    iApply (sem_typed_oval _ [_]). iApplyT sem_oval_typed_ufun. simpl.
    iApplyT sem_typed_injr. iApplyT sem_typed_mult; typed_var.
    Unshelve. all: solve_typed_side.
  Qed.

  Program Global Instance OTP :
    @SYM Σ _ vg_fvt vg_fvt vg_fvt vg_fvts vg_fvts vg_fvts
         vg_fv vg_fv vg_fv otp_struct :=
    { P k m c := ⌜c = otp_enc_sem k m⌝%I
    ; dec_typed := otp_dec_typed }.
  Next Obligation.
    iIntros (k m). iApply (otp_enc_correct_l _ []). iApply (otp_enc_correct_r _ []).
    iApply brel_value. iIntros "$ !>". by iExists _.
  Qed.
  Next Obligation.
    iIntros (k m c K e E X R ->) "H". iApply otp_dec_correct_l. by rewrite otp_dec_enc_correct.
  Qed.
  Next Obligation.
    iIntros (k m c K e E X R ->) "H". iApply otp_dec_correct_r. by rewrite otp_dec_enc_correct.
  Qed.
  Next Obligation. rewrite vg_fvt_card. lia. Qed.
  Next Obligation. rewrite vg_fvt_card. lia. Qed.

End otp.

Section otp_ots. 
  Context `{probblazeRGS Σ}.
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  #[local] Notation n := (S n'').
  Import fingroup.
  Import valgroup_tactics.

  Local Definition enc_real := enc_real otp_struct.
  Local Definition enc_ideal := enc_ideal otp_struct.

  Definition lift_vg (h : vgG → vgG) : nat → nat :=
    λ k, match vg_of_int_sem k with
         | None => k
         | Some k => int_of_vg_sem (h k)
         end.

  Local Instance lift_vg_bij h `{!Bij h} : Bij (lift_vg h).
  Proof. 
    split.
    - intros x y Heq.
      unfold lift_vg in Heq.
      destruct (vg_of_int_sem x) eqn:Hx; destruct (vg_of_int_sem y) eqn:Hy; last done.
      + apply int_of_vg_sem_inj, (inj h) in Heq as ->.
        by rewrite -(vg_of_int_of_vg_sem _ _ Hx) -(vg_of_int_of_vg_sem _ _ Hy).
      + rewrite -Heq in Hy. by rewrite int_of_vg_of_int_sem in Hy. 
      + rewrite Heq in Hx. by rewrite int_of_vg_of_int_sem in Hx. 
    - intros y.
      destruct (vg_of_int_sem y) as [xy|] eqn:Hy; last by exists y; rewrite /lift_vg Hy.
      destruct (surj h xy) as [xk Hxk].
      exists (int_of_vg_sem xk).
      by rewrite /lift_vg int_of_vg_of_int_sem Hxk (vg_of_int_of_vg_sem _ _ Hy).
  Qed.

  Lemma lift_vg_bound h : ∀ k : nat, k < S n → lift_vg h k < S n.
  Proof.
    intros k Hlt.
    destruct (vg_of_int_sem_surj k) as (xk & Hxk & _); first by rewrite vgG_card.
    rewrite /lift_vg Hxk -vgG_card.
    apply int_of_vg_sem_bound.
  Qed.

  (* The key under which [m] encrypts to [c]. *)
  Definition otp_key_of (m c : vgG) : vgG := (m * c^-1)%g.

  Local Instance otp_key_of_bij m : Bij (otp_key_of m).
  Proof.
    rewrite /otp_key_of. split.
    - intros x y Heq. apply (mulgI m) in Heq. exact (invg_inj Heq).
    - intros k. exists (k^-1 * m)%g. by rewrite invMg invgK mulgA mulgV mul1g.
  Qed.

  Lemma otp_enc_key_of m c : otp_enc_sem (otp_key_of m c) m = c.
  Proof. by rewrite /otp_enc_sem /otp_key_of invMg invgK -mulgA mulVg mulg1. Qed.

  Lemma otp_enc_real_ideal_1 : 
    ⊢ sem_typed [] enc_real enc_ideal ⊥ (𝟙 ⊸ (sem_τFT (fin_val := vg_fv) → sem_τFT (fin_val := vg_fv)))%T [].
  Proof. 
    iIntros "!# %vs Hvs /=".
    rewrite /enc_real /enc_ideal /ske.enc_real /ske.enc_ideal.
    iApply brel_value. iIntros "$ !>".
    iSplitL; last done.
    iIntros (??) "(->&->)".
    brel_pures'.
    iModIntro.
    rewrite /sem_ty_arr /sem_ty_mbang /rand_key /rand_cipher /rand_fvt /=.
    iIntros (m1 m2) "!> (%m&->&->)".
    brel_pures'.
    iApply (brel_couple_rand_rand _ _ (lift_vg (λ k, otp_enc_sem k m))).
    { rewrite /fvt_of_fvts vg_fvt_card. assert (S otp_ots.n - 1 = otp_ots.n)%Z as -> by lia. 
      rewrite Nat2Z.id. apply lift_vg_bound. }
    iIntros (k) "%Hklt".
    brel_pures'.
    assert (∃ xk : vgG, vg_of_int_sem k = Some xk) as (xk & Heqk).
    { destruct (vg_of_int_sem_surj k) as (xk & Hxk & _); last by eexists.
      rewrite /fvt_of_fvts vg_fvt_card in Hklt. rewrite vgG_card. lia. }
    iApply brel_vg_of_int_correct_l; first done.
    iApply brel_vg_of_int_correct_r.
    { rewrite /lift_vg Heqk. apply int_of_vg_of_int_sem. }
    brel_pures'.
    iApply otp_enc_correct_l.
    iApply brel_value.
    iIntros "$ !>".
    by iExists _.
  Qed. 

  Lemma otp_enc_real_ideal_2 : 
    ⊢ sem_typed [] enc_ideal enc_real ⊥ (𝟙 ⊸ (sem_τFT (fin_val := vg_fv) → sem_τFT (fin_val := vg_fv)))%T [].
  Proof. 
    iIntros "!# %vs Hvs /=".
    rewrite /enc_real /enc_ideal /ske.enc_real /ske.enc_ideal.
    iApply brel_value. iIntros "$ !>".
    iSplitL; last done.
    iIntros (??) "(->&->)".
    brel_pures'.
    iModIntro.
    rewrite /sem_ty_arr /sem_ty_mbang /rand_key /rand_cipher /rand_fvt /=.
    iIntros (m1 m2) "!> (%m&->&->)".
    brel_pures'.
    iApply (brel_couple_rand_rand _ _ (lift_vg (otp_key_of m))).
    { rewrite /fvt_of_fvts vg_fvt_card. assert (S otp_ots.n - 1 = otp_ots.n)%Z as -> by lia. 
      rewrite Nat2Z.id. apply lift_vg_bound. }
    iIntros (c) "%Hclt".
    brel_pures'.
    assert (∃ xc : vgG, vg_of_int_sem c = Some xc) as (xc & Heqc).
    { destruct (vg_of_int_sem_surj c) as (xc & Hxc & _); last by eexists.
      rewrite /fvt_of_fvts vg_fvt_card in Hclt. rewrite vgG_card. lia. }
    iApply brel_vg_of_int_correct_l; first done.
    iApply brel_vg_of_int_correct_r.
    { rewrite /lift_vg Heqc. apply int_of_vg_of_int_sem. }
    brel_pures'.
    iApply otp_enc_correct_r.
    rewrite otp_enc_key_of.
    iApply brel_value.
    iIntros "$ !>".
    by iExists _.
  Qed. 

End otp_ots.

