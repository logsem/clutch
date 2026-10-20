From clutch.prob_eff_lang.probblaze Require Import notation proofmode.
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
  Definition otp_dec : val := λ: "k" "m", "k" · "m".

  Global Instance otp_struct :
    @SYM_struct vg_fvt vg_fvts vg_fvt vg_fvts vg_fvt vg_fvts :=
    { enc := otp_enc ; dec := otp_dec }.

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
    (BREL fill K (vgval (otp_enc_sem k m)) ≤ e @ E <|X|> {{R}}) -∗
    (BREL fill K (otp_enc (vgval k) (vgval m)) ≤ e @ E <|X|> {{R}}).
  Proof with (repeat rewrite fill_app; simpl).
    iIntros "Hsem". rewrite /otp_enc /otp_enc_sem.
    brel_pures'...
    brel_mult_l...
    iApply "Hsem".
  Qed.

  Lemma otp_enc_correct_r E K (k m : vgG) X R e :
    (BREL e ≤ fill K (vgval (otp_enc_sem k m)) @ E <|X|> {{R}}) -∗
    (BREL e ≤ fill K (otp_enc (vgval k) (vgval m)) @ E <|X|> {{R}}).
  Proof with (repeat rewrite fill_app; simpl).
    iIntros "Hsem". rewrite /otp_enc /otp_enc_sem.
    brel_pures'...
    brel_mult_r...
    iApply "Hsem".
  Qed.

  Lemma otp_dec_correct_l E K (k c : vgG) X R e :
    (BREL fill K (vgval (otp_dec_sem k c)) ≤ e @ E <|X|> {{R}}) -∗
    (BREL fill K (otp_dec (vgval k) (vgval c)) ≤ e @ E <|X|> {{R}}).
  Proof with (repeat rewrite fill_app; simpl).
    iIntros "Hsem". rewrite /otp_dec /otp_dec_sem.
    brel_pures'...
    iApply "Hsem".
  Qed.

  Lemma otp_dec_correct_r E K (k c : vgG) X R e :
    (BREL e ≤ fill K (vgval (otp_dec_sem k c)) @ E <|X|> {{R}}) -∗
    (BREL e ≤ fill K (otp_dec (vgval k) (vgval c)) @ E <|X|> {{R}}).
  Proof with (repeat rewrite fill_app; simpl).
    iIntros "Hsem". rewrite /otp_dec /otp_dec_sem.
    brel_pures'...
    iApply "Hsem".
  Qed.

  Program Global Instance OTP :
    @SYM Σ _ vg_fvt vg_fvt vg_fvt vg_fvts vg_fvts vg_fvts
         vg_fv vg_fv vg_fv otp_struct :=
    { enc_sem := otp_enc_sem
    ; dec_sem := otp_dec_sem
    ; dec_enc_sem_correct := otp_dec_enc_correct
    ; enc_correct_l := otp_enc_correct_l
    ; enc_correct_r := otp_enc_correct_r
    ; dec_correct_l := otp_dec_correct_l
    ; dec_correct_r := otp_dec_correct_r }.
  Next Obligation. rewrite vg_fvt_card. lia. Qed.
  Next Obligation. rewrite vg_fvt_card. lia. Qed.

End otp.

From clutch.prob_eff_lang.probblaze Require Import logic sem_judgement sem_types sem_def.

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

  Definition f : vgG → nat → nat := λ m k, match vg_of_int_sem k with
                                               | None => k
                                               | Some k => int_of_vg_sem (otp_enc_sem k m)
                                           end.
 
  Local Instance f_bij m : Bij (f m).
  Proof. 
    split.
    - intros x y Heq.
      unfold f in Heq.
      destruct (vg_of_int_sem x) eqn:Hx; destruct (vg_of_int_sem y) eqn:Hy; last done.
      + apply int_of_vg_sem_inj, (inj (λ k, otp_enc_sem k m)) in Heq as ->.
        by rewrite -(vg_of_int_of_vg_sem _ _ Hx) -(vg_of_int_of_vg_sem _ _ Hy).
      + rewrite -Heq in Hy. by rewrite int_of_vg_of_int_sem in Hy. 
      + rewrite Heq in Hx. by rewrite int_of_vg_of_int_sem in Hx. 
    - intros y.
      destruct (vg_of_int_sem y) as [xy|] eqn:Hy; last by exists y; rewrite /f Hy.
      destruct (surj (λ k, otp_enc_sem k m) xy) as [xk Hxk].
      exists (int_of_vg_sem xk).
      by rewrite /f int_of_vg_of_int_sem Hxk (vg_of_int_of_vg_sem _ _ Hy).
  Qed.

  Lemma f_bound m : ∀ k : nat, k < S n → f m k < S n.
  Proof.
    intros k Hlt.
    destruct (vg_of_int_sem_surj k) as (xk & Hxk & _); first by rewrite vgG_card.
    rewrite /f Hxk -vgG_card.
    apply int_of_vg_sem_bound.
  Qed.

  Lemma otp_enc_real_ideal_1 : 
    ⊢ sem_typed [] enc_real enc_ideal ⊥ (sem_ty_group → sem_ty_group)%T [].
  Proof. 
    unfold enc_real, enc_ideal.
    unfold rand_cipher. simpl.
    iIntros "!> %vs Hvs /=".
    rewrite !lookup_delete_eq; 
      rewrite lookup_delete_ne; last done.
    rewrite !lookup_delete_eq.
    brel_pures'.
    iModIntro. iFrame.
    rewrite /sem_ty_arr /sem_ty_mbang /rand_key /rand_cipher /rand_fvt /=.
    iIntros (m1 m2) "!> (%m&->&->)".
    brel_pures'.
    iApply (brel_couple_rand_rand _ _ (f m)).
    { rewrite /fvt_of_fvts vg_fvt_card. assert (S otp_ots.n - 1 = otp_ots.n)%Z as -> by lia. 
      rewrite Nat2Z.id. apply f_bound. }
    iIntros (k) "%Hklt".
    brel_pures'.
    assert (∃ xk : vgG, vg_of_int_sem k = Some xk) as (xk & Heqk).
    { destruct (vg_of_int_sem_surj k) as (xk & Hxk & _); last by eexists.
      rewrite /fvt_of_fvts vg_fvt_card in Hklt. rewrite vgG_card. lia. }
    iApply brel_vg_of_int_correct_l; first done.
    iApply brel_vg_of_int_correct_r.
    { unfold f. rewrite Heqk. apply int_of_vg_of_int_sem. }
    brel_pures'.
    iApply otp_enc_correct_l.
    iApply brel_value.
    iIntros "$ !>".
    by iExists _.
  Qed. 

End otp_ots.

