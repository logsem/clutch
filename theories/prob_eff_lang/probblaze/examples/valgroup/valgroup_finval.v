From clutch.prob_eff_lang.probblaze Require Import notation proofmode.
From clutch.prob_eff_lang.probblaze.examples Require Import valgroup fin_val_type.
From mathcomp Require Import finset fintype.
Import fingroup.FinGroup.Exports.
Set Default Proof Using "Type*".

(** * A [val_group] is a finite value space

    Every [clutch_group] already carries exactly the data that
    [fin_val_type] / [fin_val_type_struct] / [fin_val] ask for: a finite
    carrier [vgG] injected into values by [vgval], the closed, well-typed
    coding functions [int_of_vg] / [vg_of_int], their semantic counterparts
    [int_of_vg_sem] / [vg_of_int_sem], and the [BREL] rules relating the two.
    This file packages that correspondence once, so a group-based scheme
    (the one-time pad in [otp.v], and any future one) can use a group as a
    key, message or cipher space without rebuilding the interface.

    Nothing here is scheme-specific; it is the [fin_val] counterpart of
    [valgroup.v]. *)

Section valgroup_finval.
  Context `{probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.

  Import valgroup_notation.
  Import fingroup.

  (** ** The carrier

      [vgG] is a [finGroupType]; the HB coercion down to [finType] is not
      inserted automatically here, so it is written out. *)
  Program Definition vg_fvt : fin_val_type :=
    {| fvT := fingroup_FinGroup__to__fintype_Finite vgG ; fvtval := vgval |}.
  Next Obligation. exact vgval_inj. Defined.

  (* NB [card] is qualified: [fintype] is imported above and shadows it. *)
  Lemma vg_fvt_card : @fin_val_type.card vg_fvt = S (S n'').
  Proof. rewrite /fin_val_type.card /= -cardsT. apply vgG_card. Qed.

  (** ** The syntactic coding functions *)
  Program Definition vg_fvts : @fin_val_type_struct vg_fvt :=
    {| int_of_fvt := int_of_vg ; fvt_of_int := vg_of_int ; τFT := τG |}.
  Next Obligation. exact int_of_vg_closed. Defined.
  Next Obligation. exact vg_of_int_closed. Defined.
  Next Obligation. exact int_of_vg_typed. Defined.
  Next Obligation. exact vg_of_int_typed. Defined.
  Next Obligation. exact τG_multi. Defined.

  (** ** The semantic coding functions and their [BREL] rules *)
  Program Definition vg_fv : @fin_val Σ _ vg_fvt vg_fvts :=
    {| int_of_fvt_sem := int_of_vg_sem
     ; fvt_of_int_sem := vg_of_int_sem |}.
  Next Obligation. exact τG_subtype. Defined.
  Next Obligation. exact vgval_typed. Defined.
  Next Obligation. rewrite vg_fvt_card -vgG_card. apply int_of_vg_sem_bound. Defined.
  Next Obligation. exact vg_of_int_of_vg_sem. Defined.
  Next Obligation. exact int_of_vg_of_int_sem. Defined.
  Next Obligation. exact brel_int_of_vg_sem_correct_l. Defined.
  Next Obligation. exact brel_int_of_vg_sem_correct_r. Defined.
  Next Obligation. exact brel_vg_of_int_correct_l. Defined.
  Next Obligation. exact brel_vg_of_int_correct_r. Defined.
  Next Obligation. exact brel_vg_of_int_none_l. Defined.
  Next Obligation. exact brel_vg_of_int_none_r. Defined.

End valgroup_finval.
