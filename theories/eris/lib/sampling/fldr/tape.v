From Coq Require Import Arith.PeanoNat Lists.List Lia ZArith NArith.
From clutch.eris Require Import eris.
From clutch.common Require Import inject.
From clutch.eris.lib Require Import list.
From clutch.eris.lib.sampling.fldr Require Import implementation model walk pure distribution list_total preprocessing walk_spec.

Import ListNotations.

Local Open Scope fin.

(** A completed FLDR proposal round is represented by exactly the raw bits
    consumed by the instrumented walk. *)
Definition round_ok (ws : list nat) (bs : list (fin 2)) (i : nat) : Prop :=
  walkc (ddg_table ws) 0 (map bit_of bs) = Some (i, length bs).

Definition rejected (ws : list nat) (i : nat) : Prop :=
  ~ (i < length ws).

Fixpoint is_fldr_translation (ws : list nat) (raw : list (fin 2))
    (outs : list nat) : Prop :=
  match outs with
  | [] => raw = []
  | i :: outs' =>
      exists (rej : list (list (fin 2))) (acc tail : list (fin 2)),
        raw = concat rej ++ acc ++ tail /\
        Forall (fun bs => exists j, round_ok ws bs j /\ rejected ws j) rej /\
        round_ok ws acc i /\ i < length ws /\
        is_fldr_translation ws tail outs'
  end.

Lemma is_fldr_translation_nil ws : is_fldr_translation ws [] [].
Proof. reflexivity. Qed.

Lemma is_fldr_translation_snoc ws raw outs
    (rej : list (list (fin 2))) (acc : list (fin 2)) (i : nat) :
    is_fldr_translation ws raw outs ->
    Forall (fun bs => exists j, round_ok ws bs j /\ rejected ws j) rej ->
    round_ok ws acc i -> i < length ws ->
    is_fldr_translation ws (raw ++ concat rej ++ acc) (outs ++ [i]).
Proof.
  induction outs as [|a outs IH] in raw |- *.
  - intros Hraw Hrej Hacc Hi.
    simpl in Hraw. subst raw.
    simpl. exists rej, acc, [].
    repeat split; try done.
    rewrite app_nil_r. reflexivity.
  - intros Hraw Hrej Hacc Hi.
    simpl in Hraw.
    destruct Hraw as (rej0 & acc0 & tail & Hraw & Hrej0 & Hacc0 & Ha & Htail).
    simpl. exists rej0, acc0, (tail ++ concat rej ++ acc).
    repeat split.
    + rewrite Hraw. rewrite !app_assoc. reflexivity.
    + exact Hrej0.
    + exact Hacc0.
    + exact Ha.
    + apply IH; assumption.
Qed.

Section FldrTape.
  Context `{!erisGS Σ}.

  Definition own_fldr_tape (ws : list nat) (α : loc) (outs : list nat) : iProp Σ :=
    (∃ raw, α ↪ ((1%nat; raw) : tape) ∗ ⌜is_fldr_translation ws raw outs⌝)%I.

  Lemma twp_fldr_alloc E ws :
      [[{ True }]]
        fldr_alloc #() @ E
      [[{ (α : loc), RET #lbl:α; own_fldr_tape ws α [] }]].
  Proof.
    iIntros (Φ) "_ HΦ".
    unfold fldr_alloc.

    wp_pures.
    wp_apply (twp_alloc_tape 1 1 E with "[$]") as (α) "Hα".
    iApply "HΦ".
    iExists [].
    iFrame.
    iPureIntro. apply is_fldr_translation_nil.
  Qed.
  Lemma twp_fldr_loop_tape E (ws : list nat) (vrows : val) (α : loc)
      (i : nat) (outs : list nat) :
      is_list (ddg_table ws) vrows ->
      [[{ own_fldr_tape ws α (i :: outs) }]]
        fldr_loop #lbl:α vrows #(length ws) @ E
      [[{ RET #i; own_fldr_tape ws α outs }]].
  Proof.
    intros Hrows.
    iIntros (Φ) "(%raw & Hα & %Htrans) HΦ".
    simpl in Htrans.
    destruct Htrans as (rej & acc & tail & Hraw & Hrej & Hacc & Hi & Htail).
    subst raw.
    iRevert (acc tail i outs Hrej Hacc Hi Htail Φ) "Hα HΦ".
    iInduction rej as [|bs rej] "IH".
    - iIntros (acc tail i outs Hrej Hacc Hi Htail Φ) "Hα HΦ".
      rewrite /fldr_loop.
      wp_rec; wp_pures.
      wp_apply (twp_fldr_walk_tape E (ddg_table ws) vrows 0 α acc tail i Hacc
        with "[Hα]") as "Hα".
      { iSplit; [iPureIntro; exact Hrows|iFrame]. }
      wp_pures.
      case_bool_decide; last lia.
      wp_pures.
      iApply "HΦ".
      iExists tail. iFrame. iPureIntro. exact Htail.
    - iIntros (acc tail i outs Hrej Hacc Hi Htail Φ) "Hα HΦ".
      assert (Hbs0 : exists j, round_ok ws bs j /\ rejected ws j).
      { apply (Forall_inv (P := fun bs => exists j, round_ok ws bs j /\ rejected ws j)
          (a := bs) (l := rej)); exact Hrej. }
      assert (Hrej0 : Forall
          (fun bs => exists j, round_ok ws bs j /\ rejected ws j) rej).
      { apply (Forall_inv_tail (P := fun bs => exists j, round_ok ws bs j /\ rejected ws j)
          (a := bs) (l := rej)); exact Hrej. }
      destruct Hbs0 as (j & Hbs0 & Hj).
      rewrite /fldr_loop.
      wp_rec; wp_pures.
      assert (HeqTape : ((1%nat; concat (bs :: rej) ++ acc ++ tail) : tape) =
          ((1%nat; bs ++ concat rej ++ acc ++ tail) : tape)).
      { f_equal. simpl. repeat rewrite app_assoc. reflexivity. }
      iAssert (α ↪ ((1%nat; bs ++ concat rej ++ acc ++ tail) : tape))%I
          with "[Hα]" as "Hα".
       { rewrite <- HeqTape. iExact "Hα". }
      wp_apply (twp_fldr_walk_tape E (ddg_table ws) vrows 0 α bs
          (concat rej ++ acc ++ tail) j Hbs0 with "[Hα]") as "Hα'".
        { iSplit; [iPureIntro; exact Hrows|iFrame]. }
      wp_pures.
      case_bool_decide; first (exfalso; apply Hj; lia).
      wp_if.
       wp_apply ("IH" $! acc tail i outs Hrej0 Hacc Hi Htail Φ with "[Hα']").
       { iExact "Hα'". }
       { iExact "HΦ". }

  Qed.
  Lemma twp_fldr_tape_load E (ws : list nat) (vws : val) (α : loc)
      (i : nat) (outs : list nat) :
      admissible ws ->
      [[{ ⌜is_list ws vws⌝ ∗ own_fldr_tape ws α (i :: outs) }]]
        fldr_tape #lbl:α vws @ E
      [[{ RET #i; own_fldr_tape ws α outs }]].
  Proof.
    intros Hadm.
    iIntros (Φ) "(%Hws & Htape) HΦ".
    rewrite /fldr_tape.
    wp_pures.
    wp_bind (fldr_table vws).
    wp_apply (twp_fldr_table E ws vws) as (vrows) "Hrows";
      [exact Hadm|iPureIntro; exact Hws|].
    iDestruct "Hrows" as %Hrows.
    wp_let.
    wp_bind (list_length vws).
    wp_apply (twp_list_length E ws vws) as (n) "Hn"; [iPureIntro; exact Hws|].
    iDestruct "Hn" as %Hn.
    rewrite Hn.
    wp_apply (twp_fldr_loop_tape E ws vrows α i outs Hrows with "[Htape]") as "Htape".
    { iExact "Htape". }
    iApply "HΦ".
    iExact "Htape".
  Qed.
  Example fldr_translation_321 :
      is_fldr_translation ([3%nat; 2%nat; 1%nat] : list nat)
        [1%fin; 1%fin; 1%fin] [2%nat].
  Proof.
    simpl. exists [], [1%fin; 1%fin; 1%fin], [].
    split; [reflexivity|].
    split; [constructor|].
    split; [vm_compute; reflexivity|].
    split; [lia|reflexivity].
  Qed.
End FldrTape.
