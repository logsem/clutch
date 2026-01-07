From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import gset_bij.
From clutch.eris Require Import eris.
From clutch.eris.tutorial Require Import hash_interface.
From clutch.eris.lib Require Import list array.
From clutch.eris Require Export eris.

Set Default Proof Using "Type*".

Definition geo
  := (λ:"_", (rec: "g" "n" :=
        if: ((rand #1) = #0)%E
          then "n"
          else ("g" ("n" + #1))) #0)%V.


Section geometric.

  Context `{!erisGS Σ}.

  Lemma geo_0 :
    {{{ ↯ (1/2%nat)%R }}} geo #() {{{ (v : Z), RET #v; ⌜v = 0⌝}}}.
  Proof.
    unfold geo. iIntros (post) "Herr Hpost". wp_pures.
    set (E2 := fun n => match n with 0 => 0 | _ => 1 end).
    wp_apply (wp_rand_exp_nat 1 _ _ E2 with "[$Herr]").
    { intros. destruct n ; cbn ; lra. }
    {
      erewrite <- (SeriesC_singleton 1).
      right.
      eapply SeriesC_ext.
      intros n.
      subst E2. do 2 case_bool_decide.
      - subst. rewrite Rmult_1_r. lra.
      - destruct n ; try lia. apply Rmult_0_r.
      - lia.
      - reflexivity.
    }
    iIntros (n) "[%Hn Herr]".
    wp_pures.
    case_bool_decide ; wp_pures.
    - iApply "Hpost". done.
    - subst E2. cbn.
      assert (n ≠ 0). { intro. subst. apply H. done. }
      destruct n. 1: done.
      iExFalso. iApply (ec_contradict with "Herr"). reflexivity.
  Qed.

  Lemma geo_01 :
    {{{ ↯ (1/4%nat)%R }}} geo #() {{{ (v : Z), RET #v; ⌜v <= 1⌝%Z}}}.
  Proof.
    unfold geo. iIntros (post) "Herr Hpost". wp_pures.
    set (E1 := fun n => match n with 0 => 0%R | _ => (1/2)%R end).
    wp_apply (wp_rand_exp_nat 1 _ _ E1 with "[$Herr]").
    { intros. destruct n ; cbn ; lra. }
    {
      erewrite <- (SeriesC_singleton 1).
      right.
      eapply SeriesC_ext.
      intros n.
      subst E1. do 2 case_bool_decide.
      - subst. qify_r ; zify_q ; lia.
      - destruct n ; try lia. apply Rmult_0_r.
      - lia.
      - reflexivity.
    }
    iIntros (n) "[%Hn Herr]".
    wp_pures.
    case_bool_decide ; wp_pures.
    - iApply "Hpost". done.
    - subst E1. cbn.
      assert (n ≠ 0). { intro. subst. apply H. done. }
      destruct n. 1: done.
      set (E2 := fun n => match n with 0 => 0%R | _ => 1 end).
      wp_apply (wp_rand_exp_nat 1 _ _ E2 with "[$Herr]").
      { intros n'. destruct n' ; cbn ; lra. }
      {
        erewrite <- (SeriesC_singleton 1).
        right.
        eapply SeriesC_ext.
        intros n'.
        subst E2. do 2 case_bool_decide.
        - subst. qify_r ; zify_q ; lia.
        - destruct n' ; try lia. apply Rmult_0_r.
        - lia.
        - reflexivity.
      }
      iIntros (n') "[%Hn' Herr]".
      wp_pures.
      case_bool_decide ; wp_pures.
      + iApply "Hpost". done.
      + subst E2. cbn.
        assert (n' ≠ 0). { intro. subst. apply H. done. }
        destruct n'. 1: done.
        iExFalso. iApply (ec_contradict with "Herr"). reflexivity.
  Qed.

End geometric.
