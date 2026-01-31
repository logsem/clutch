From Stdlib Require Import Reals Psatz.
From clutch Require Import base.
Set Default Proof Using "Type*".

Definition ε_bday Q N := ((INR Q - 1) * INR Q / (2 * INR N))%R.

Lemma sum_seq N :
  (((INR N - 1) * INR N) / 2)%R = INR (fold_left Nat.add (seq 0 N) 0).
Proof.
  symmetry.
  cut (Rmult 2%R (INR (fold_left Nat.add (seq 0 N) 0)) = (Rmult ((INR N - 1)) (INR N))).
  - intros foo.
    rewrite -foo.
    rewrite Rmult_comm.
    by rewrite Rmult_div_l => //.
  - destruct N.
    { compute. lra. }
    induction N as [|k IH] ; [compute ; lra|].
    rewrite seq_S. replace (0+ S k) with (S k) by lia.
    rewrite fold_left_app.
    rewrite {1}/fold_left.
    revert IH.
    replace 2%R with (INR 2%nat) => //.
    rewrite -mult_INR.
    intros IH.
    rewrite -mult_INR.
    rewrite Nat.mul_add_distr_l.
    rewrite plus_INR.
    rewrite IH.
    replace ((INR (S k)) - 1)%R with (INR k).
    2:{ replace 1%R with (INR 1) by easy. rewrite -minus_INR => //. 2: f_equal ; simpl ; lia.
        f_equal. lia. }
    rewrite -mult_INR. rewrite -plus_INR.
    replace ((INR (S (S k))) - 1)%R with (INR (S k)).
    2:{ replace 1%R with (INR 1) by easy. rewrite -minus_INR => //.
        lia. }
    rewrite -mult_INR. f_equal. lia.
Qed.

Lemma bday_sum Q N : ε_bday Q N = (INR (fold_left Nat.add (seq 0 Q) 0%nat) / INR N)%R.
Proof.
  by rewrite /ε_bday Rdiv_mult_distr sum_seq.
Qed.
