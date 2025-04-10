From Coq Require Import QArith Reals Psatz.
From Coquelicot Require Import Rcomplements.
From clutch.prelude Require Import base.

Ltac nat_solver :=
  by (match goal with |- context [(?m ^ ?n)%nat] => unfold Nat.pow
                 | _ => idtac
      end ; lia || nia).

(* try pushing expressions from R to nat *)
Ltac nify_r :=
  repeat match goal with
    | |- context [0%R] => rewrite -INR_0
    | |- context [1%R] => rewrite -INR_1
    | |- context [((INR ?m) ^ ?n)%R] => rewrite -pow_INR
    (* | |- context [exp (?x * INR ?n)%R] => rewrite -(exp_pow x n) *)
    | |- context [(INR ?n - INR ?m)%R] =>
        rewrite -(minus_INR n m) ; [|try nat_solver]
    | |- context [(INR ?n + INR ?m)%R] => rewrite -(plus_INR n m)
    (* | |- context [(INR ?n + 1)%R] => rewrite -(S_INR n) *)
    | |- context [(INR ?n * INR ?m)%R] => rewrite -(mult_INR n m)
    | |- context [IPR ?p] => rewrite -(INR_IPR p)
    | |- INR _ = INR _ => f_equal
    | |- not (INR _ = INR _) => apply not_INR
    | |- (INR _ <= INR _)%R => apply le_INR
    | |- (INR _ < INR _)%R => apply lt_INR
    end.

(* Local Coercion inject_Z : Z >-> QArith_base.Q. *)
Ltac zify_q := unfold Qeq, Qlt, Qle ; simpl Qden ; simpl Qnum.

Lemma IZR_Q2R_inject_Z (z : Z) : IZR z = Q2R (inject_Z z).
Proof. rewrite /Q2R. simpl Qden. simpl Qnum. rewrite RMicromega.Rinv_1. reflexivity. Qed.

Lemma INR_Q2R_of_nat (n : nat) : INR n = Q2R (inject_Z (Z.of_nat n)).
Proof. rewrite ?INR_IZR_INZ ?IZR_Q2R_inject_Z. reflexivity. Qed.

Ltac qify_r :=
  repeat rewrite
    ?IZR_Q2R_inject_Z ?INR_Q2R_of_nat
  -?INR_IPR
  -?RMicromega.Q2R_0 -?RMicromega.Q2R_1
  -?Qreals.Q2R_plus -?Qreals.Q2R_mult
  -?Qreals.Q2R_opp -?Qreals.Q2R_minus
  -?Qreals.Q2R_inv -?Qreals.Q2R_div
  ;
    repeat (apply Qreals.Qle_Rle || apply Qreals.Qlt_Rlt || apply Qreals.Qeq_eqR).

Lemma Qminus_0_r x : (x - 0 == x)%Q.
Proof. zify_q. nia. Qed.

Lemma Qdiv_0_l x : (0 / x == 0)%Q.
Proof. zify_q. nia. Qed.


(* Notation "x ≤ y" := (Rle x y) (at level 70, no associativity) : R_scope. *)
(* Notation "x ≥ y" := (Rge x y) (at level 70, no associativity) : R_scope. *)

#[local] Open Scope R.

#[global] Instance Rge_Transitive: Transitive Rge.
Proof. intros ???. eapply Rge_trans. Qed.
#[global] Instance Rle_Transitive: Transitive Rle.
Proof. intros ???. eapply Rle_trans. Qed.
#[global] Instance Rge_Reflexive: Reflexive Rge.
Proof. intros ?. eapply Rge_refl. Qed.
#[global] Instance Rle_Reflexive: Reflexive Rle.
Proof. intros ?. eapply Rle_refl. Qed.
#[global] Instance Rgt_Transitive: Transitive Rgt.
Proof. intros ???. eapply Rgt_trans. Qed.
#[global] Instance Rlt_Transitive: Transitive Rlt.
Proof. intros ???. eapply Rlt_trans. Qed.

#[global] Instance Req_decision (r1 r2 : R) : Decision (r1 = r2).
Proof. destruct (Rle_dec r1 r2); destruct (Rle_dec r2 r1);
 [left | right | right |]; lra. Qed.
#[global] Instance Rgt_decision (r1 r2 : R) : Decision (Rgt r1 r2).
Proof. apply Rgt_dec. Qed.
#[global] Instance Rge_decision (r1 r2 : R) : Decision (Rge r1 r2).
Proof. apply Rge_dec. Qed.
#[global] Instance Rlt_decision (r1 r2 : R) : Decision (Rlt r1 r2).
Proof. apply Rlt_dec. Qed.
#[global] Instance Rle_decision (r1 r2 : R) : Decision (Rle r1 r2).
Proof. apply Rle_dec. Qed.

#[global] Instance Rlt_plus_proper: Proper (Rlt ==> Rlt ==> Rlt) Rplus.
Proof.
  intros ?? Hle ?? Hle'. apply Rplus_lt_compat; auto.
Qed.
#[global] Instance Rlt_plus_proper': Proper (Rlt ==> eq ==> Rlt) Rplus.
Proof.
  intros ?? Hle ?? Hle'. subst. nra.
Qed.
#[global] Instance Rlt_plus_proper'': Proper (Rlt ==> Rle ==> Rlt) Rplus.
Proof.
  intros ?? Hle ?? Hle'. subst. nra.
Qed.

#[global] Instance Rle_plus_proper_left: Proper (Rle ==> eq ==> Rle) Rplus.
Proof. intros ?? Hle ?? Hle'. nra. Qed.
#[global] Instance Rle_plus_proper_right: Proper (eq ==> Rle ==> Rle) Rplus.
Proof. intros ?? Hle ?? Hle'. nra. Qed.
#[global] Instance Rle_plus_proper: Proper (Rle ==> Rle ==> Rle) Rplus.
Proof. intros ?? Hle ?? Hle'. nra. Qed.

Lemma Rmax_INR a b: Rmax (INR a) (INR b) = INR (max a b).
Proof.
  apply Rmax_case_strong; intros ?%INR_le; f_equal;
    [ rewrite Nat.max_l // | rewrite Nat.max_r // ].
Qed.

Global Coercion INR : nat >-> R.

Lemma Rmult_neq_0 (r1 r2 : R) :
  r1 * r2 ≠ 0 → r1 ≠ 0 ∧ r2 ≠ 0.
Proof. intros ?. split; intros ->; lra. Qed.

Lemma Rmult_neq_0_pos (r1 r2 : R) :
  r1 * r2 ≠ 0 → 0 <= r1 → 0 <= r2 → 0 < r1 ∧ 0 < r2.
Proof. intros [? ?]%Rmult_neq_0 ? ?. lra. Qed.

Lemma Rle_plus_plus (r1 r2 r3 r4 : R) :
  r1 <= r3 → r2 <= r4 → r1 + r2 <= r3 + r4.
Proof. lra. Qed.

Lemma Rle_plus_l (r1 r2 r3 : R) :
  r1 <= r2 → 0 <= r3 → r1 <= r2 + r3.
Proof. lra. Qed.

Lemma Rle_plus_r (r1 r2 r3 : R) :
  r1 <= r3 → 0 <= r2 → r1 <= r2 + r3.
Proof. lra. Qed.

Lemma pos_sum_nn_real p q :
    0 <= p →
    0 <= q →
    0 < p + q →
    0 < p ∨ 0 < q.
  Proof.
    intros Hp Hq Hsum.
    destruct Hp as [ Hp | Hp ]; simplify_eq; auto.
    destruct Hq as [ Hq | Hq ]; simplify_eq; auto.
    lra.
  Qed.

Lemma pos_prod_nn_real p q :
    0 <= p →
    0 <= q →
    0 < p * q →
    0 < p ∧ 0 < q.
Proof.
  intros Hp Hq Hsum.
  destruct Hp as [ Hp | Hp ]; simplify_eq; split; auto; try lra.
  destruct Hq as [ Hq | Hq ]; simplify_eq ; auto; lra.
Qed.

Lemma pos_INR_S n :
  0 < INR (S n).
Proof.
  pose proof (pos_INR n).
  rewrite S_INR; lra.
Qed.

Lemma RinvN_pos' n : 0 < / (INR (S n)).
Proof.
  assert (INR (S n) = (INR n + 1)) as ->.
  { replace 1 with (INR 1); [|done].
    rewrite -plus_INR. f_equal. lia. }
  apply RinvN_pos. 
Qed.

Lemma Req_minus_r (x y z : R):
  x + z = y → x = y - z.
Proof. intros; lra. Qed.

Lemma Rle_0_le_minus (x y : R) : (x <= y)%R -> (0 <= y - x)%R.
Proof. lra. Qed.

Lemma Rmult_pos_nat_r r (n : nat) :
  (0 <= r)%R →
  (0 <= r * n)%R.
Proof. intros. eapply Rmult_le_pos; [done|]. apply pos_INR. Qed.

Hint Resolve Rmult_pos_nat_r : real.

Lemma Rplus_le_0_compat : (forall x y, 0 <= x -> y <= y+x)%R.
Proof. intros. rewrite -{1}(Rplus_0_r y). by apply Rplus_le_compat. Qed.

Hint Resolve Rplus_le_0_compat : real.

Lemma Rminus_le_0_compat : (forall x y, 0 <= y -> x - y <= x)%R.
Proof. intros ; lra. Qed.

Hint Resolve Rminus_le_0_compat : real.

From Ltac2 Require Import Ltac2.

Ltac2 split_le_le _ :=
  let rename_prod old prod :=
    let extract_prod_name t :=
      match Constr.Unsafe.kind t with
      | Constr.Unsafe.Prod b t => Constr.Binder.name b
      | _ => None
      end in
    let name := extract_prod_name old in
    match Constr.Unsafe.kind prod with
    | Constr.Unsafe.Prod x_dom cod =>
        let dom := Constr.Binder.type x_dom in
        let b := Constr.Binder.make name dom in
        Constr.Unsafe.make (Constr.Unsafe.Prod b cod)
    | _ => prod
    end in
  let f h suf :=
    let s := String.concat (Ident.to_string h) [""; suf] in
    match Ident.of_string s with
    | None => Fresh.in_goal h
    | Some id => Fresh.in_goal id
    end
  in
  lazy_match! goal with
  | [ h : (forall z : ?dom, (?l <= @?x z <= ?u)%R)
      |- _ ] =>
      let hh := Control.hyp h in
      let t := Constr.type hh in
      let h_l := rename_prod t constr:(forall z : $dom, Rle $l ($x z)) in
      let h_u := rename_prod t constr:(forall z : $dom, Rle ($x z) $u) in
      let i_l := f h "_l" in
      let i_u := f h "_u" in
      assert $h_l as $i_l by apply $hh ;
      assert $h_u as $i_u by apply $hh ;
      clear $h
  end
  ; ltac1:(intuition idtac).


(* real_simpl should be save to use, i.e., it should make no "regrettable" choices. *)
Ltac real_simpl :=
  match goal with
         | |- _ <= _ <= _ => split

         (* arithmetic patterns *)
         (* <= *)
         | |- 0 <= _ * _ => apply Rmult_le_pos
         | |- ?a * ?b <= 1 => rewrite -(Rmult_1_r 1)
         | |- ?a * ?b <= ?a => rewrite -{2}(Rmult_1_r a)
         | |- ?a * ?b <= ?b => rewrite -{2}(Rmult_1_l b)

         | |- ?a * ?b <= ?a * ?c => apply Rmult_le_compat_l
         | |- ?a * ?b <= ?c * ?b => apply Rmult_le_compat_r
         | |- ?a * ?b <= ?c * ?d => apply Rmult_le_compat
         | |- ?a * ?b * ?c <= ?b => rewrite -{2}(Rmult_1_r b)
         | |- (0 <= ?r1 / ?r2)%R => apply Rcomplements.Rdiv_le_0_compat
         | |- (INR 0 <= ?r1 / ?r2)%R => apply Rcomplements.Rdiv_le_0_compat

         | |- ?x <= ?x + ?y => apply Rplus_le_0_compat
         | |- ?x - ?y <= ?x => apply Rminus_le_0_compat

         (* < *)
         | |- 0 < _ * _ => apply Rmult_gt_0_compat
         | |- ?a * ?b < ?a * ?c => apply Rmult_lt_compat_l
         | |- ?a * ?b < ?c * ?b => apply Rmult_lt_compat_r

         (* INR *)                           
         | |- 0 < INR _ => apply lt_0_INR                                  
         | |- 0 <= INR _ => apply pos_INR
         | |- INR _ <= INR _ => apply le_INR
         | |- INR _ < INR _ => apply lt_INR
         | |- INR _ = INR _ => f_equal
                                  
         (* = *)
         | H : ?r1 + ?r = ?r2 + ?r |- _ =>
             (apply Rplus_eq_reg_r in H; subst)
         | H : ?r + ?r1 = ?r + ?r2 |- _ =>
             (apply Rplus_eq_reg_l in H; subst)
         | H : ?a = ?a * ?b |- _ =>
             (rewrite -{1}(Rmult_1_r a) in H; apply Rmult_eq_reg_l in H)
         | |- _/_ = 1 => apply Rdiv_diag_eq

         (* simplifications *)
         | |- context[?a * (?b * ?c)] => rewrite -Rmult_assoc
         | |- context[_ > _] => rewrite /Rgt
         | H : context[_ > _] |- _ => rewrite /Rgt in H
         | H : _ <= _ <= _ |-  _  => destruct H
         | H : forall _, _ <= _ <= _ |- _ => progress repeat ltac2:(split_le_le ())
         | |- _ >= _ => apply Rle_ge

         (* general solving patterns *)
         | |- ∀ _, _ => intros
         | _ => ( done || lra || eauto with real || lia || nat_solver )
                || fail "real_simpl: no applicable clauses"
         end.

Ltac real_solver_partial :=
  match goal with
  | |- context [@bool_decide ?P ?dec] =>
      destruct_decide (@bool_decide_reflect P dec); simplify_eq
  | |- context [ match ?x with _ => _ end ] => destruct x eqn:Hd
  | _ => real_simpl
  end.

(* real_solver_partial may make bad choices, so we require real_solver to close
   the goal with "by". *)
Ltac real_solver := by repeat real_solver_partial.
