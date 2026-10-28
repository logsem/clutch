From iris.proofmode Require Import base.
From mathcomp Require all_boot ssrnat prime solvable.cyclic.
From clutch.prelude Require base.
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require valgroup.
From Stdlib Require Import Lia.
Set Default Proof Using "Type*".

(** The coupling for the aggregator's first message.  Alice's mask [g^ρ]
    (left) is coupled with the simulator's [g^μ] (right) such that
    [g^μ = x · g^ρ], i.e. [μ = add_coupling_nat x ρ].  The opposite
    direction uses [add_coupling_nat x^-1]. *)

Section add_bijection.

  Import fingroup valgroup base stdpp_ext.
  Import GroupScope.
  (* [g_log_id] and [id_g_log_nat] are stated under these contexts. *)
  Context `{logic.probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  #[local] Notation n := (S (S n'')).

  Definition add_coupling_nat (x : vgG) : nat → nat :=
    λ k, if decide (k < n) then fin_to_nat (g_log (x * g ^+ k)) else k.

  Global Instance add_coupling_nat_bij (x : vgG) : Bij (add_coupling_nat x).
  Proof.
    split.
    - intros a b Heq. unfold add_coupling_nat in Heq.
      case_decide as Ha; case_decide as Hb.
      + apply (inj fin_to_nat), (f_equal (λ k : fin n, g ^+ k)) in Heq.
        rewrite !g_log_id in Heq. apply (mulgI x) in Heq.
        by rewrite -(id_g_log_nat a Ha) -(id_g_log_nat b Hb) Heq.
      + subst. pose proof (fin_to_nat_lt (g_log (x * g ^+ a))). lia.
      + subst. pose proof (fin_to_nat_lt (g_log (x * g ^+ b))). lia.
      + done.
    - intros k. unfold add_coupling_nat.
      destruct (decide (k < n)) as [Hk | Hk].
      + exists (fin_to_nat (g_log (x^-1 * g ^+ k))).
        rewrite decide_True; last apply fin_to_nat_lt.
        by rewrite g_log_id mulKVg id_g_log_nat.
      + exists k. by rewrite decide_False.
  Qed.

  Lemma add_coupling_nat_bound x :
    ∀ k : nat, (k < S (S n''))%nat → (add_coupling_nat x k < S (S n''))%nat.
  Proof.
    intros k Hk. unfold add_coupling_nat.
    rewrite decide_True; last done.
    apply fin_to_nat_lt.
  Qed.

  Lemma add_coupling_nat_mult x (k : nat) :
    (k < n)%nat → g ^+ (add_coupling_nat x k) = x * g ^+ k.
  Proof.
    intros Hk. unfold add_coupling_nat.
    rewrite decide_True; last done.
    apply g_log_id.
  Qed.

  Lemma add_coupling_nat_mult_inv x (k : nat) :
    (k < n)%nat → x * g ^+ (add_coupling_nat x^-1 k) = g ^+ k.
  Proof.
    intros Hk. by rewrite add_coupling_nat_mult // mulKVg.
  Qed.

  (* The group is cyclic, hence commutative. *)
  Lemma vgG_comm (a b : vgG) : a * b = b * a.
  Proof.
    rewrite -(g_log_id a) -(g_log_id b) -!expgD.
    by rewrite ssrnat.addnC.
  Qed.

  (* Bob's message computed by the simulator, [z · u^-1] with [z = x · y]
     and [u = x · r], is the real one, [y · r^-1]. *)
  Lemma add_mask_cancel (x y r : vgG) : (x * y) * (x * r)^-1 = y * r^-1.
  Proof.
    by rewrite invMg (vgG_comm x y) -mulgA (vgG_comm r^-1 x^-1) mulKVg.
  Qed.

End add_bijection.
