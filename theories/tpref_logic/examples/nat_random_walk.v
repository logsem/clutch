(** Almost-sure termination of a simple random walk over the natural numbers *)
From Coq Require Import Reals Psatz.
From iris.base_logic.lib Require Import invariants.
From clutch.prob_lang Require Import lang notation.
From clutch.tpref_logic Require Import weakestpre spec primitive_laws proofmode adequacy.
From clutch.prob Require Import distribution markov.
From clutch.tpref_logic.examples Require Import flip.
#[local] Open Scope R.

(** Model *)
Definition nrw_step (n : nat) :=
  match n with
    | 0 => dzero
    | S m => fair_conv_comb (dret m) (dret (S (S m)))
  end.

Definition nrw_to_final (n : nat) : option nat :=
  match n with
    | 0 => Some 0%nat
    | S m => None
  end.

Definition nat_random_walk_mixin : MarkovMixin nrw_step nrw_to_final.
Proof. constructor. by intros [] [] []; simplify_eq=>/=. Qed.

Canonical Structure nat_random_walk : markov := Markov _ _ nat_random_walk_mixin.

(** Termination proof, by hand  *)
Lemma nrw_mass_Sn (n : nat) :
  SeriesC (lim_exec (S n)) = 0.5 * (SeriesC (lim_exec n) + SeriesC (lim_exec (S (S n)))).
Proof.
  rewrite {1}lim_exec_step /step_or_final /=.
  rewrite -SeriesC_plus // -SeriesC_scal_l.
  apply SeriesC_ext => m.
  rewrite fair_conv_comb_dbind.
  rewrite 2!dret_id_left'.
  rewrite fair_conv_comb_pmf /=.
  real_solver.
Qed.

Lemma nrw_mass_SSn (n : nat) :
  SeriesC (lim_exec (S (S n))) = 2 * SeriesC (lim_exec (S n)) - SeriesC (lim_exec n).
Proof. rewrite (nrw_mass_Sn  n). lra. Qed.

Lemma nrw_zero :
  SeriesC (lim_exec 0%nat) = 1.
Proof.
  erewrite lim_exec_final; [|done]. apply dret_mass.
Qed.

Lemma nrw_no_step_down (n : nat) :
  SeriesC (lim_exec (S n)) < SeriesC (lim_exec n) →
  ∃ k, SeriesC (lim_exec (S k + n)%nat) < 0.
Proof.
  intros Hlt.
  set (d := SeriesC (lim_exec n) - SeriesC (lim_exec (S n))).
  assert (0 < d) as Hd.
  { rewrite /d. lra. }
  assert (∀ k l, l ≤ k →
                 SeriesC (lim_exec ((S l) + n)%nat) = SeriesC (lim_exec n) - ((S l)* d)%R) as Haux.
  { induction k.
    - intros [] Hl; simpl in Hl.
      + rewrite /d. simpl. lra.
      + inversion Hl.
    - intros l H.
      + inversion H.
        * rewrite nrw_mass_SSn -/plus.
          replace (S (k + n)%nat) with (S k + n)%nat; auto.
          rewrite (IHk k); auto.
          destruct k.
          ** simpl. lra.
          ** rewrite IHk; auto. simpl. lra.
       * apply IHk; auto. }
  assert (∃ r, 0 <= r ∧ 1 < r * d) as [r [Hr1 Hr2]].
  { exists (1 + (1/d)); split.
    - apply Rplus_le_le_0_compat; [lra | ].
      apply Rcomplements.Rdiv_le_0_compat; lra.
    - rewrite Rmult_plus_distr_r.
      rewrite /Rdiv.
      rewrite 2!Rmult_1_l.
      rewrite Rinv_l; lra. }
  assert (∃ l, 1 < (S l * d)) as [k ?].
  { destruct (Rcomplements.nfloor_ex r) as [l [Hl1 Hl2]]; auto.
    exists l.
    etrans; [apply Hr2|].
    apply Rmult_lt_compat_r; [done|].
    rewrite S_INR //. }
  exists k.
  rewrite (Haux k k); [|done].
  apply Rlt_minus.
  eapply Rle_lt_trans; eauto.
Qed.

Lemma nrw_non_decr (n : nat) :
  SeriesC (lim_exec n) <= SeriesC (lim_exec (S n)).
Proof.
  destruct (Rle_lt_dec (SeriesC (lim_exec n)) (SeriesC (lim_exec (S n))))
    as [H1 | H2]; [done|].
  exfalso.
  specialize (nrw_no_step_down n H2) as (k & Hk).
  assert (0 <= SeriesC (lim_exec (S k + n)%nat)); [done|].
  lra.
Qed.

Lemma nrw_AST (n : nat) :
  SeriesC (lim_exec n) = 1.
Proof.
  induction n.
  - apply nrw_zero.
  - symmetry.
    apply Rle_antisym; [|done].
    rewrite -IHn.
    apply nrw_non_decr.
Qed.

(** Recursion through the store (Landin's knot) *)
Definition myrec : val :=
  λ: "f",
    let: "r" := ref (λ: "x", "x") in
    "r" <- (λ: "x", "f" (! "r") "x");;
    ! "r".

Section myrec_spec.
  Context `{!tprG δ Σ}.

  Definition nmyrec := nroot .@ "myrec".

  Lemma wp_myrec (P : val → iProp Σ) (Q : val → val → iProp Σ) (F v1 : val) E :
    ↑nmyrec ⊆ E →
    (∀ (f v2 : val),
        ⟨⟨⟨ (∀ (v3 : val), ⟨⟨⟨ P v3 ⟩⟩⟩ f v3 @ E ⟨⟨⟨ u, RET u; Q u v3 ⟩⟩⟩) ∗
            P v2 ⟩⟩⟩
          F f v2 @ E
        ⟨⟨⟨ u, RET u; Q u v2 ⟩⟩⟩) ⊢
    ⟨⟨⟨ P v1 ⟩⟩⟩
      myrec F v1 @ E
    ⟨⟨⟨ u, RET u; Q u v1 ⟩⟩⟩.
  Proof.
    iIntros (?) "#HF"; iIntros (Ψ) "!# HP HΨ".
    wp_lam.
    wp_alloc r as "Hr".
    wp_let.
    wp_store.
    wp_load.
    iMod (inv_alloc (nroot .@ "myrec") _ _ with "Hr") as "#inv".
    wp_pures.
    iLöb as "IH" forall (v1 Ψ).
    wp_bind (! _)%E.
    iInv nmyrec as ">Hr" "cl".
    wp_load.
    iMod ("cl" with "Hr") as "_".
    iModIntro.
    iApply ("HF" with "[HP]"); [|done].
    iFrame.
    iIntros (v3).
    iModIntro.
    iIntros (Φ) "HP HQ".
    wp_pures.
    (* To do a fully generic higher-order spec we'll need something akin to
       later credits or a model construction (just like in [determinize.v]) *)
  Abort.

End myrec_spec.

(** A random walk on the natural numbers  *)
Definition F : val :=
  λ: "f", λ: "n",
    if: "n" = #0 then #() else
    if: flip then "f" ("n" - #1) else "f" ("n" + #1).

Lemma flip_couple n :
    Rcoupl fair_coin (step (m := nat_random_walk) (S n))
      (λ b m, if b then m = n else m = S (S n)).
Proof.
  rewrite /=.
  rewrite /fair_conv_comb.
  rewrite -{1}(dret_id_right fair_coin).
  eapply Rcoupl_dbind; [|eapply Rcoupl_eq].
  intros ? [] ->; by eapply Rcoupl_dret.
Qed.

Section nat_rw_prog_spec.
  Context `{!tprG nat_random_walk Σ}.

  Lemma wp_nat_rw (n : nat) :
    ⟨⟨⟨ specF n ⟩⟩⟩
      myrec F #n
    ⟨⟨⟨ m, RET #(); specF m ⟩⟩⟩.
  Proof.
    iIntros (Ψ) "HP HΨ".
    wp_lam.
    wp_alloc r as "Hr".
    wp_let.
    wp_store.
    wp_load.
    wp_pures.
    iLöb as "IH" forall (n Ψ).
    wp_bind (! _)%E.
    wp_load.
    rewrite {4}/F.
    wp_pures; rewrite -/flip.
    destruct n.
    { rewrite bool_decide_eq_true_2 //. wp_if. by iApply "HΨ". }
    rewrite bool_decide_eq_false_2; [|done].
    wp_if.
    wp_apply (rwp_couple_flip with "HP").
    { apply flip_couple. }
    iIntros ([] m) "[Hspec ->] /="; wp_pures.
    - assert (S n - 1 = n)%Z as -> by lia.
      wp_apply ("IH" with "Hspec HΨ Hr").
    - assert (S n + 1 = S (S n))%Z as -> by lia.
      wp_apply ("IH" with "Hspec HΨ Hr").
  Qed.

End nat_rw_prog_spec.
