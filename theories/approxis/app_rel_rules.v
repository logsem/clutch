(** Core relational rules *)
From stdpp Require Import coPset namespaces.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import list.
From clutch.common Require Import language ectx_language ectxi_language locations.
From clutch.prelude Require Import fin.
From clutch.prob_lang Require Import notation lang.
From clutch.prob_lang.spec Require Import spec_ra spec_rules spec_tactics.
From clutch.approxis Require Import ectx_lifting app_weakestpre model.
From clutch.approxis Require Export proofmode primitive_laws coupling_rules.
From clutch.base_logic Require Export spec_update.

Section rules.
  Context `{!approxisRGS Σ}.
  Implicit Types A : lrel Σ.
  Implicit Types e : expr.
  Implicit Types v w : val.

  Local Existing Instance pure_exec_fill.

  (** * Primitive rules *)

  (** ([fupd_refines] is defined in [logrel_binary.v]) *)

  (** ** Forward reductions on the LHS *)

  Lemma refines_pure_l E n
    (K' : list ectx_item) e e' t A ϕ :
    PureExec ϕ n e e' →
    ϕ →
    ▷^n (REL fill K' e' << t @ E : A)
    ⊢ REL fill K' e << t @ E : A.
  Proof.
    intros Hpure Hϕ.
    rewrite refines_eq /refines_def.
    iIntros "IH" (j ε) "Hs Hnais Herr Hpos".
    wp_pures.
    iApply ("IH" with "Hs Hnais Herr Hpos").
  Qed.

  Lemma refines_wp_l E K e1 t A :
    (WP e1 {{ v,
        REL fill K (of_val v) << t @ E : A }})%I
    ⊢ REL fill K e1 << t @ E : A.
  Proof.
    rewrite refines_eq /refines_def.
    iIntros "He" (K' ε) "Hs Hnais Herr Hpos /=".
    iApply wp_bind.
    iApply (wp_wand with "He").
    iIntros (v) "Hv".
    iApply ("Hv" with "Hs Hnais Herr Hpos").
  Qed.

  Lemma refines_atomic_l (E E' : coPset) K e1 t A
    (Hatomic : Atomic StronglyAtomic e1) :
    (∀ K', ⤇ fill K' t ={⊤, E'}=∗
             WP e1 @ E' {{ v,
              |={E', ⊤}=> ∃ t', ⤇ fill K' t' ∗
              REL fill K (of_val v) << t' @ E : A }})%I
   ⊢ REL fill K e1 << t @ E : A.
  Proof.
    rewrite refines_eq /refines_def.
    iIntros "Hlog" (K' ε) "Hs Hnais Herr Hpos /=".
    iApply wp_bind. iApply wp_atomic; auto.
    iMod ("Hlog" with "Hs") as "He". iModIntro.
    iApply (wp_wand with "He").
    iIntros (v) "Hlog".
    iMod "Hlog" as (t') "[Hr Hlog]".
    iApply ("Hlog" with "Hr Hnais Herr Hpos").
  Qed.

  (** ** Forward reductions on the RHS *)
  Lemma refines_pure_r E K' e e' t A n ϕ :
    PureExec ϕ n e e' →
    ϕ →
    (REL t << fill K' e' @ E : A)
      ⊢ REL t << fill K' e @ E : A.
  Proof.
    rewrite refines_eq /refines_def => Hpure Hϕ.
    iIntros "Hlog" (j ε) "Hj Hnais Herr Hpos /=".
    tp_pures ; auto.
    iApply ("Hlog" with "Hj Hnais Herr Hpos").
  Qed.

  (* A helper lemma for proving the stateful reductions for the RHS below *)
  Lemma refines_step_r E K' e1 e2 A :
    (∀ k, ⤇ fill k e2 -∗
         spec_update ⊤ (∃ v, ⤇ fill k (of_val v) ∗
                             REL e1 << fill K' (of_val v) @ E : A))
    ⊢ REL e1 << fill K' e2 @ E : A.
  Proof.
    rewrite refines_eq /refines_def /=.
    iIntros "He" (K'' ε) "Hs Hnais Herr Hpos /=".
    rewrite -fill_app.
    iMod ("He" with "Hs") as (v) "[Hs He]".
    rewrite fill_app.
    iSpecialize ("He" with "Hs Hnais Herr Hpos").
    by iApply "He".
  Qed.

  (* Variant of refines_step_r that doesn't require full evaluation. *)
  (* NB: refines_step_r only requires e2 as input but existentially
     quantifies v, which is important e.g. in refines_alloc_r, where v is
     freshly generated. If e2' is known, this variant can be used instead *)
  Lemma refines_steps_r E e1 e2 e2' A K' :
    (∀ K, (⤇ fill K e2 ={⊤}=∗ ⤇ fill K e2'))
    ⊢ (|={⊤}=> REL e1 << ectxi_language.fill K' e2' @ E : A)
    -∗ REL e1 << ectxi_language.fill K' e2 @ E : A.
  Proof.
    iIntros "upd >Hlog".
    rewrite refines_eq /refines_def.
    iIntros (??) "???".
    rewrite -fill_app.
    iDestruct ("upd" with "[$]") as ">?".
    rewrite fill_app.
    iApply ("Hlog" with "[$][$][$]").
  Qed.

  Lemma refines_alloc_r E K e v t A :
    IntoVal e v →
    (∀ l : loc, l ↦ₛ v -∗ REL t << fill K (of_val #l) @ E : A)%I
      ⊢ REL t << fill K (ref e) @ E : A.
  Proof.
    intros <-.
    iIntros "Hlog". simpl.
    iApply refines_step_r ; simpl.
    iIntros (K') "HK'".
    tp_alloc as l "Hl".
    iModIntro. iExists _. iFrame. by iApply "Hlog".
  Qed.

  Lemma refines_load_r E K l q v t A :
    l ↦ₛ{q} v ⊢
      (l ↦ₛ{q} v -∗ REL t << fill K (of_val v) @ E : A)
    -∗ REL t << (fill K !#l) @ E : A.
  Proof.
    iIntros "Hl Hlog".
    iApply refines_step_r.
    iIntros (k) "Hk".
    tp_load.
    iModIntro. iExists _. iFrame. by iApply "Hlog".
  Qed.

  Lemma refines_store_r E K l e e' v v' A :
    IntoVal e' v' →
    l ↦ₛ v ⊢
      (l ↦ₛ v' -∗ REL e << fill K (of_val #()) @ E : A)
    -∗ REL e << fill K (#l <- e') @ E : A.
  Proof.
    iIntros (<-) "Hl Hlog".
    iApply refines_step_r.
    iIntros (k) "Hk". simpl.
    tp_store. iModIntro. iExists _. iFrame.
    by iApply "Hlog".
  Qed.

  Lemma refines_alloctape_r E K N z t A :
    TCEq N (Z.to_nat z) →
    (∀ α : loc, α ↪ₛN (N; []) -∗ REL t << fill K (of_val #lbl:α) @ E : A)%I
    ⊢ REL t << fill K (alloc #z) @ E : A.
  Proof.
    iIntros (->) "Hlog".
    iApply refines_step_r.
    iIntros (K') "HK'".
    tp_alloctape as α "Hα".
    iModIntro. iExists _. iFrame.
    iApply "Hlog".
    iFrame; auto.
  Qed.

  Lemma refines_randT_r E K α N z n ns t A :
    TCEq N (Z.to_nat z) →
    α ↪ₛN (N; n :: ns)
   ⊢ (α ↪ₛN (N; ns)-∗ ⌜ n ≤ N ⌝ -∗ REL t << fill K (of_val #n) @ E : A)
    -∗ REL t << (fill K (rand(#lbl:α) #z)) @ E : A.
  Proof.
    iIntros (->) "Hα Hlog".
    iApply refines_step_r.
    iIntros (k) "Hk".
    iDestruct (read_spec_tape_head with "Hα") as (x xs) "[Hα' [% Hcont]]".
    tp_rand.
    iSpecialize ("Hcont" with "Hα'").
    iModIntro. iExists _. iFrame.
    rewrite H.
    iApply ("Hlog" with "Hcont").
    iPureIntro.
    rewrite -H.
    apply fin_to_nat_le.
  Qed.
  Definition refines_rand_r := refines_randT_r.

  Lemma refines_randT_empty_r K E α A N z e :
    TCEq N (Z.to_nat z) →
    ▷ α ↪ₛN (N; []) ∗
      (∀ n : nat, α ↪ₛN (N; []) -∗ ⌜ n ≤ N ⌝ -∗ REL e << fill K (Val #n) @ E : A)
    ⊢ REL e << fill K (rand(#lbl:α) #z) @ E : A.
  Proof.
    iIntros (->) "[>Hα H]".
    rewrite refines_eq /refines_def.
    iIntros (K2 ε) "Hspec Hnais Herr Hpos /=".
    wp_apply wp_rand_empty_r.
    rewrite -fill_app.
    iFrame "Hα Hspec".
    iIntros (N) "(Hα & Hb) %".
    rewrite /= fill_app.
    iSpecialize ("H" with "Hα [//] [$Hb] Hnais Herr Hpos").
    wp_apply (wp_mono with "H").
    iIntros (?) "[% [% ?]]".
    iExists _, _. iFrame.
  Qed.
  Definition refines_rand_empty_r := refines_randT_empty_r.

  Lemma refines_randU_r E K e (N : nat) (z : Z) A :
    TCEq N (Z.to_nat z) →
    (∀ (n : nat), ⌜ n ≤ N ⌝ -∗ REL e << fill K (Val #n) @ E : A)
      ⊢ REL e << fill K (rand #z) @ E : A.
  Proof.
    iIntros (?) "H".
    rewrite refines_eq /refines_def.
    iIntros (K2 ε) "Hspec Hnais Herr Hpos /=".
    rewrite -fill_app. wp_apply (wp_rand_r _ _ _ _ (K++K2)) => //.
    iSplitL "Hspec"; [iFrame |].
    iIntros (n) "Hspec %" => /=. rewrite fill_app.
    iApply ("H" with "[//] Hspec Hnais Herr Hpos").
  Qed.

  (** This rule is useful for proving that functions refine each other *)
  Lemma refines_arrow_val (v v' : val) A A' :
    □(∀ v1 v2, A v1 v2 -∗
      REL App v (of_val v1) << App v' (of_val v2) : A') ⊢
    REL (of_val v) << (of_val v') : (A → A')%lrel.
  Proof.
    iIntros "#H".
    iApply refines_ret. iModIntro.
    iModIntro. iIntros (v1 v2) "HA".
    iSpecialize ("H" with "HA").
    by iApply "H".
  Qed.

  (** * Some derived (symbolic execution) rules *)

  (** ** Stateful reductions on the LHS *)

  Lemma refines_alloc_l K E e v t A :
    IntoVal e v →
    (▷ (∀ l : loc, l ↦ v -∗
           REL fill K (of_val #l) << t @ E : A))
    ⊢ REL fill K (ref e) << t @ E : A.
  Proof.
    iIntros (<-) "Hlog".
    iApply refines_wp_l.
    wp_alloc l as "Hl". by iApply "Hlog".
  Qed.

  Lemma refines_load_l K E l q t A :
    (∃ v',
      ▷(l ↦{q} v') ∗
      ▷(l ↦{q} v' -∗ (REL fill K (of_val v') << t @ E : A)))
    ⊢ REL fill K (! #l) << t @ E : A.
  Proof.
    iIntros "[%v' [Hl Hlog]]".
    iApply refines_wp_l.
    wp_load. by iApply "Hlog".
  Qed.

  Lemma refines_store_l K E l e v' t A :
    IntoVal e v' →
    (∃ v, ▷ l ↦ v ∗
      ▷(l ↦ v' -∗ REL fill K (of_val #()) << t @ E : A))
    ⊢ REL fill K (#l <- e) << t @ E : A.
  Proof.
    iIntros (<-) "[%v [Hl Hlog]]".
    iApply refines_wp_l.
    wp_store. by iApply "Hlog".
  Qed.

  Lemma refines_alloctape_l K E N z t A :
    TCEq N (Z.to_nat z) →
    (▷ (∀ α : loc, α ↪N (N; []) -∗ REL fill K (of_val #lbl:α) << t @ E : A))%I
    ⊢ REL fill K (alloc #z) << t @ E : A.
  Proof.
    iIntros (->) "Hlog".
    iApply refines_wp_l.
    by wp_apply (wp_alloc_tape with "[//]").
  Qed.

  Lemma refines_randT_l E K α N z n ns t A :
    TCEq N (Z.to_nat z) →
    (▷ α ↪N (N; n :: ns) ∗
     ▷ (α ↪N (N; ns) -∗ ⌜ n ≤ N ⌝ -∗ REL fill K (of_val #n) << t @ E : A))
    ⊢ REL fill K (rand(#lbl:α) #z) << t @ E : A.
  Proof.
    iIntros (->) "[Hα Hlog]".
    iApply refines_wp_l.
    wp_apply (wp_rand_tape with "Hα").
    iIntros "(Hα&%)".
    iApply ("Hlog" with "Hα [//]").
  Qed.
  Definition refines_rand_l := refines_randT_l.

  Lemma refines_randT_empty_l K E α A N z e :
    TCEq N (Z.to_nat z) →
    ▷ α ↪N (N; []) ∗
      ▷ (∀ (n : nat), α ↪N (N; []) -∗ ⌜ n ≤ N ⌝ -∗ REL fill K (Val #n) << e @ E : A)
    ⊢ REL fill K (rand(#lbl:α) #z) << e @ E : A.
  Proof.
    iIntros (->) "[>Hα H]".
    rewrite refines_eq /refines_def.
    iIntros (K2 ε) "Hspec Hnais Herr Hpos /=".
    wp_apply wp_bind.
    wp_apply (wp_rand_tape_empty with "Hα").
    iIntros (n) "(Hα & %) /=".
    iApply ("H" with "Hα [//] Hspec Hnais Herr Hpos").
  Qed.
  Definition refines_rand_empty_l := refines_randT_empty_l.

  Lemma refines_randU_l E K e (N : nat) (z : Z) A :
    TCEq N (Z.to_nat z) →
    (∀ (n : nat), ⌜ n ≤ N ⌝ -∗ REL fill K (Val #n) << e @ E : A)
      ⊢ REL fill K (rand #z) << e @ E : A.
  Proof.
    iIntros (?) "H".
    rewrite refines_eq /refines_def.
    iIntros (K2 ε) "Hspec Hnais Herr Hpos /=".
    wp_apply wp_bind. wp_apply wp_rand => //.
    iIntros (n) "%" => /=.
    iApply ("H" with "[//] Hspec Hnais Herr Hpos").
  Qed.

  Lemma refines_wand E e1 e2 A A' :
    (REL e1 << e2 @ E : A) ⊢
    (∀ v1 v2, A v1 v2 ={⊤}=∗ A' v1 v2) -∗
    REL e1 << e2 @ E : A'.
  Proof.
    iIntros "He HAA".
    iApply (refines_bind [] [] with "He").
    iIntros (v v') "HA /=". iApply refines_ret.
    by iApply "HAA".
  Qed.

  Lemma refines_arrow (v v' : val) A A' :
    □ (∀ v1 v2 : val, □(REL of_val v1 << of_val v2 : A) -∗
      REL App v (of_val v1) << App v' (of_val v2) : A') ⊢
    REL (of_val v) << (of_val v') : (A → A')%lrel.
  Proof.
    iIntros "#H".
    iApply refines_arrow_val; eauto.
    iModIntro. iIntros (v1 v2) "#HA".
    iApply "H". iModIntro.
    by iApply refines_ret.
  Qed.

  Lemma refines_couple_TT_err (N M : nat) E e1 e2 A α αₛ ns nsₛ (ε : R) :
    (N <= M)%nat →
    (((S M - S N) / S M) = ε)%R →
    (▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗ ↯ ε ∗
    (∀ (n : nat),
       α ↪N (N; ns ++ [n]) ∗ αₛ ↪ₛN (M; nsₛ ++ [n]) ∗ ⌜ n ≤ N ⌝ -∗
        REL e1 << e2 @ E : A))
    ⊢ REL e1 << e2 @ E : A.
  Proof.
    iIntros (Hleq Heq) "(Hα & Hαs & Herr & Hlog)".
    rewrite refines_eq /refines_def.
    iIntros (K2 ε') "He2 Hnais Herr' Hpos/=".
    wp_apply (wp_couple_tapes N M); [done|done|].
    iFrame.
    iIntros (n) "% [Hα Hαs]".
    iApply ("Hlog" with "[$Hα $Hαs //] [$He2] Hnais Herr' Hpos").
  Qed.
  Definition refines_couple_tapes := refines_couple_TT_err.

  Lemma refines_couple_TT_frag (N M : nat) (f : nat -> nat) {_ : Inj (=) (=) f} E e1 e2 A α αₛ ns nsₛ :
    (M <= N)%nat →
    (∀ n : nat, n < S M → f n < S N) ->
    ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗
    (∀ (n : nat),
       ⌜ n ≤ N ⌝ -∗
       if bool_decide (∃ m, m ≤ M /\ f m = n) then
         ∀ m, α ↪N (N; ns ++ [f m]) ∗ αₛ ↪ₛN (M; nsₛ ++ [m]) ∗ ⌜f m ≤ N⌝ ∗ ⌜m ≤ M⌝ -∗
              REL e1 << e2 @ E : A
       else
         α ↪N (N; ns ++ [n]) ∗ αₛ ↪ₛN (M; nsₛ) ∗ ⌜ n ≤ N ⌝ -∗ REL e1 << e2 @ E : A
    )
    ⊢ REL e1 << e2 @ E : A.
  Proof.
    iIntros (Hleq Hdom) "(Hα & Hαs & Hlog)".
    rewrite refines_eq /refines_def.
    iIntros (K2 ε') "He2 Hnais Herr' Hpos/=".
    wp_apply wp_couple_fragmented_rand_rand_inj; [done|done|].
    iFrame.
    iIntros (n) "%".
    iSpecialize ("Hlog" $! n).
    case_bool_decide.
    - iIntros (m) "(Hα & Hαs & Hnm)".
      iApply ("Hlog" with "[//] [$Hα $Hαs $Hnm] [$He2] Hnais Herr' Hpos").
    - iIntros "(Hα & Hαs)".
      iApply ("Hlog" with "[//] [$Hα $Hαs] [$He2] Hnais Herr' Hpos").
  Qed.

  Lemma refines_couple_TT_adv (N M : nat) (f : nat → nat) {_ : Inj (=) (=) f} E e1 e2 A α αₛ ns nsₛ (ε : R) :
    (0 <= ε)%R →
    (N < M)%nat →
    (∀ n : nat, n < S N → f n < S M) ->
    ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗ ↯ ε ∗
      (∀ (m : nat),
          ⌜ m ≤ M ⌝ -∗
          if bool_decide (∃ n, n ≤ N /\ f n = m) then
            ∀ n, α ↪N (N; ns ++ [n]) ∗ αₛ ↪ₛN (M; nsₛ ++ [f n]) ∗ ⌜n ≤ N⌝ ∗ ⌜f n ≤ M⌝ -∗
                 REL e1 << e2 @ E : A
          else
            ∀ (ε' : R),
              ⌜ε' = ((S M) / (S M - S N) * ε)%R⌝ ∗
              α ↪N (N; ns) ∗ αₛ ↪ₛN (M; nsₛ ++ [m]) ∗ ↯ ε' ∗ ⌜ m ≤ M ⌝ -∗
              REL e1 << e2 @ E : A)
      ⊢ REL e1 << e2 @ E : A.
  Proof.
    iIntros (Hε Hleq Hdom) "(Hα & Hαs & Herr & Hlog)".
    rewrite refines_eq /refines_def.
    set ε' := mknonnegreal _ Hε.
    replace ε with ε'.(nonneg); [|done]. 
    iIntros (K2 ε2) "He2 Hnais Herr' %Hε' /=".
    wp_apply (wp_couple_fragmented_rand_rand_inj_rev' _ _ _ _ _ _ _ _ ε') ; [done|done|done|].
    iFrame "Hα Hαs Herr".
    iIntros (m) "%".
    iSpecialize ("Hlog" $! m).
    case_bool_decide.
    - iIntros (n) "(Hα & Hαs & Hnm)".
      iApply ("Hlog" with "[//] [$Hα $Hαs $Hnm] [$He2] Hnais Herr' [//]").
    - iIntros (ε'0) "(%Herr2 & Hα & Hαs & Herr'0)".
      iSpecialize ("Hlog" with "[//]").
      iApply ("Hlog" $! ε'0 with "[$Hα $Hαs $Herr'0] [$He2] Hnais [$Herr'] [//]").
      iPureIntro.
      done.
  Qed.

  Lemma refines_get_ec E e e' A :
    (∀ ε : R, ↯ ε -∗ ⌜(0 < ε)%R⌝ -∗ REL e << e' @ E : A) ⊢
    (REL e << e' @ E : A).
  Proof.
    iIntros "H".
    rewrite refines_eq /refines_def.
    iIntros (K ε) "Hfill Hown Herr %Hpos".
    replace (ε) with (ε / 2 + ε / 2)%R by lra. 
    iDestruct (ec_split with "Herr") as "[Herr1 Herr2]";
      [lra|lra|].
    iApply ("H" with "Herr1 [] Hfill Hown Herr2"); iPureIntro; lra. 
  Qed.

  Lemma refines_ind_amp E e e' A (k : R) :
    (1 < k)%R ->
    □ (∀ (ε : R),
          ⌜(0 < ε)%R⌝ -∗ □(↯ (k * ε) -∗ (REL e << e' @ E : A))
          -∗ ↯ ε -∗ (REL e << e' @ E : A))%I
      ⊢ REL e << e' @ E : A.
  Proof.
    intros Hk.
    iIntros "#IH".
    iApply refines_get_ec.
    iIntros (ε) "Herr %Hpos".
    iApply (ec_ind_amp _ k with "[IH] Herr"); auto.
  Qed.

  Lemma refines_couple_UU N f `{Bij nat nat f} K K' E A z :
    TCEq N (Z.to_nat z) →
    (∀ n : nat, n < S N → f n < S N) ->
    ▷ (∀ (n : nat), ⌜ n ≤ N ⌝ -∗ REL fill K (Val #n) << fill K' (Val #(f n)) @ E : A)
    ⊢ REL fill K (rand #z) << fill K' (rand #z) @ E : A.
  Proof.
    iIntros (-> Hdom) "Hcnt".
    rewrite refines_eq /refines_def.
    iIntros (K2 ε) "Hfill Hown Herr %Hpos".
    wp_apply wp_bind.
    rewrite -fill_app.
    iApply (wp_couple_rand_rand with "Hfill"); auto.
    iIntros "!>" (n) "[% Hspec]".
    rewrite fill_app.
    iSpecialize ("Hcnt" with "[//] Hspec Hown").
    iApply ("Hcnt" with "Herr"); done.
  Qed.

  Definition refines_couple_rands_lr := refines_couple_UU.

  Lemma refines_couple_UU_err N M ε f K K' E A (z w :Z):
    (∀ n, n < S N → f n < S M)%nat →
    (∀ n1 n2, n1 < S N → n2 < S N → f n1 = f n2 → n1 = n2)%nat →
    TCEq N (Z.to_nat z) →
    TCEq M (Z.to_nat w) →
    (N <= M)%nat →
    ((S M - S N) / S M = ε)%R →
    ↯ ε ∗
    ▷ (∀ (n : nat), ⌜ n ≤ N ⌝ -∗ REL fill K (Val #n) << fill K' (Val #(f n)) @ E : A)
    ⊢ REL fill K (rand #z) << fill K' (rand #w) @ E : A.
  Proof.
    iIntros (??->->??) "[Hε Hcnt]".
    rewrite refines_eq /refines_def.
    iIntros (K2 ε') "Hfill Hown Herr %Hpos".
    wp_apply wp_bind.
    rewrite -fill_app.
    iApply (wp_couple_rand_rand_inj _ _ f with "[$Hε $Hfill]"); try done.
    iIntros "!>" (n) "(Hspec & %Hn)".
    rewrite fill_app.
    iSpecialize ("Hcnt" with "[//] Hspec Hown").
    iApply ("Hcnt" with "Herr"); done.
  Qed.

  Lemma refines_couple_UU_err_rev N M ε f K K' E A (z w :Z):
    (∀ n, n < S M → f n < S N)%nat →
    (∀ n1 n2, n1 < S M → n2 < S M → f n1 = f n2 → n1 = n2)%nat →
    TCEq N (Z.to_nat z) →
    TCEq M (Z.to_nat w) →
    (M <= N)%nat →
    ((S N - S M) / S N = ε)%R →
    ↯ ε ∗
    ▷ (∀ (n : nat), ⌜ n ≤ M ⌝ -∗ REL fill K (Val #(f n)) << fill K' (Val #n) @ E : A)
    ⊢ REL fill K (rand #z) << fill K' (rand #w) @ E : A.
  Proof.
    iIntros (??->->??) "[Hε Hcnt]".
    rewrite refines_eq /refines_def.
    iIntros (K2 ε') "Hfill Hown Herr %Hpos".
    wp_apply wp_bind.
    rewrite -fill_app.
    iApply (wp_couple_rand_rand_rev_inj _ _ f with "[$Hε $Hfill]"); try done.
    iIntros "!>" (n) "[Hspec %]".
    rewrite fill_app.
    iSpecialize ("Hcnt" with "[//] Hspec Hown").
    iApply ("Hcnt" with "Herr"); done.
  Qed.

  Lemma refines_arrow_val_err (v v' : val) A A' k :
    (1 < k)%R ->
    □ (∀ ε,
          ⌜ (0 < ε)%R ⌝ -∗
          □ ( ↯ ((k * ε)) -∗ ∀ v1 v2, A v1 v2 -∗ REL App v (of_val v1) << App v' (of_val v2) : A' ) -∗
                ↯ ε -∗ ∀ v1 v2, A v1 v2 -∗ REL App v (of_val v1) << App v' (of_val v2) : A')
      ⊢ REL (of_val v) << (of_val v') : (A → A')%lrel.
  Proof.
    iIntros (Hk) "#H".
    iApply refines_ret. iModIntro.
    iModIntro.
    iIntros (v1 v2) "HA".
    iApply refines_get_ec.
    iIntros (ε') "Herr' %Hpos'".
    iRevert (v1 v2) "HA".
    by iApply (ec_ind_amp _ k); auto.
  Qed.


  Lemma refines_couple_exp (M N p : nat ) (f : list nat → nat)
    (Hdom : ∀ l : list nat, Forall (λ x : nat, x < S N) l → f l < S M)
    (Hinj: forall (l1 l2:list nat),
        Forall (λ x, (x < S N)%nat) l1 ->
        Forall (λ x, (x < S N)%nat) l2 ->
        length l1 = p -> length l2 = p -> f l1 = f l2 -> l1 = l2) ns nsₛ α αₛ e1 e2 E A :
    (S N ^ p = S M)%nat->
    ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗
      (∀ (l : list nat) (m: nat),
          ⌜Forall (λ x : nat, x < S N) l⌝ -∗ ⌜m < S M⌝ -∗
          ⌜length l = p /\ f l = m⌝ -∗
          α ↪N (N; ns ++ l) -∗ αₛ ↪ₛN (M; nsₛ ++ [m]) -∗
              REL e1 << e2 @ E : A
      )
      ⊢ REL e1 << e2 @ E : A.
  Proof.
    iIntros (HExp) "[>Hα [>Hαs Hcont]]".
    rewrite refines_eq /refines_def.
    iIntros (K ε) "Hfill Hown Herr %Hpos".
    wp_apply (wp_couple_exp M N p f Hdom Hinj ns nsₛ α αₛ); eauto. iFrame.
    iIntros (l m) "%Hfa %HmM (%Hlm & %Heq) Hα Hαs".
    iApply ("Hcont" with "[//] [//] [//] Hα Hαs Hfill Hown Herr").
    done.
  Qed.


  Lemma refines_couple_exp_decoder (M N p : nat) ns nss α αs e1 e2 E A :
    (S N ^ p = S M)%nat ->
    ▷ α ↪N (N; ns) ∗ ▷ αs ↪ₛN (M; nss) ∗
      (∀ (l : list nat) (m: nat),
          ⌜Forall (λ x, (x < S N)%nat) l⌝ -∗
          ⌜(m < S M)%nat ⌝ -∗
          ⌜length l = p⌝ -∗
          α ↪N (N; ns ++ l) -∗ αs ↪ₛN (M; nss ++ [@decoder_nat N l]) -∗
          REL e1 << e2 @ E : A
      )
      ⊢ REL e1 << e2 @ E : A.
  Proof.
    iIntros (HExp) "[>Hα [>Hαs Hcont]]".
    rewrite refines_eq /refines_def.
    iIntros (K ε) "Hfill Hown Herr %Hpos".
    wp_apply (wp_couple_exp_decoder M N p ns nss α αs); eauto. iFrame.
    iIntros (l m) "% % % Hα Hαs".
    iApply ("Hcont" with "[//][//][//] Hα Hαs Hfill Hown Herr").
    done.
  Qed.

  Lemma refines_couple_exp_decoder_lr (M N p : nat) ns nss α αs e1 e2 E A :
    (S N ^ p = S M)%nat ->
    ▷ α ↪N (N; ns) ∗ ▷ αs ↪ₛN (M; nss) ∗
      (∀ (l : list nat) (m: nat),
          ⌜Forall (λ x, (x < S N)%nat) l⌝ -∗
          ⌜(m < S M)%nat ⌝ -∗
          ⌜length l = p⌝ -∗
          α ↪N (N; ns ++ l) -∗ αs ↪ₛN (M; nss ++ [@decoder_nat_lr N l]) -∗
          REL e1 << e2 @ E : A
      )
      ⊢ REL e1 << e2 @ E : A.
  Proof.
    iIntros (HExp) "[>Hα [>Hαs Hcont]]".
    rewrite refines_eq /refines_def.
    iIntros (K ε) "Hfill Hown Herr %Hpos".
    wp_apply (wp_couple_exp_decoder_lr M N p ns nss α αs); eauto. iFrame.
    iIntros (l m) "% % % Hα Hαs".
    iApply ("Hcont" with "[//][//][//] Hα Hαs Hfill Hown Herr").
    done.
  Qed.


    (** TODO: Strengthen Hinj hypothesis *)
    Lemma refines_couple_exp_rev (M N p : nat)
      (f:(list nat) -> nat)
      (Hdom : ∀ l : list nat, Forall (λ x : nat, x < S N) l → f l < S M)
      (Hinj: ∀ (l1 l2 : list nat),
        Forall (λ x, (x < S N)%nat) l1 ->
        Forall (λ x, (x < S N)%nat) l2 ->
        length l1 = p → length l2 = p → f l1 = f l2 → l1 = l2) ns nsₛ α αₛ e1 e2 E A:
      (S N ^ p = S M)%nat ->
      ▷ α ↪N (M; ns) ∗ ▷ αₛ ↪ₛN (N; nsₛ) ∗
        (∀ (l : list nat) (m: nat),
            ⌜Forall (λ x : nat, x < S N) l⌝ -∗ ⌜m < S M⌝ -∗
            ⌜length l = p /\ f l = m⌝ -∗
            α ↪N (M; ns ++ [m]) -∗ αₛ ↪ₛN (N; nsₛ ++ l) -∗
            REL e1 << e2 @ E : A
      )
      ⊢ REL e1 << e2 @ E : A.
  Proof.
    iIntros (HExp) "[>Hα [>Hαs Hcont]]".
    rewrite refines_eq /refines_def.
    iIntros (K ε) "Hfill Hown Herr %Hpos".
    wp_apply (wp_couple_exp_rev M N p f Hdom Hinj ns nsₛ α αₛ); eauto. iFrame.
    iIntros (l m) "%Hfa %HmM %Hlm Hα Hαs".
    iApply ("Hcont" with "[//] [//] [//] Hα Hαs Hfill Hown Herr").
    done.
  Qed.

  Lemma refines_couple_couple_avoid (N:nat) l z E K K' A:
    NoDup l ->
    TCEq N (Z.to_nat z) →
    ↯ (length l / (S N)) ∗
    ▷ (∀ (n : fin (S N)), ⌜n ∉ l⌝ -∗ REL fill K (Val #n) << fill K' (Val #n) @ E : A)
    ⊢ REL fill K (rand #z) << fill K' (rand #z) @ E : A.
  Proof.
    iIntros (Hl ->) "[Hε HΦ]".
    rewrite refines_eq/refines_def.
    iIntros (? ε) "Hfill Hown Herr %Hpos".
    wp_apply wp_bind.
    rewrite -fill_app.
    rewrite S_INR.
    iApply (wp_couple_rand_rand_avoid with "[$]"); first done.
    iIntros "!>" (n) "[% Hspec]".
    rewrite fill_app.
    by iApply ("HΦ" with "[][$][$][$]").
  Qed.
    

  Lemma refines_couple_exp_decoder_rev (M N p : nat) ns nss α αs e1 e2 E A :
    (S N ^ p = S M)%nat ->
    ▷ α ↪N (M; ns) ∗ ▷ αs ↪ₛN (N; nss) ∗
      (∀ (l : list nat) (m: nat),
          ⌜Forall (λ x, (x < S N)%nat) l⌝ -∗
          ⌜(m < S M)%nat ⌝ -∗
          ⌜length l = p⌝ -∗
          α ↪N (M; ns ++ [@decoder_nat N l]) -∗ αs ↪ₛN (N; nss ++ l) -∗
          REL e1 << e2 @ E : A
      )
      ⊢ REL e1 << e2 @ E : A.
  Proof.
    iIntros (HExp) "[>Hα [>Hαs Hcont]]".
    rewrite refines_eq /refines_def.
    iIntros (K ε) "Hfill Hown Herr %Hpos".
    wp_apply (wp_couple_exp_decoder_rev M N p ns nss α αs); eauto. iFrame.
    iIntros (l m) "% % % Hα Hαs".
    iApply ("Hcont" with "[//][//][//] Hα Hαs Hfill Hown Herr").
    done.
  Qed.


  Lemma refines_couple_exp_decoder_lr_rev (M N p : nat) ns nss α αs e1 e2 E A :
    (S N ^ p = S M)%nat ->
    ▷ α ↪N (M; ns) ∗ ▷ αs ↪ₛN (N; nss) ∗
      (∀ (l : list nat) (m: nat),
          ⌜Forall (λ x, (x < S N)%nat) l⌝ -∗
          ⌜(m < S M)%nat ⌝ -∗
          ⌜length l = p⌝ -∗
          α ↪N (M; ns ++ [@decoder_nat_lr N l]) -∗ αs ↪ₛN (N; nss ++ l) -∗
          REL e1 << e2 @ E : A
      )
      ⊢ REL e1 << e2 @ E : A.
  Proof.
    iIntros (HExp) "[>Hα [>Hαs Hcont]]".
    rewrite refines_eq /refines_def.
    iIntros (K ε) "Hfill Hown Herr %Hpos".
    wp_apply (wp_couple_exp_decoder_lr_rev M N p ns nss α αs); eauto. iFrame.
    iIntros (l m) "% % % Hα Hαs".
    iApply ("Hcont" with "[//][//][//] Hα Hαs Hfill Hown Herr").
    done.
  Qed.

 (*
  TODO: Port other rules by need

  Lemma refines_couple_TU N f `{Bij (fin (S N)) (fin (S N)) f} K' E α A z ns e :
    TCEq N (Z.to_nat z) →
    to_val e = None →
    ▷ α ↪ (N; ns) ∗
      (∀ (n : fin (S N)), α ↪ (N; ns ++ [n]) -∗ REL e << fill K' (Val #(f n)) @ E : A)
    ⊢ REL e << fill K' (rand #z) @ E : A.
  Proof.
    iIntros (-> ?) "[>Hα Hcnt]".
    rewrite {2}refines_eq {1}/refines_def.
    iIntros (K2) "[#Hs Hspec] Hnais /=".
    wp_apply wp_couple_tape_rand; [done|done|].
    rewrite -fill_app.
    (* [iFrame] is too aggressive.... *)
    iFrame "Hs Hα Hspec".
    iIntros (n) "[Hα [_ Hspec]]".
    rewrite fill_app.
    rewrite refines_eq /refines_def /refines_right.
    iSpecialize ("Hcnt" with "Hα [$Hs $Hspec] Hnais").
    wp_apply (wp_mono with "Hcnt").
    iIntros (v) "[% ([? ?] &?&?)]". iExists _. iFrame.
  Qed.
  Definition refines_couple_tape_rand := refines_couple_TU.

  Lemma refines_couple_UT N f `{Bij (fin (S N)) (fin (S N)) f} K E α A z ns e :
    TCEq N (Z.to_nat z) →
    ▷ α ↪ₛ (N; ns) ∗
      ▷ (∀ (n : fin (S N)), α ↪ₛ (N; ns ++ [f n]) -∗ REL fill K (Val #n) << e @ E : A)
    ⊢ REL fill K (rand #z) << e @ E : A.
  Proof.
    iIntros (->) "[H Hcnt]"
    rewrite refines_eq /refines_def.
    iIntros (K2) "[#Hs Hspec] Hnais /=".
    wp_apply wp_bind.
    wp_apply wp_couple_rand_tape; [done|].
    iFrame "Hs Hα".
    iIntros "!>" (b) "Hα".
    iSpecialize ("Hcnt" with "Hα [$Hs $Hspec] Hnais").
    wp_apply (wp_mono with "Hcnt").
    iIntros (v) "[% ([? ?] &?&?)]".
    iExists _. iFrame.
  Qed.
  Definition refines_couple_rand_tape := refines_couple_UT.

  Corollary refines_couple_TU_empty N f `{Bij (fin (S N)) (fin (S N)) f} K K' E α A z :
    TCEq N (Z.to_nat z) →
    ▷ α ↪ (N; []) ∗
      ▷ (∀ (n : fin (S N)), α ↪ (N; []) -∗ REL fill K (Val #n) << fill K' (Val #(f n)) @ E : A)
    ⊢ REL fill K (rand(#lbl:α) #z) << fill K' (rand #z) @ E : A.
  Proof.
    iIntros (->) "(>α & H)".
    iApply refines_couple_tape_rand.
    { rewrite fill_not_val //. }
    iFrame => /=. iIntros (n) "Hα".
    iApply refines_rand_l.
    iFrame. iModIntro. iApply "H".
  Qed.
  Definition refines_couple_rands_l := refines_couple_TU_empty.

  Corollary refines_couple_UT_empty N f `{Bij (fin (S N)) (fin (S N)) f} K K' E α A z :
    TCEq N (Z.to_nat z) →
    ▷ α ↪ₛ (N; []) ∗
      ▷ (∀ (n : fin (S N)), α ↪ₛ (N; []) -∗ REL fill K (Val #n) << fill K' (Val #(f n)) @ E : A)
    ⊢ REL fill K (rand #z) << fill K' (rand(#lbl:α) #z) @ E : A.
  Proof.
    iIntros (->) "(>Hα & H)".
    iApply refines_couple_rand_tape.
    iFrame.
    iIntros "!>" (n) "Hα".
    iApply (refines_rand_r with "Hα").
    iIntros "α".
    by iApply "H".
  Qed.
  Definition refines_couple_rands_r := refines_couple_UT_empty.


*)

End rules.
