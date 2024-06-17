(** Core relational rules *)
From stdpp Require Import coPset namespaces.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import list.
From clutch.common Require Import language ectx_language ectxi_language.
From clutch.prob_lang Require Import locations notation lang.
From clutch.prob_lang.spec Require Import spec_ra spec_rules spec_tactics.
From clutch.paris Require Import ectx_lifting app_weakestpre model.
From clutch.paris Require Export proofmode primitive_laws coupling_rules.
From clutch.base_logic Require Export spec_update.

Section rules.
  Context `{!parisRGS Σ}.
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
    (∀ α : loc, α ↪ₛ (N; []) -∗ REL t << fill K (of_val #lbl:α) @ E : A)%I
    ⊢ REL t << fill K (alloc #z) @ E : A.
  Proof.
    iIntros (->) "Hlog".
    iApply refines_step_r.
    iIntros (K') "HK'".
    tp_alloctape as α "Hα".
    iModIntro. iExists _. iFrame. by iApply "Hlog".
  Qed.

  Lemma refines_randT_r E K α N z n ns t A :
    TCEq N (Z.to_nat z) →
    α ↪ₛ (N; n :: ns)
    ⊢ (α ↪ₛ (N; ns) -∗ REL t << fill K (of_val #n) @ E : A)
    -∗ REL t << (fill K (rand(#lbl:α) #z)) @ E : A.
  Proof.
    iIntros (->) "Hα Hlog".
    iApply refines_step_r.
    iIntros (k) "Hk".
    tp_rand.
    iModIntro. iExists _. iFrame. by iApply "Hlog".
  Qed.
  Definition refines_rand_r := refines_randT_r.

  Lemma refines_randT_empty_r K E α A N z e :
    TCEq N (Z.to_nat z) →
    ▷ α ↪ₛ (N; []) ∗
      (∀ n : fin (S N), α ↪ₛ (N; []) -∗ REL e << fill K (Val #n) @ E : A)
    ⊢ REL e << fill K (rand(#lbl:α) #z) @ E : A.
  Proof.
    iIntros (->) "[>Hα H]".
    rewrite refines_eq /refines_def.
    iIntros (K2 ε) "Hspec Hnais Herr Hpos /=".
    wp_apply wp_rand_empty_r.
    rewrite -fill_app.
    iFrame "Hα Hspec".
    iIntros (N) "(Hα & Hb)".
    rewrite /= fill_app.
    iSpecialize ("H" with "Hα [$Hb] Hnais Herr Hpos").
    wp_apply (wp_mono with "H").
    iIntros (?) "[% [% ?]]".
    iExists _, _. iFrame.
  Qed.
  Definition refines_rand_empty_r := refines_randT_empty_r.

  Lemma refines_randU_r E K e (N : nat) (z : Z) A :
    TCEq N (Z.to_nat z) →
    (∀ (n : fin (S N)), REL e << fill K (Val #n) @ E : A)
      ⊢ REL e << fill K (rand #z) @ E : A.
  Proof.
    iIntros (?) "H".
    rewrite refines_eq /refines_def.
    iIntros (K2 ε) "Hspec Hnais Herr Hpos /=".
    rewrite -fill_app. wp_apply (wp_rand_r _ _ _ _ (K++K2)) => //.
    iSplitL "Hspec"; [iFrame |].
    iIntros (n) "Hspec" => /=. rewrite fill_app.
    iApply ("H" with "[$Hspec] Hnais Herr Hpos").
  Qed.

  (** This rule is useful for proving that functions refine each other *)
  Lemma refines_arrow_val (v v' : val) A A' :
    □(∀ v1 v2, A v1 v2 -∗
      REL App v (of_val v1) << App v' (of_val v2) : A') ⊢
    REL (of_val v) << (of_val v') : (A → A')%lrel.
  Proof.
    iIntros "#H".
    iApply refines_ret. iModIntro.
    iExists (2%NNR).
    iSplit; [iPureIntro; simpl; lra |].
    iModIntro.
    iIntros (v1 v2 ε) "#HInd Herr HA".
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
    (▷ (∀ α : loc, α ↪ (N; []) -∗ REL fill K (of_val #lbl:α) << t @ E : A))%I
    ⊢ REL fill K (alloc #z) << t @ E : A.
  Proof.
    iIntros (->) "Hlog".
    iApply refines_wp_l.
    by wp_apply (wp_alloc_tape with "[//]").
  Qed.

  Lemma refines_randT_l E K α N z n ns t A :
    TCEq N (Z.to_nat z) →
    (▷ α ↪ (N; n :: ns) ∗
     ▷ (α ↪ (N; ns) -∗ REL fill K (of_val #n) << t @ E : A))
    ⊢ REL fill K (rand(#lbl:α) #z) << t @ E : A.
  Proof.
    iIntros (->) "[Hα Hlog]".
    iApply refines_wp_l.
    by wp_apply (wp_rand_tape with "Hα").
  Qed.
  Definition refines_rand_l := refines_randT_l.

  Lemma refines_randT_empty_l K E α A N z e :
    TCEq N (Z.to_nat z) →
    ▷ α ↪ (N; []) ∗
      ▷ (∀ (n : fin (S N)), α ↪ (N; []) -∗ REL fill K (Val #n) << e @ E : A)
    ⊢ REL fill K (rand(#lbl:α) #z) << e @ E : A.
  Proof.
    iIntros (->) "[>Hα H]".
    rewrite refines_eq /refines_def.
    iIntros (K2 ε) "Hspec Hnais Herr Hpos /=".
    wp_apply wp_bind.
    wp_apply (wp_rand_tape_empty with "Hα").
    iIntros (n) "Hα /=".
    iApply ("H" with "Hα [$Hspec] Hnais Herr Hpos").
  Qed.
  Definition refines_rand_empty_l := refines_randT_empty_l.

  Lemma refines_randU_l E K e (N : nat) (z : Z) A :
    TCEq N (Z.to_nat z) →
    (∀ (n : fin (S N)), REL fill K (Val #n) << e @ E : A)
      ⊢ REL fill K (rand #z) << e @ E : A.
  Proof.
    iIntros (?) "H".
    rewrite refines_eq /refines_def.
    iIntros (K2 ε) "Hspec Hnais Herr Hpos /=".
    wp_apply wp_bind. wp_apply wp_rand => //.
    iIntros (n) "_" => /=.
    iApply ("H" with "[$Hspec] Hnais Herr Hpos").
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

  Lemma refines_couple_TT_err (N M : nat) E e1 e2 A α αₛ ns nsₛ (ε : nonnegreal) :
    (N <= M)%R →
    (((S M - S N) / S M) = ε)%R →
    (▷ α ↪ (N; ns) ∗ ▷ αₛ ↪ₛ (M; nsₛ) ∗ ↯ ε ∗
    (∀ (n : fin (S N)) (m : fin (S M)),
        ⌜(fin_to_nat n = m)⌝ -∗ α ↪ (N; ns ++ [n]) ∗ αₛ ↪ₛ (M; nsₛ ++ [m]) -∗
        REL e1 << e2 @ E : A))
    ⊢ REL e1 << e2 @ E : A.
  Proof.
    iIntros (Hleq Heq) "(Hα & Hαs & Herr & Hlog)".
    rewrite refines_eq /refines_def.
    iIntros (K2 ε') "He2 Hnais Herr' Hpos/=".
    wp_apply (wp_couple_tapes N M);
      [done|done|].
    iFrame.
    iIntros (n m) "H [Hα Hαs]".
    iApply ("Hlog" with "[$H] [$Hα $Hαs] [$He2] Hnais Herr' Hpos").
  Qed.
  Definition refines_couple_tapes := refines_couple_TT_err.

  Lemma refines_couple_TT_frag {M N} (f : fin(S M) → fin (S N)) {_ : Inj (=) (=) f} E e1 e2 A α αₛ ns nsₛ :
    (M <= N)%R →
    ▷ α ↪ (N; ns) ∗ ▷ αₛ ↪ₛ (M; nsₛ) ∗
    (∀ (n : fin (S N)),
       if bool_decide(∃ m, f m = n) then
         ∀ m,
       α ↪ (N; ns ++ [n]) ∗ αₛ ↪ₛ (M; nsₛ ++ [m]) ∗ ⌜f m = n⌝ -∗
         REL e1 << e2 @ E : A
     else
       α ↪ (N; ns ++ [n]) ∗ αₛ ↪ₛ (M; nsₛ) -∗
         REL e1 << e2 @ E : A
    )
    ⊢ REL e1 << e2 @ E : A.
  Proof.
    iIntros (Hleq) "(Hα & Hαs & Hlog)".
    rewrite refines_eq /refines_def.
    iIntros (K2 ε') "He2 Hnais Herr' Hpos/=".
    wp_apply wp_couple_fragmented_rand_rand_inj; [done|].
    iFrame.
    iIntros (n).
    iSpecialize ("Hlog" $! n).
    case_bool_decide.
    - iIntros (m) "(Hα & Hαs & Hnm)".
      iApply ("Hlog" with "[$Hα $Hαs $Hnm] [$He2] Hnais Herr' Hpos").
    - iIntros "(Hα & Hαs)".
      iApply ("Hlog" with "[$Hα $Hαs] [$He2] Hnais Herr' Hpos").
  Qed.

  Lemma refines_couple_TT_adv {M N} (f : fin(S N) → fin (S M)) {_ : Inj (=) (=) f} E e1 e2 A α αₛ ns nsₛ ε :
    (N < M)%R →
    ▷ α ↪ (N; ns) ∗ ▷ αₛ ↪ₛ (M; nsₛ) ∗ ↯ ε ∗
      (∀ (m : fin (S M)),
          if bool_decide (∃ n, f n = m) then
            ∀ n, α ↪ (N; ns ++ [n]) ∗ αₛ ↪ₛ (M; nsₛ ++ [m]) ∗ ⌜f n = m⌝ -∗
                 REL e1 << e2 @ E : A
          else
            ∀ (ε':nonnegreal),
              ⌜(nonneg ε' = (S M) / (S M - S N) * ε)%R⌝ ∗
              α ↪ (N; ns) ∗ αₛ ↪ₛ (M; nsₛ ++ [m]) ∗ ↯ ε' -∗
              REL e1 << e2 @ E : A)
      ⊢ REL e1 << e2 @ E : A.
  Proof.
    iIntros (Hleq) "(Hα & Hαs & Herr & Hlog)".
    rewrite refines_eq /refines_def.
    iIntros (K2 ε') "He2 Hnais Herr' Hpos/=".
    wp_apply wp_couple_fragmented_rand_rand_inj_rev'; [done|].
    iFrame "Hα Hαs Herr".
    iIntros (m).
    iSpecialize ("Hlog" $! m).
    case_bool_decide.
    - iIntros (n) "(Hα & Hαs & Hnm)".
      iApply ("Hlog" with "[$Hα $Hαs $Hnm] [$He2] Hnais Herr' Hpos").
    - iIntros (ε'0) "(%Herr2 & Hα & Hαs & Herr'0)".
      iApply ("Hlog" $! ε'0 with "[$Hα $Hαs $Herr'0] [$He2] Hnais [$Herr'] Hpos").
      iPureIntro.
      done.
  Qed.

  Lemma refines_get_ec E e e' A :
    (∀ ε : nonnegreal, ↯ ε -∗ ⌜ (0 < ε)%R ⌝ -∗ REL e << e' @ E : A) ⊢
    (REL e << e' @ E : A).
  Proof.
    iIntros "H".
    rewrite refines_eq /refines_def.
    iIntros (K ε) "Hfill Hown Herr %Hpos".
    replace (ε) with (nnreal_div ε (nnreal_nat 2) + nnreal_div ε (nnreal_nat 2))%NNR;
      last first.
    { apply nnreal_ext.
      simpl. lra.
    }
    iPoseProof (ec_split with "Herr") as "[Herr1 Herr2]".
    iApply ("H" with "Herr1 [] Hfill Hown Herr2").
    - iPureIntro. simpl. lra.
    - iPureIntro. simpl. lra.
  Qed.


  Lemma refines_ind_amp E e e' A (k : nonnegreal) :
    (1 < k)%R ->
    □ (∀ (ε : nonnegreal),
          ⌜ (0 < ε)%R ⌝ -∗ □ (↯ ((k * ε)%NNR) -∗ (REL e << e' @ E : A))
               -∗ ↯ ε -∗ (REL e << e' @ E : A))%I
      ⊢ REL e << e' @ E : A.
  Proof.
    intros Hk.
    iIntros "#IH".
    iApply refines_get_ec.
    iIntros (ε) "Herr %Hpos".
    iApply (ec_ind_amp _ k with "[IH] Herr"); auto.
  Qed.


  (** Threading the error through recursive functions *)
  Lemma refines_arrow_val_err (v v' : val) A A' (k : nonnegreal) :
    (1 < k)%R ->
    □ (∀ (ε : nonnegreal),
        □ ( ↯ ((k * ε)%NNR) -∗ ∀ v3 v4, A v3 v4 -∗ REL App v (of_val v3) << App v' (of_val v4) : A') -∗
        ↯ ε -∗
          ∀ v1 v2, A v1 v2 -∗ REL App v (of_val v1) << App v' (of_val v2) : A')
    ⊢ REL (of_val v) << (of_val v') : (A → A')%lrel.
  Proof.
    iIntros (Hk) "#H".
    iApply refines_ret. iModIntro.
    iExists (k).
    iSplit; [done |].
    iModIntro.
    iIntros (v1 v2 ε) "#HInd Herr #HA".
    iApply ("H" with "[] Herr HA").
    iModIntro.
    iIntros "Herr".
    by iApply "HInd".
  Qed.



  Lemma refines_couple_UU N f `{Bij (fin (S N)) (fin (S N)) f} K K' E A z :
    TCEq N (Z.to_nat z) →
    ▷ (∀ (n : fin (S N)), REL fill K (Val #n) << fill K' (Val #(f n)) @ E : A)
    ⊢ REL fill K (rand #z) << fill K' (rand #z) @ E : A.
  Proof.
    iIntros (->) "Hcnt".
    rewrite refines_eq /refines_def.
    iIntros (K2 ε) "Hfill Hown Herr %Hpos".
    wp_apply wp_bind.
    rewrite -fill_app.
    iApply (wp_couple_rand_rand with "Hfill").
    iIntros "!>" (n) "Hspec".
    rewrite fill_app.
    iSpecialize ("Hcnt" with "Hspec Hown").
    iApply ("Hcnt" with "Herr"); done.
  Qed.

  Definition refines_couple_rands_lr := refines_couple_UU.

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
