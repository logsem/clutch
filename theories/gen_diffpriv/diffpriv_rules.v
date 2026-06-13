(** Generic sensitivity / differential-privacy Hoare rules for the generic DP
    logic.  Ported from [clutch.diffpriv.diffpriv_rules]; the DISTRIBUTION-
    SPECIFIC lemmas (the Laplace mechanism [hoare_laplace_diffpriv] and its
    composition corollaries) have been moved to the reusable [lib.laplace]
    library — this file is distribution-agnostic and only threads the signature
    [Sg] through the generic sensitivity/DP combinators. *)
From clutch.gen_prob_lang Require Import inject.
From clutch.gen_prob_lang Require Export notation tactics metatheory lang.
From clutch.gen_prob_lang.spec Require Export spec_rules spec_tactics.
From clutch.diffpriv Require Export weakestpre lifting ectx_lifting.
From clutch.gen_diffpriv Require Export distance primitive_laws coupling_rules proofmode.

#[local] Open Scope R.

Section diffpriv.
  Context (Sg : Sig).
  Canonical Structure gen_ectxi_lang_dpr := gen_ectxi_lang Sg.
  Canonical Structure gen_ectx_lang_dpr := gen_ectx_lang Sg.
  Canonical Structure gen_lang_dpr := gen_lang Sg.
  Context `{!diffprivGS Sg Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).

  Definition wp_sensitive (f : expr) (c : R) `(d_in : Distance A) `(d_out : Distance B) : iProp Σ
    :=
    ∀ (c_pos : 0 <= c) K (x x' : A),
    ⤇ fill K (f $ Val $ inject x') -∗
    WP
      f $ Val $ inject x
      {{ v,
           ∃ b b' : B, ⌜v = inject b⌝ ∧ ⤇ fill K (Val (inject b'))
                      ∧ ⌜d_out b b' <= c * d_in x x'⌝
      }}.

  Definition hoare_sensitive (f : expr) (c : R) `(d_in : Distance A) `(d_out : Distance B) : iProp Σ
    :=
    ∀ (c_pos : 0 <= c) K (x x' : A),
    {{{ ⤇ fill K (f $ Val $ inject x') }}}
      f $ Val $ inject x
      {{{ (v : val), RET (v);
          ∃ b b' : B, ⌜v = inject b⌝ ∧ ⤇ fill K (Val (inject b'))
                      ∧ ⌜d_out b b' <= c * d_in x x'⌝
      }}}.

  Definition wp_diffpriv (f : expr) ε δ `(dA : Distance A) B `{Inject B val} : iProp Σ :=
    ∀ K c (x x' : A), ⌜dA x x' <= c⌝ →
    ⤇ fill K (f (Val (inject x'))) ∗ ↯m (c * ε) ∗ ↯(c * δ) -∗
      WP f (Val (inject x)) {{ v, ∃ (y : B), ⌜v = inject y⌝ ∗ ⤇ fill K (Val (inject y)) }}.
  #[global] Arguments wp_diffpriv (_)%_E (_ _)%_R  _ _ _ _ %_stdpp.

  (* this is what's called internally (ε,δ)-dp in the paper *)
  (* classic (ε,δ)-diffpriv; strict version w/o equivalence *)
  Definition hoare_diffpriv_classic (f : expr) ε δ `(dA : Distance A) B `{Inject B val} : iProp Σ :=
    ∀ K (x x' : A), ⌜dA x x' <= 1⌝ -∗
      {{{ ⤇ fill K (f (Val (inject x'))) ∗ ↯m ε ∗ ↯ δ }}}
        f (Val (inject x))
      {{{ (y : B), RET (inject y); ⤇ fill K (Val (inject y)) }}}.

  (* built in rescaling ~ group privacy *)
  Definition hoare_diffpriv (f : expr) ε δ `(dA : Distance A) B `{Inject B val} : iProp Σ :=
    ∀ K c (x x' : A), ⌜dA x x' <= c⌝ -∗
      {{{ ⤇ fill K (f (Val (inject x'))) ∗ ↯m (c * ε) ∗ ↯ (c * δ) }}}
        f (Val (inject x))
      {{{ (y : B), RET (inject y); ⤇ fill K (Val (inject y)) }}}.
  #[global] Arguments hoare_diffpriv _%_E (_ _)%_R  _ _  _ _ %_stdpp.

  Lemma wp_diffpriv_mono (f : expr) ε δ ε' δ' `(dA : Distance A) `{Inject B val}
    (ε_pos : 0 <= ε) (hε' : ε <= ε')
    (δ_pos : 0 <= δ) (hδ' : δ <= δ') :
    wp_diffpriv f ε δ dA B -∗
    wp_diffpriv f ε' δ' dA B.
  Proof.
    iIntros "fεδ" (?? a a' ?) "[rhs [ε δ]]".
    pose proof (distance_pos a a').
    iApply ("fεδ" with "[] [$rhs ε δ]") => //.
    iSplitL "ε".
    - iApply (ecm_weaken with "[$ε]"). real_solver.
    - iApply (ec_weaken with "[$δ]"). real_solver.
  Qed.

  Lemma wp_sensitive_mono (f : expr) c c' `(dA : Distance A) `(dB : Distance B)
    (c_pos : 0 <= c) (hc' : c <= c') :
    wp_sensitive f c dA dB -∗
    wp_sensitive f c' dA dB.
  Proof.
    iIntros "fsens" (?? a a') "rhs". rewrite /wp_sensitive.
    pose proof (distance_pos a a').
    iSpecialize ("fsens" $! c_pos K a a' with "rhs").
    iApply (wp_mono with "fsens").
    iIntros "% (% & % & % & rhs & %)".
    iExists _,_. iFrame. iPureIntro. intuition eauto.
    etrans. 1: eassumption. real_solver.
  Qed.

  Fact sensitive_comp (f g : val) cg cf
    `(dA : Distance A) `(dB : Distance B) {C : Type} `(dC : Distance C) (cf_pos : 0 <= cf) (cg_pos : 0 <= cg) :
    hoare_sensitive f cf dA dB -∗ hoare_sensitive g cg dB dC -∗ hoare_sensitive (λ:"x", g (f "x")) (cg * cf) dA dC.
  Proof.
    rewrite /hoare_sensitive. iIntros "#f_sens #g_sens". iIntros. iIntros (Φ). iIntros "!> f' hΦ".
    tp_pures. wp_pures. wp_bind (f _). tp_bind (f _).
    iApply ("f_sens" $! _ _ _ _ _ with "[$f']") => //.
    iIntros "!>" (vfx) "(%fx & %fx' & -> & gv' & %sens)".
    iApply ("g_sens" $! _ _ _ _ _ with "[$gv']") => //.
    iIntros "!>" (vgfx) "(%gfx & %gfx'' & -> & vv' & %sens')".
    iApply "hΦ". iExists _,_. iFrame. iPureIntro.
    split ; [eauto|].
    etrans => //.
    rewrite Rmult_assoc.
    eapply Rmult_le_compat_l => //.
    Unshelve. all: done.
  Qed.

  Fact diffpriv_sensitive_comp (f g : val) ε δ c
    `(dA : Distance A) `(dB : Distance B) {C : Type} `{Inject C val}
    (c_pos : 0 <= c) :
    hoare_sensitive f c dA dB -∗ hoare_diffpriv g ε δ dB B -∗ hoare_diffpriv (λ:"x", g (f "x")) (c*ε) (c*δ) dA B.
  Proof.
    rewrite /hoare_sensitive/hoare_diffpriv. iIntros "#f_sens #g_dipr". iIntros (K c'). iIntros. iIntros (Φ) "!> [f' [ε δ]] hΦ".
    wp_pures. wp_bind (f _). tp_pures. tp_bind (f _).
    iApply ("f_sens" $! _ _ _ _ _ with "[$f']") => //.
    iIntros "!>" (_v) "(%v & %v' & -> & gv' & %sens)".
    iApply ("g_dipr" $! K (c * c') _ _ _ with "[$gv' ε δ]").
    { rewrite (Rmult_comm c c') 2!Rmult_assoc. iFrame. }
    Unshelve.
    1-2 : done.
    etrans => //. apply Rmult_le_compat_l => //.
  Qed.

  Fact diffpriv_sensitive_strict_comp (f g : val) ε δ c
    `(dA : Distance A) `(dB : Distance B) {C : Type} `{Inject C val}
    (c_pos : 0 <= c) :
    hoare_sensitive f c dA dB -∗ hoare_diffpriv g ε δ dB C -∗ hoare_diffpriv (λ:"x", g (f "x")) (c*ε) (c*δ) dA C.
  Proof.
    rewrite /hoare_sensitive/hoare_diffpriv. iIntros "#f_sens #g_dipr". iIntros (K c'). iIntros. iIntros (Φ) "!> [f' [ε δ]] hΦ".
    wp_pures. wp_bind (f _). tp_pures. tp_bind (f _).
    iApply ("f_sens" $! _ _ _ _ _ with "[$f']") => //.
    iIntros "!>" (_v) "(%v & %v' & -> & gv' & %sens)".
    iApply ("g_dipr" $! K (c * c') _ _ _ with "[$gv' ε δ]").
    { rewrite (Rmult_comm c c') 2!Rmult_assoc. iFrame. }
    Unshelve.
    1-2 : done.
    etrans => //. apply Rmult_le_compat_l => //.
  Qed.

  Lemma Rdiv_pos_den_0 x y (div_pos : 0 < x/y) : ¬ y = 0.
  Proof.
    intro d0. rewrite d0 in div_pos. rewrite Rdiv_0_r in div_pos. lra.
  Qed.

  Definition hoare_functional_on `(dA : Distance A) B `{Inject B val} (f : expr) : iProp Σ := ∀ K (x : A) ,
    {{{ ⤇ fill K (f $ Val $ inject x) }}}
      f $ Val $ inject x
      {{{ (y : B), RET (inject y);  ⤇ fill K (Val (inject y)) }}}.
  #[global] Arguments hoare_functional_on _ _ _ _%_stdpp _%_E.

  Definition hoare_has_codomain (B : Type) `{Inject B val} (f : expr) : iProp Σ :=
    ∀ x P Q, {{{ P }}} f x {{{ v , RET v ; Q v }}} -∗ {{{ P }}} f x {{{ v , RET v ; ∃ b, ⌜ v = inject b ⌝ ∧ Q v }}}.

  Fact well_typed_diffpriv_comp (f g : val) ε δ c `(dA : Distance A) `(dB : Distance B)
    {C : Type} `(Inject C val) (c_pos : 0 <= c) :
    hoare_diffpriv f ε δ dA B -∗ hoare_has_codomain B f -∗
    hoare_functional_on dB C g -∗ hoare_diffpriv (λ:"x", g (f "x")) ε δ dA C.
  Proof.
    rewrite /hoare_sensitive/hoare_diffpriv. iIntros "#f_dipr f_cod #g_dom". iIntros (K c' ?? adj ?).
    iIntros "!> [g [ε δ]] hΦ".
    wp_pures. wp_bind (f _). tp_pures. tp_bind (f _).
    iApply ("f_dipr" with "[//] [f_dipr $g $ε $δ]").
    iIntros "!>" (y) "g".
    by iApply ("g_dom" with "g").
  Qed.

  Fact diffpriv_functional (f : val) ε δ `(dA : Distance A) `{Inject B val} :
    hoare_diffpriv f ε δ dA B -∗ hoare_functional_on dA B f.
  Proof.
    iIntros "#f_dipr" (K z z') "!> fz hΦ".
    iMod ecm_zero as "ε0".
    iMod ec_zero as "δ0".
    rewrite /hoare_diffpriv.
    unshelve iApply ("f_dipr" $! K 0 _ _ _ with "[$fz ε0 δ0]") => //.
    - right ; by apply distance_0.
    - rewrite 2!Rmult_0_l. iFrame.
  Qed.

  Corollary diffpriv_diffpriv_comp (f g : val) εf δf εg δg
    `(dA : Distance A) `(dB : Distance B) {C : Type} `{Inject C val}
    (εg_pos : 0 <= εg) (δg_pos : 0 <= δg) (εf_pos : 0 <= εf) (δf_pos : 0 <= δf) :
    hoare_has_codomain B f -∗ hoare_diffpriv f εf δf dA B -∗
    hoare_diffpriv g εg δg dB C -∗ hoare_diffpriv (λ:"x", g (f "x")) εf δf dA C.
  Proof.
    iIntros "f_cod #f_dipr #g_dipr". iIntros (???? h).
    iPoseProof (diffpriv_functional _ _ _ with "g_dipr") as "g_fun".
    iApply (well_typed_diffpriv_comp f g εf δf c dA dB _ with "f_dipr f_cod g_fun") => //.
    Unshelve. etrans. 2: apply h. apply distance_pos.
  Qed.

  (* variant of diffpriv_diffpriv_seq_comp assuming strict DP for f. *)
  Theorem diffpriv_strict_diffpriv_seq_comp (f g : val) εf δf εg δg
    `(dA : Distance A) `{Inject B val} {C : Type} `{Inject C val}
    (εg_pos : 0 <= εg) (δg_pos : 0 <= δg) (εf_pos : 0 <= εf) (δf_pos : 0 <= δf):
    hoare_diffpriv f εf δf dA A -∗
    (∀ b, hoare_diffpriv (g b) εg δg dA C) -∗
    hoare_diffpriv (λ:"a", g (f "a") "a") (εf+εg) (δf+δg) dA C.
  Proof.
    iIntros "#f_dipr #g_dipr" (?? a a' adj Φ) "!> [gfa' [ε δ]] HΦ".
    rewrite 2!Rmult_plus_distr_l.
    assert (0 <= c). { etrans. 2: eauto. apply distance_pos. }
    iDestruct (ecm_split with "ε") as "[εf εg]" => //. 1,2: real_solver.
    iDestruct (ec_split with "δ") as "[δf δg]" => //. 1,2: real_solver.
    tp_pures ; wp_pures.
    tp_bind (f _). wp_bind (f _).
    iApply ("f_dipr" $! _ _ _ _ _ with "[$gfa' $εf $δf]") => //.
    iIntros "!>" (b) "gb" => /=.
    iEval (rewrite /hoare_diffpriv) in "g_dipr".
    by wp_apply ("g_dipr" $! _ K c a a' adj with "[$gb $εg $δg]").
    Unshelve. auto.
  Qed.

  Theorem wp_diffpriv_diffpriv_par_comp (f g : val) ε δ
    `(dA : Distance A) `(dB : Distance B) {C : Type}
    `{Inject C val} `{Inject D val}
    (ε_pos : 0 <= ε) (δ_pos : 0 <= δ) :
    wp_diffpriv f ε δ dA C -∗
    wp_diffpriv g ε δ dB D -∗
    wp_diffpriv (λ:"xy", (f (Fst "xy"), g (Snd "xy"))) ε δ (dtensor dA dB) (C * D)%type.
  Proof.
    iIntros "f_dipr g_dipr" (?? [a b] [a' b'] adj) "[fa_gb' [ε δ]]".
    rewrite /dtensor in adj. simpl in adj.
    pose proof (distance_pos a a'). pose proof (distance_pos b b').
    iDestruct (ecm_weaken _ ((dA a a' + dB b b') * ε) with "ε") as "ε". 1: real_solver.
    rewrite Rmult_plus_distr_r. iDestruct (ecm_split with "ε") as "[εf εg]" => //. 1,2: real_solver.
    iDestruct (ec_weaken _ ((dA a a' + dB b b') * δ) with "δ") as "δ". 1: real_solver.
    rewrite Rmult_plus_distr_r. iDestruct (ec_split with "δ") as "[δf δg]" => //. 1,2: real_solver.
    tp_pures ; wp_pures. tp_bind (g _). wp_bind (g _).
    iApply (wp_strong_mono'' with "[g_dipr fa_gb' εg δg] [-]").
    1: iApply "g_dipr". 2: iFrame. 1: iPureIntro ; lra.
    iIntros (gb) "(%y & -> & rhs) /=". tp_pures. wp_pures.
    tp_bind (f _) ; wp_bind (f _).
    iApply (wp_strong_mono'' with "[f_dipr rhs εf δf] [-]").
    1: iApply "f_dipr". 2: iFrame. 1: iPureIntro ; lra.
    iIntros (fa) "(%z & -> & rhs) /=".
    tp_pures. wp_pures.
    iModIntro. iExists (_, _). iFrame.
    done.
  Qed.

  Theorem diffpriv_diffpriv_par_comp (f g : val) ε δ
    `(dA : Distance A) `(dB : Distance B) {C : Type}
    `{Inject C val} `{Inject D val}
    (ε_pos : 0 <= ε) (δ_pos : 0 <= δ) :
    hoare_diffpriv f ε δ dA C -∗
    hoare_diffpriv g ε δ dB D -∗
    hoare_diffpriv (λ:"xy", (f (Fst "xy"), g (Snd "xy"))) ε δ (dtensor dA dB) (C * D)%type.
  Proof.
    iIntros "#f_dipr #g_dipr" (?? [a b] [a' b'] adj Φ) "!> [fa_gb' [ε δ]] HΦ".
    rewrite /dtensor in adj. simpl in adj.
    pose proof (distance_pos a a'). pose proof (distance_pos b b').
    iDestruct (ecm_weaken _ ((dA a a' + dB b b') * ε) with "ε") as "ε". 1: real_solver.
    rewrite Rmult_plus_distr_r. iDestruct (ecm_split with "ε") as "[εf εg]" => //. 1,2: real_solver.
    iDestruct (ec_weaken _ ((dA a a' + dB b b') * δ) with "δ") as "δ". 1: real_solver.
    rewrite Rmult_plus_distr_r. iDestruct (ec_split with "δ") as "[δf δg]" => //. 1,2: real_solver.
    tp_pures ; wp_pures. tp_bind (g _). wp_bind (g _).
    iApply ("g_dipr" $! _ _ _ _ _ with "[$fa_gb' $εg $δg]") => //.
    iIntros "!>" (y) "fa_gb" => /=.
    tp_pures. wp_pures. tp_bind (f _). wp_bind (f _).
    iApply ("f_dipr" $! _ _ _ _ _ with "[$fa_gb $εf $δf]") => //.
    iIntros "!>" (z) "fa_gb" => /=.
    tp_pures. wp_pures. iApply ("HΦ" $! (_, _)). by iFrame.
    Unshelve. all: lra.
  Qed.

  Definition hoare_sensitive_Z (f : expr) (c : Z) `(d_in : Distance A) : iProp Σ
    :=
    ∀ (c_pos : (0 <= IZR c)) K (x x' : A) (C : Z) (h_in : d_in x x' <= IZR C),
      {{{ ⤇ fill K (f $ Val $ inject x') }}}
        f $ Val $ inject x
        {{{ (v : val), RET (v);
            ∃ b b' : Z, ⌜v = inject b⌝ ∧ ⤇ fill K (Val (inject b'))
                        ∧ ⌜- (c * C) <= b - b'⌝%Z
                        ∧ ⌜b - b' <= c * C⌝%Z

        }}}.

  Lemma hoare_sensitive_Z_bounded f (c : Z) `(d_in : Distance A) :
    hoare_sensitive f (IZR c) d_in dZ -∗ hoare_sensitive_Z f c d_in.
  Proof.
    iIntros "#h % * % !> rhs hk".
    iApply ("h" with "[] rhs") => //.
    iNext. iIntros "* h'". iApply "hk".
    iDestruct "h'" as "(%&%&->&rhs&%adj)".
    iExists _,_. iFrame. iPureIntro. split ; eauto.
    apply dZ_bounded_cases. rewrite mult_IZR.
    etrans ; real_solver.
  Qed.

End diffpriv.
