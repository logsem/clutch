From clutch.common Require Import inject.
From clutch.prob_lang Require Export notation tactics metatheory.
From clutch.prob_lang Require Export lang.
From clutch.prob_lang.spec Require Export spec_rules spec_tactics.
From clutch.diffpriv Require Export weakestpre lifting ectx_lifting primitive_laws coupling_rules proofmode.

Section diffpriv.
  Context `{!diffprivGS Σ}.

  #[local] Open Scope R.

  Class Distance A := { carrier :: Inject A val
                      ; distance : A -> A -> R
                      ; distance_pos a1 a2 : 0 <= distance a1 a2
                      ; distance_0 a : distance a a = 0
                      ; distance_sep a1 a2 : distance a1 a2 <= 0 -> a1 = a2
                      (* leaving out symmetry and triangle inequality until they're needed. *)
                      (* ; distance_sym a1 a2 : distance a1 a2 = distance a2 a1 *)
                      (* ; distance_triangle a1 a2 a3 : distance a1 a3 <= distance a1 a2 + distance a2 a3 *)
    }.
  Arguments carrier {_} _.
  Coercion carrier : Distance >-> Inject.
  Arguments distance {_} _ _ _.
  Coercion distance : Distance >-> Funclass.

  Program Definition dZ : Distance Z := {| distance z z' := Rabs (IZR (z - z')) |}.
  Next Obligation. intros => /= ; eauto using Rabs_pos. Qed.
  Next Obligation. intros => /= ; replace (a - a)%Z with 0%Z by lia. exact Rabs_R0. Qed.
  Next Obligation.
    intros ?? => /= ; rewrite -abs_IZR. pose proof (IZR_le _ _ $ Zabs_pos (a1-a2)).
    intros h. assert (IZR (Z.abs (a1 - a2)) = 0) as h' by lra. revert h'.
    apply Zabs_ind ; intros ? h' ; apply eq_IZR in h' ; lia.
  Qed.

  Program Definition dtensor `(dA : Distance A) `(dB : Distance B) : Distance (A * B) :=
    {| distance x y := let (x1, x2) := x in let (y1, y2) := y in dA x1 y1 + dB x2 y2 |}.
  Next Obligation. intros ???? [] []. apply Rplus_le_le_0_compat ; apply distance_pos. Qed.
  Next Obligation. intros ???? []. rewrite !distance_0. lra. Qed.
  Next Obligation.
    intros ???? [a b] [a' b'] ?.
    pose proof (distance_pos a a'). pose proof (distance_pos b b').
    assert (dA a a' <= 0) by lra. assert (dB b b' <= 0) by lra.
    pose proof (distance_sep a a'). pose proof (distance_sep b b').
    f_equal ; intuition auto.
  Qed.

  Definition wp_sensitive (f : expr) (c : R) `(d_in : Distance A) `(d_out : Distance B) : iProp Σ
    :=
    ∀ (c_pos : 0 <= c) K (x x' : A),
    ⤇ fill K (f $ Val $ inject x') -∗
    WP
      f $ Val $ inject x
      {{ v,
           ∃ b b' : B, ⌜v = inject b⌝ ∧ ⤇ fill K (inject b')
                      ∧ ⌜d_out b b' <= c * d_in x x'⌝
      }}.

  Definition hoare_sensitive (f : expr) (c : R) `(d_in : Distance A) `(d_out : Distance B) : iProp Σ
    :=
    ∀ (c_pos : 0 <= c) K (x x' : A),
    {{{ ⤇ fill K (f $ Val $ inject x') }}}
      f $ Val $ inject x
      {{{ (v : val), RET (v);
          ∃ b b' : B, ⌜v = inject b⌝ ∧ ⤇ fill K (inject b')
                      ∧ ⌜d_out b b' <= c * d_in x x'⌝
      }}}.

  Definition wp_diffpriv (f : expr) ε δ `(dA : Distance A) : iProp Σ := ∀ K c (x x' : A), ⌜dA x x' <= c⌝ →
    ⤇ fill K (f (Val (inject x'))) ∗ ↯m (c * ε) ∗ ↯(c * δ) -∗
      WP f (Val (inject x)) {{ v, ⤇ fill K (Val v) }}.

  Definition wp_diffpriv_pw (f : expr) ε δ `(dA : Distance A) : iProp Σ := ∀ K c (x x' : A), ⌜dA x x' <= c⌝ →
    ⤇ fill K (f (Val (inject x'))) ∗ ↯m (c * ε) ∗ ↯(c * δ) -∗
    ∀ r,
      WP f (Val (inject x)) {{ v, ∃ (v' : val), ⤇ fill K (Val v') ∗ ⌜v = r → v' = r⌝ }}.

  Definition hoare_diffpriv (f : expr) ε δ `(dA : Distance A) : iProp Σ := ∀ K c (x x' : A), ⌜dA x x' <= c⌝ →
      {{{ ⤇ fill K (f (Val (inject x'))) ∗ ↯m (c * ε) ∗ ↯ (c * δ) }}}
        f (Val (inject x))
      {{{ (v : val), RET v; ⤇ fill K (Val v) }}}.

  Lemma wp_diffpriv_mono (f : val) ε δ ε' δ' `(dA : Distance A)
    (ε_pos : 0 <= ε) (hε' : ε <= ε')
    (δ_pos : 0 <= δ) (hδ' : δ <= δ') :
    wp_diffpriv f ε δ dA -∗
    wp_diffpriv f ε' δ' dA.
  Proof.
    iIntros "fεδ" (?? a a' ?) "[rhs [ε δ]]".
    pose proof (distance_pos a a').
    iApply ("fεδ" with "[] [$rhs ε δ]") => //.
    iSplitL "ε".
    - iApply (ecm_weaken with "[$ε]"). real_solver.
    - iApply (ec_weaken with "[$δ]"). real_solver.
  Qed.

  Lemma wp_sensitive_mono (f : val) c c' `(dA : Distance A) `(dB : Distance B)
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

  Fact hoare_laplace_diffpriv (num den : Z) :
    ⌜0 < IZR num / IZR den⌝ -∗
    hoare_diffpriv (λ: "loc", Laplace #num #den "loc")%E ((IZR num / IZR den)) 0 dZ.
  Proof.
    iIntros. rewrite /hoare_diffpriv/dZ /=. iIntros (K c x x' adj).
    iIntros (φ) "!> [f' [ε δ]] hφ".
    tp_pures. wp_pures.
    tp_bind (Laplace _ _ _).
    iApply (hoare_couple_laplace _ _ 0%Z with "[$f' ε]") => //.
    2: setoid_rewrite Z.add_0_r ; iNext ; iIntros ; iApply "hφ" ; iFrame.
    iFrame. iApply ecm_weaken. 2: iFrame.
    split. all: rewrite abs_IZR ; real_solver_partial. 1: apply Rabs_pos.
    3: rewrite Z.add_0_l. all: lra.
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
    `(dA : Distance A) `(dB : Distance B) {C : Type} `(dC : Distance C)
    (c_pos : 0 <= c) :
    hoare_sensitive f c dA dB -∗ hoare_diffpriv g ε δ dB -∗ hoare_diffpriv (λ:"x", g (f "x")) (c*ε) (c*δ) dA.
  Proof.
    rewrite /hoare_sensitive/hoare_diffpriv. iIntros "#f_sens #g_dipr". iIntros (K c'). iIntros. iIntros (Φ) "!> [f' [ε δ]] hΦ".
    wp_pures. wp_bind (f _). tp_pures. tp_bind (f _).
    iApply ("f_sens" $! _ _ _ _ _ with "[$f']") => //.
    iIntros "!>" (_v) "(%v & %v' & -> & gv' & %sens)".
    iApply ("g_dipr" $! K (c * c') _ _ _ with "[$gv' ε δ]").
    { rewrite (Rmult_comm c c') 2!Rmult_assoc. iFrame. }
    Unshelve. 1-2: done.
    etrans => //. apply Rmult_le_compat_l => //.
  Qed.

  Fact diffpriv_pw_sensitive_comp (f g : val) ε δ c
    `(dA : Distance A) `(dB : Distance B) {C : Type} `(dC : Distance C)
    (c_pos : 0 <= c) :
    wp_sensitive f c dA dB -∗ wp_diffpriv_pw g ε δ dB -∗ wp_diffpriv_pw (λ:"x", g (f "x")) (c*ε) (c*δ) dA.
  Proof.
    rewrite /wp_sensitive/wp_diffpriv_pw. iIntros "f_sens g_dipr". iIntros (K c'). iIntros (??) "% [f' [ε δ]] %".
    wp_pures. wp_bind (f _). tp_pures. tp_bind (f _).
    iSpecialize ("f_sens" $! c_pos _ x x' with "f'").
    iApply (wp_strong_mono'' with "f_sens").
    iIntros "% (% & % & -> & gb' & %sens) /=".
    unshelve iApply ("g_dipr" $! _ (c * c') b b' _ with "[$gb' ε δ]").
    2:{ rewrite (Rmult_comm c c') 2!Rmult_assoc. iFrame. }
    etrans. 1: eauto. real_solver.
  Qed.

  Definition hoare_functional_on (A : Type) {_ : Inject A val} (f : expr) : iProp Σ := ∀ K (x : A) ,
    {{{ ⤇ fill K (f $ Val $ inject x) }}}
      f $ Val $ inject x
      {{{ (v : val), RET v; ⤇ fill K (Val v) }}}.

  Definition hoare_has_codomain (B : Type) {_ : Inject B val} (f : expr) : iProp Σ :=
    ∀ x P Q, {{{ P }}} f x {{{ v , RET v ; Q v }}} -∗ {{{ P }}} f x {{{ v , RET v ; ∃ b, ⌜ v = inject b ⌝ ∧ Q v }}}.

  Fact well_typed_diffpriv_comp (f g : val) ε δ c `(dA : Distance A) `(dB : Distance B) (c_pos : 0 <= c) :
    hoare_diffpriv f ε δ dA -∗ hoare_has_codomain B f -∗ hoare_functional_on B g -∗ hoare_diffpriv (λ:"x", g (f "x")) ε δ dA.
  Proof.
    rewrite /hoare_sensitive/hoare_diffpriv. iIntros "#f_dipr f_cod #g_dom". iIntros (K c' ?? adj ?).
    iSpecialize (("f_dipr" $! _ c' _ _ _)).
    iPoseProof ("f_cod" with "[$f_dipr]") as "#Hg".
    iIntros "!> [g [ε δ]] hΦ".
    wp_pures. wp_bind (f _). tp_pures. tp_bind (f _).
    iApply ("Hg" with "[$g ε δ]") => //; [iFrame|].
    iNext. iIntros (?) "(%gix & -> & f')".
    iApply ("g_dom" with "[$f']").
    iIntros "!>" (?) "gv'".
    iApply "hΦ". done.
    Unshelve. auto.
  Qed.

  Fact diffpriv_functional (f : val) ε δ `(dA : Distance A) :
    hoare_diffpriv f ε δ dA -∗ hoare_functional_on A f.
  Proof.
    iIntros "#f_dipr" (K z Φ) "!> fz hΦ".
    iMod ecm_zero as "ε0".
    iMod ec_zero as "δ0".
    rewrite /hoare_diffpriv.
    unshelve iApply ("f_dipr" $! K 0 _ _ _ with "[$fz ε0 δ0]") => //.
    - right ; apply distance_0.
    - rewrite 2!Rmult_0_l. iFrame.
  Qed.

  Fact sensitive_functional (f : val) c `(dA : Distance A) `(dB : Distance B) (c_pos : 0 <= c) :
    hoare_sensitive f c dA dB -∗ hoare_functional_on A f.
  Proof.
    iIntros "#f_sens" (K z Φ) "!> f' hΦ".
    rewrite /hoare_sensitive.
    iApply ("f_sens" $! c_pos K with "[$f']").
    iNext. iIntros (v) "(%b & %b' & -> & b' & %sens)".
    iApply "hΦ".
    assert (b = b') as -> => //.
    move: sens.
    rewrite distance_0. rewrite Rmult_0_r. apply distance_sep.
  Qed.

  Corollary diffpriv_diffpriv_comp (f g : val) εf δf εg δg
    `(dA : Distance A) `(dB : Distance B) {C : Type} `(dC : Distance C)
    (εg_pos : 0 <= εg) (δg_pos : 0 <= δg) (εf_pos : 0 <= εf) (δf_pos : 0 <= δf) :
    hoare_has_codomain B f -∗ hoare_diffpriv f εf δf dA -∗
    hoare_diffpriv g εg δg dB -∗ hoare_diffpriv (λ:"x", g (f "x")) εf δf dA.
  Proof.
    iIntros "f_cod #f_dipr #g_dipr". iIntros (???? h).
    iPoseProof (diffpriv_functional _ _ _ with "g_dipr") as "g_fun".
    iApply (well_typed_diffpriv_comp f g εf δf c dA dB _ with "f_dipr f_cod g_fun") => //.
    Unshelve. etrans. 2: apply h. apply distance_pos.
  Qed.

  Corollary sensitive_diffpriv_comp (g f : val) ε δ c (c_pos : 0 <= c)
    `(dA : Distance A) `(dB : Distance B) {C : Type} `(dC : Distance C) :
    hoare_diffpriv f ε δ dA -∗ hoare_has_codomain B f -∗
    hoare_sensitive g c dB dC -∗ hoare_diffpriv (λ:"x", g (f "x")) ε δ dA.
  Proof.
    iIntros "#f_dipr f_cod #g_sens".
    iPoseProof (sensitive_functional _ _ _ _ _ with "g_sens") as "g_fun" => //.
    iApply (well_typed_diffpriv_comp _ _ _ _ _ _ _ c_pos with "f_dipr f_cod g_fun").
    Unshelve. auto.
  Qed.

  (* The typing here is a bit weird with `f : A → B` and `g : B → A → C` ; it
  is stated like this because the assumption that g is diffpriv in A for all b
  has to refer to g's last argument, and reasoning about `λ a, g a b` is
  annoying. *)
  Theorem diffpriv_diffpriv_seq_comp (f g : val) εf δf εg δg
    `(dA : Distance A) `(dB : Distance B)
    (εg_pos : 0 <= εg) (δg_pos : 0 <= δg) (εf_pos : 0 <= εf) (δf_pos : 0 <= δf):
    hoare_diffpriv f εf δf dA -∗
    (∀ b, hoare_diffpriv (g b) εg δg dA) -∗
    hoare_diffpriv (λ:"a", g (f "a") "a") (εf+εg) (δf+δg) dA.
  Proof.
    iIntros "#f_dipr #g_dipr" (?? a a' adj Φ) "!> [gfa' [ε δ]] HΦ".
    rewrite 2!Rmult_plus_distr_l.
    assert (0 <= c). { etrans. 2: eauto. apply distance_pos. }
    iDestruct (ecm_split with "ε") as "[εf εg]" => //. 1,2: real_solver.
    iDestruct (ec_split with "δ") as "[δf δg]" => //. 1,2: real_solver.
    tp_pures ; wp_pures. tp_bind (f _). wp_bind (f _).
    iApply ("f_dipr" $! _ _ _ _ _ with "[$gfa' $εf $δf]") => // ; iIntros "!>" (b) "gb" => /=.
    iSpecialize ("g_dipr" $! b K c a a' adj with "[$gb $εg $δg]").
    iApply "g_dipr". done.
    Unshelve. auto.
  Qed.

  Theorem wp_diffpriv_diffpriv_par_comp (f g : val) ε δ
    `(dA : Distance A) `(dB : Distance B)
    (ε_pos : 0 <= ε) (δ_pos : 0 <= δ) :
    wp_diffpriv f ε δ dA -∗
    wp_diffpriv g ε δ dB -∗
    wp_diffpriv (λ:"xy", (f (Fst "xy"), g (Snd "xy"))) ε δ (dtensor dA dB).
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
    iIntros (gb) "rhs /=". tp_pures. wp_pures.
    tp_bind (f _) ; wp_bind (f _).
    iApply (wp_strong_mono'' with "[f_dipr rhs εf δf] [-]").
    1: iApply "f_dipr". 2: iFrame. 1: iPureIntro ; lra.
    iIntros (fa) "rhs /=". tp_pures. wp_pures.
    done.
  Qed.

  Theorem diffpriv_diffpriv_par_comp (f g : val) ε δ
    `(dA : Distance A) `(dB : Distance B)
    (ε_pos : 0 <= ε) (δ_pos : 0 <= δ) :
    hoare_diffpriv f ε δ dA -∗
    hoare_diffpriv g ε δ dB -∗
    hoare_diffpriv (λ:"xy", (f (Fst "xy"), g (Snd "xy"))) ε δ (dtensor dA dB).
  Proof.
    iIntros "#f_dipr #g_dipr" (?? [a b] [a' b'] adj Φ) "!> [fa_gb' [ε δ]] HΦ".
    rewrite /dtensor in adj. simpl in adj.
    pose proof (distance_pos a a'). pose proof (distance_pos b b').
    iDestruct (ecm_weaken _ ((dA a a' + dB b b') * ε) with "ε") as "ε". 1: real_solver.
    rewrite Rmult_plus_distr_r. iDestruct (ecm_split with "ε") as "[εf εg]" => //. 1,2: real_solver.
    iDestruct (ec_weaken _ ((dA a a' + dB b b') * δ) with "δ") as "δ". 1: real_solver.
    rewrite Rmult_plus_distr_r. iDestruct (ec_split with "δ") as "[δf δg]" => //. 1,2: real_solver.
    tp_pures ; wp_pures. tp_bind (g _). wp_bind (g _).
    iApply ("g_dipr" $! _ _ _ _ _ with "[$fa_gb' $εg $δg]") => // ; iIntros "!>" (gb) "fa_gb" => /=.
    tp_pures. wp_pures. tp_bind (f _). wp_bind (f _).
    iApply ("f_dipr" $! _ _ _ _ _ with "[$fa_gb $εf $δf]") => // ; iIntros "!>" (fa) "fa_gb" => /=.
    tp_pures. wp_pures. iApply "HΦ". done.
    Unshelve. all: lra.
  Qed.


End diffpriv.
