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

  Definition hoare_diffpriv (f : expr) ε δ `(dA : Distance A) : iProp Σ := ∀ K c (x x' : A), ⌜dA x x' <= c⌝ →
      {{{ ⤇ fill K (f (Val (inject x'))) ∗ ↯m (c * ε) ∗ ↯ (c * δ) }}}
        f (Val (inject x))
      {{{ (v : val), RET v; ⤇ fill K (Val v) }}}.

  Fact hoare_laplace_diffpriv (num den : Z) :
    ⌜0 < IZR num / IZR den⌝ -∗
    hoare_diffpriv (λ: "loc", Laplace #num #den "loc")%E ((IZR num / IZR den)) 0 dZ.
  Proof.
    iIntros. rewrite /hoare_diffpriv/dZ /=. iIntros (K c x x' adj).
    iIntros (φ) "!> [f' [ε δ]] hφ".
    tp_pures. wp_pures.
    tp_bind (Laplace _ _ _).
    iApply (wp_couple_laplace _ _ 0%Z with "[$f' ε]") => //.
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
    iIntros "!>" (?) "(%b & %v' & -> & gv' & %sens)".
    iApply ("g_dipr" $! K (c * c') _ _ _ with "[$gv' ε δ]").
    { rewrite (Rmult_comm c c') 2!Rmult_assoc. iFrame. }
    Unshelve. 1-2: done.
    etrans => //. apply Rmult_le_compat_l => //.
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


End diffpriv.
