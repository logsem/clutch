(** Generic sensitivity / differential-privacy Hoare rules for the generic DP
    logic.  Ported from [clutch.diffpriv.diffpriv_rules]; the DISTRIBUTION-
    SPECIFIC lemmas (the Laplace mechanism [hoare_laplace_diffpriv] and its
    composition corollaries) have been moved to the reusable [lib.laplace]
    library — this file is distribution-agnostic and only threads the signature
    [Sg] through the generic sensitivity/DP combinators. *)
From clutch.prob Require Import differential_privacy.
From clutch.gen_prob_lang Require Import inject.
From clutch.gen_prob_lang Require Export notation tactics metatheory lang.
From clutch.gen_prob_lang.spec Require Export spec_rules spec_tactics.
From clutch.diffpriv Require Export weakestpre lifting ectx_lifting.
From clutch.gen_diffpriv Require Export distance primitive_laws coupling_rules proofmode.

#[local] Open Scope R.

(* ------------------------------------------------------------------ *)
(* The group-bound additive credit [grp].                              *)
(*                                                                     *)
(* For a base rate [eps] and a group/distance [c], the exact           *)
(* "group privacy" amplification of the additive [δ] is the geometric  *)
(* factor                                                              *)
(*                                                                     *)
(*     grp eps c = (exp (c·eps) − 1) / (exp eps − 1).                  *)
(*                                                                     *)
(* This is the EXACT group-bound for the additive term: it matches the *)
(* boundary mass [δ_A_s = δ₁ · grp eps s] of the truncated Laplace     *)
(* coupling (see [prob/trunc_laplace.v], [tlap_delta]), where          *)
(* [δ₁ = exp(−eps·A)/Z_A].  It satisfies:                              *)
(*   - [grp eps 1 = 1]            (no amplification at distance 1);    *)
(*   - [grp eps c · grp (c·eps) c' = grp eps (c·c')]  (the group-      *)
(*     composition law that powers the SENSITIVITY composition below). *)
(*                                                                     *)
(* NOTE.  Because [grp] is super-linear in [c] for [c > 1] and         *)
(* sub-linear for [c < 1], the metric DP definition built on it does   *)
(* NOT enjoy monotonicity / sequential / parallel composition for      *)
(* general distances with [δ > 0] (those laws are FALSE and not        *)
(* provided).  The single law that survives is sensitivity-pre-        *)
(* composition, which threads [c] through the multiplicative AND       *)
(* additive credits via [grp_comp].                                    *)
(* ------------------------------------------------------------------ *)

(* [grp] and its facts ([grp_nonneg]/[grp_1]/[grp_comp]) now live (shared) in
   [clutch.prob.differential_privacy] alongside the meta-level [diffpriv_metric],
   imported above. *)

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


  (* ---------------------------------------------------------------- *)
  (* GROUP-BOUND METRIC approximate DP.                                *)
  (*                                                                   *)
  (* These are THE differential-privacy definitions in this library.   *)
  (* At distance [c], a program satisfies [(eps,del)]-DP iff it        *)
  (* consumes [↯m (c·eps)] multiplicative credit AND                   *)
  (* [↯ (del · grp eps c)] additive credit.  Because [grp eps 1 = 1], *)
  (* at adjacency (c = 1) this is exactly the [(eps, del)] profile.   *)
  (* For [c > 1] it is the textbook group-privacy amplification: the   *)
  (* additive term grows by the exact geometric factor [grp eps c =    *)
  (* (exp(c·eps)−1)/(exp(eps)−1)].  This is the correct bound for     *)
  (* the truncated-Laplace coupling (see [grp_comp] in                 *)
  (* [prob.differential_privacy]).                                     *)
  (* ---------------------------------------------------------------- *)

  Definition wp_diffpriv_metric (f : expr) eps del `(dA : Distance A) B `{Inject B val} : iProp Σ :=
    ∀ K c (x x' : A), ⌜dA x x' <= c⌝ →
    ⤇ fill K (f (Val (inject x'))) ∗ ↯m (c * eps) ∗ ↯ (del * grp eps c) -∗
      WP f (Val (inject x)) {{ v, ∃ (y : B), ⌜v = inject y⌝ ∗ ⤇ fill K (Val (inject y)) }}.
  #[global] Arguments wp_diffpriv_metric (_)%_E (_ _)%_R  _ _ _ _ %_stdpp.

  Definition hoare_diffpriv_metric (f : expr) eps del `(dA : Distance A) B `{Inject B val} : iProp Σ :=
    ∀ K c (x x' : A), ⌜dA x x' <= c⌝ -∗
      {{{ ⤇ fill K (f (Val (inject x'))) ∗ ↯m (c * eps) ∗ ↯ (del * grp eps c) }}}
        f (Val (inject x))
      {{{ (y : B), RET (inject y); ⤇ fill K (Val (inject y)) }}}.
  #[global] Arguments hoare_diffpriv_metric _%_E (_ _)%_R  _ _  _ _ %_stdpp.


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


  (* The ONE composition law that survives for the group-bound metric form:    *)
  (* pre-composition with a [c]-SENSITIVE map.  At input distance [c'], [f]      *)
  (* maps to output distance [c·c']; the metric privacy of [g] at distance      *)
  (* [c·c'] demands [↯m ((c·c')·eps)] and [↯ (del · grp eps (c·c'))].  The       *)
  (* supplied credits [↯m (c'·((c·eps)))] and [↯ ((del·grp eps c) · grp (c·eps) c')] *)
  (* rearrange into exactly that: the multiplicative one by associativity        *)
  (* ([Rmult_comm]/[Rmult_assoc], as in the linear proof), and the additive one  *)
  (* by the group-composition identity [grp_comp]:                               *)
  (*    (del · grp eps c) · grp (c·eps) c' = del · grp eps (c·c').               *)
  (* (Monotonicity / sequential / parallel composition are NOT provided — they   *)
  (*  are FALSE for [c < 1] with [δ > 0].)                                        *)
  Fact diffpriv_metric_sensitive_comp (f g : val) eps del c
    `(dA : Distance A) `(dB : Distance B) {C : Type} `{Inject C val}
    (Heps : 0 < eps) (c_pos : 0 < c) :
    hoare_sensitive f c dA dB -∗
    hoare_diffpriv_metric g eps del dB B -∗
    hoare_diffpriv_metric (λ:"x", g (f "x")) (c*eps) (del * grp eps c) dA B.
  Proof.
    rewrite /hoare_sensitive/hoare_diffpriv_metric.
    iIntros "#f_sens #g_dipr". iIntros (K c' adj x' Hadj).
    iIntros (Φ) "!> [f' [ε δ]] hΦ".
    wp_pures. wp_bind (f _). tp_pures. tp_bind (f _).
    iApply ("f_sens" $! _ _ _ _ _ with "[$f']") => //.
    iIntros "!>" (_v) "(%v & %v' & -> & gv' & %sens)".
    iApply ("g_dipr" $! K (c * c') _ _ _ with "[$gv' ε δ]").
    { (* rearrange multiplicative [c'·(c·eps) = (c·c')·eps] and additive          *)
      (* [(del·grp eps c)·grp (c·eps) c' = del·grp eps (c·c')] credits.           *)
      iSplitL "ε".
      - rewrite (Rmult_comm c c') Rmult_assoc. iFrame.
      - rewrite -(grp_comp eps c c') // -Rmult_assoc. iFrame. }
    Unshelve.
    (* three remaining goals: the postcondition continuation (discharged by      *)
    (* [hΦ]), the [0 <= c] premise of [f_sens], and the distance side-condition  *)
    (* [dB (f x) (f x') <= c·c'] from [c]-sensitivity composed with [adj].        *)
    - iApply "hΦ".
    - lra.
    - etrans; [exact sens|]. apply Rmult_le_compat_l; lra.
  Qed.

  (* OPEN / wp_apply-friendly form of the sensitivity∘DP composition.            *)
  (*                                                                             *)
  (* A Texan triple about the BARE composite [g (f (inject x))] with the input   *)
  (* [x] META-quantified — NO reified [(λ:"x", g (f "x"))] for [wp_pures] to     *)
  (* compute away.  Apply it at a program site of the shape [g (f ds)] (e.g.     *)
  (* [Laplace #num #den (query ds) #()]) directly with [wp_apply].  The credit   *)
  (* profile is the composite's [(c·eps, del)] metric cost at input distance     *)
  (* [c']: [↯m ((c·c')·eps)] and [↯ (del · grp eps (c·c'))] (the additive term   *)
  (* already in its [grp_comp]-collapsed form, so the credits frame directly).   *)
  Fact diffpriv_metric_sensitive_comp_at (f g : expr) eps del c
    `(dA : Distance A) `(dB : Distance B) {C : Type} `{Inject C val}
    (Heps : 0 < eps) (c_pos : 0 < c)
    K c' (x x' : A) (Hadj : dA x x' <= c') :
    hoare_sensitive f c dA dB -∗
    hoare_diffpriv_metric g eps del dB C -∗
      {{{ ⤇ fill K (g (f (Val (inject x')))) ∗ ↯m ((c*c') * eps) ∗ ↯ (del * grp eps (c*c')) }}}
        g (f (Val (inject x)))
      {{{ (y : C), RET (inject y); ⤇ fill K (Val (inject y)) }}}.
  Proof.
    rewrite /hoare_sensitive/hoare_diffpriv_metric.
    iIntros "#f_sens #g_dipr" (Φ) "!> (Hrhs & ε & δ) hΦ".
    wp_bind (f _). tp_bind (f _).
    iApply ("f_sens" $! _ _ _ _ _ with "[$Hrhs]") => //.
    iIntros "!>" (vf) "(%v & %v' & -> & gv' & %sens)".
    iApply ("g_dipr" $! K (c * c') v v' _ with "[$gv' $ε $δ]").
    - iApply "hΦ".
    Unshelve.
    + lra.
    + etrans; [exact sens|]. apply Rmult_le_compat_l; lra.
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* OPEN / wp_apply-friendly composition laws.                              *)
  (*                                                                         *)
  (* All three below are Texan triples about the BARE composite program with *)
  (* the input META-quantified ([∀ K c x x']) — NO reified [(λ:"x", …)] for  *)
  (* [wp_pures] to compute away.  This is the difference that makes them      *)
  (* [wp_apply]-able at a real program site (the reified laws above were not). *)
  (* ---------------------------------------------------------------------- *)

  (* (2) POST-PROCESSING (open form).                                        *)
  (*                                                                         *)
  (* If [f] is [(eps,del)]-DP releasing a [C], and [g] is a DETERMINISTIC    *)
  (* continuation that refines itself (couples its single spec run to its    *)
  (* single impl run, output-equal), then [g ∘ f] is [(eps,del)]-DP — the    *)
  (* budget is UNCHANGED.  This is the law that absorbs a deterministic       *)
  (* middle/tail of a pipeline into the preceding release.  Apply by          *)
  (* [wp_bind]-ing the head [f (inject x)], coupling its release [y] with     *)
  (* [f]'s DP, then running [g] on both sides via its self-refinement.        *)
  Fact diffpriv_metric_postprocess_at (f g : expr) eps del
    `(dA : Distance A) {C : Type} `{Inject C val} {D : Type} `{Inject D val}
    K c (x x' : A) (Hadj : dA x x' <= c) :
    hoare_diffpriv_metric f eps del dA C -∗
    □ (∀ (y : C) K, ⤇ fill K (g (Val (inject y))) -∗
        WP g (Val (inject y)) {{ v, ∃ z : D, ⌜v = inject z⌝ ∗ ⤇ fill K (Val (inject z)) }}) -∗
      {{{ ⤇ fill K (g (f (Val (inject x')))) ∗ ↯m (c * eps) ∗ ↯ (del * grp eps c) }}}
        g (f (Val (inject x)))
      {{{ (z : D), RET (inject z); ⤇ fill K (Val (inject z)) }}}.
  Proof.
    rewrite /hoare_diffpriv_metric.
    iIntros "#f_dipr #Hg_det" (Φ) "!> (Hrhs & ε & δ) hΦ".
    wp_bind (f _). tp_bind (f _).
    iApply ("f_dipr" $! _ c x x' Hadj with "[$Hrhs $ε $δ]").
    iIntros "!>" (y) "gv'".
    iApply (wp_wand with "[gv']").
    { iApply ("Hg_det" with "gv'"). }
    iIntros (vv) "(%z & -> & Hspec)".
    iApply "hΦ". iFrame.
  Qed.

  (* (3) DP-SEQ (binary, ADAPTIVE; open form).                               *)
  (*                                                                         *)
  (* The adaptive sequential composition of two releases.  [f] is a DP        *)
  (* release of a [B]; for every released value [b], the CONTINUATION [g b]   *)
  (* (which may also use the original input [x]) is a DP release of a [C].    *)
  (* The composite [g (f (inject x)) (inject x)] — the bare let-body          *)
  (* [let: "y" := f (inject x) in g "y" (inject x)] after the head is bound — *)
  (* is [(εf+εg, δf+δg)]-DP at adjacency.  Apply by [wp_bind]-ing the head    *)
  (* [f (inject x)], coupling [y], then the continuation [g y (inject x)].    *)
  (* (Open analogue of [diffpriv_metric_seq_comp_full].)                      *)
  Theorem diffpriv_metric_seq_comp_at (f g : expr) εf δf εg δg
    `(dA : Distance A) {B : Type} `{Inject B val} {C : Type} `{Inject C val}
    (dA_nat : ∀ x y, ∃ n : nat, dA x y = INR n)
    (εf_pos : 0 < εf) (εg_pos : 0 < εg) (δf_pos : 0 <= δf) (δg_pos : 0 <= δg)
    K c (a a' : A) (adj : dA a a' <= c) :
    hoare_diffpriv_metric f εf δf dA B -∗
    (∀ b : B, hoare_diffpriv_metric (g (Val (inject b))) εg δg dA C) -∗
      {{{ ⤇ fill K (g (f (Val (inject a'))) (Val (inject a'))) ∗
            ↯m (c * (εf + εg)) ∗ ↯ ((δf + δg) * grp (εf + εg) c) }}}
        g (f (Val (inject a))) (Val (inject a))
      {{{ (y : C), RET (inject y); ⤇ fill K (Val (inject y)) }}}.
  Proof.
    rewrite /hoare_diffpriv_metric.
    iIntros "#f_dipr #g_dipr" (Φ) "!> (gfa' & ε & δ) HΦ".
    destruct (dA_nat a a') as [n Hn].
    assert (Hnc : INR n <= c) by (rewrite -Hn; exact adj).
    assert (Hn0 : 0 <= INR n) by apply pos_INR.
    assert (Hsum_pos : 0 < εf + εg) by lra.
    (* Split the multiplicative credit *)
    replace (c * (εf + εg)) with
      ((INR n * εf) + ((INR n * εg) +
        (c * (εf + εg) - INR n * εf - INR n * εg))) by lra.
    iDestruct (ecm_split with "ε") as "[εf_n εg_slack]".
    { apply Rmult_le_pos; lra. }
    { nra. }
    iDestruct (ecm_split with "εg_slack") as "[εg_n _εslack]".
    { apply Rmult_le_pos; lra. }
    { nra. }
    (* Prove the δ slack is nonneg *)
    assert (Hδ_le : δf * grp εf (INR n) + δg * grp εg (INR n) <=
                    (δf + δg) * grp (εf + εg) c).
    {
      have Hf_eps : grp εf (INR n) <= grp (εf + εg) (INR n) by (apply grp_mono_eps; lra).
      have Hg_eps : grp εg (INR n) <= grp (εf + εg) (INR n) by (apply grp_mono_eps; lra).
      have Hfg_c : grp (εf + εg) (INR n) <= grp (εf + εg) c by (apply grp_mono_c; lra).
      have Hf_nn : 0 <= grp εf (INR n) by (apply grp_nonneg; lra).
      have Hg_nn : 0 <= grp εg (INR n) by (apply grp_nonneg; lra).
      nra.
    }
    (* Split the additive credit *)
    replace ((δf + δg) * grp (εf + εg) c) with
      ((δf * grp εf (INR n)) + ((δg * grp εg (INR n)) +
        ((δf + δg) * grp (εf + εg) c -
          δf * grp εf (INR n) - δg * grp εg (INR n)))) by lra.
    iDestruct (ec_split with "δ") as "[δf_n δg_slack]".
    { apply Rmult_le_pos; [lra | apply grp_nonneg; lra]. }
    { have Hg_nn2 : 0 <= δg * grp εg (INR n) by (apply Rmult_le_pos; [lra | apply grp_nonneg; lra]). lra. }
    iDestruct (ec_split with "δg_slack") as "[δg_n _δslack]".
    { apply Rmult_le_pos; [lra | apply grp_nonneg; lra]. }
    { have Hg_nn3 : 0 <= δg * grp εg (INR n) by (apply Rmult_le_pos; [lra | apply grp_nonneg; lra]). lra. }
    wp_bind (f _). tp_bind (f _).
    iApply ("f_dipr" $! _ (INR n) a a' with "[%] [$gfa' εf_n δf_n]").
    { rewrite Hn. lra. }
    - iFrame.
    - iIntros "!>" (b) "gb" => /=.
      iApply ("g_dipr" $! _ _ (INR n) a a' with "[%] [$gb εg_n δg_n]").
      + rewrite Hn. lra.
      + iFrame.
      + iIntros "!>" (y) "gy". iApply "HΦ". iFrame.
  Qed.

  (* (4) SENS∘SENS (open form).                                              *)
  (*                                                                         *)
  (* Composition of two SENSITIVE queries: [f] is [cf]-sensitive and [g] is   *)
  (* [cg]-sensitive, so the composite [g (f (inject x))] is [cg·cf]-sensitive. *)
  (* Open analogue of [sensitive_comp]; same wp_apply-friendly bare-program    *)
  (* shape as the laws above (here as a [wp_sensitive] / WP statement, since   *)
  (* sensitivity is naturally a single WP about the bare composite).          *)
  Fact wp_sensitive_comp_at (f g : expr) cg cf
    `(dA : Distance A) `(dB : Distance B) {C : Type} `(dC : Distance C)
    (cf_pos : 0 <= cf) (cg_pos : 0 <= cg) :
    hoare_sensitive f cf dA dB -∗
    hoare_sensitive g cg dB dC -∗
    ∀ K (x x' : A),
      ⤇ fill K (g (f (Val (inject x')))) -∗
      WP g (f (Val (inject x)))
        {{ v, ∃ z z' : C, ⌜v = inject z⌝ ∧ ⤇ fill K (Val (inject z'))
                          ∧ ⌜dC z z' <= (cg * cf) * dA x x'⌝ }}.
  Proof.
    rewrite /hoare_sensitive. iIntros "#f_sens #g_sens" (K x x') "Hrhs".
    wp_bind (f _). tp_bind (f _).
    iApply ("f_sens" $! cf_pos _ x x' with "[$Hrhs]").
    iIntros "!>" (vf) "(%v & %v' & -> & gv' & %sens)".
    iApply ("g_sens" $! cg_pos _ v v' with "[$gv']").
    iIntros "!>" (vg) "(%z & %z' & -> & vv' & %sens')".
    iExists z, z'. iFrame. iPureIntro. split; [done|].
    etrans; [exact sens'|].
    rewrite Rmult_assoc. apply Rmult_le_compat_l; [done|exact sens].
  Qed.


  Theorem diffpriv_metric_seq_comp_full (f g : val) εf δf εg δg
    `(dA : Distance A) `{Inject B val} {C : Type} `{Inject C val}
    (dA_nat : ∀ x y, ∃ n : nat, dA x y = INR n)
    (εf_pos : 0 < εf) (εg_pos : 0 < εg) (δf_pos : 0 <= δf) (δg_pos : 0 <= δg) :
    hoare_diffpriv_metric f εf δf dA A -∗
    (∀ b, hoare_diffpriv_metric (g b) εg δg dA C) -∗
    hoare_diffpriv_metric (λ:"a", g (f "a") "a") (εf + εg) (δf + δg) dA C.
  Proof.
    rewrite /hoare_diffpriv_metric.
    iIntros "#f_dipr #g_dipr" (K c a a' adj Φ) "!> [gfa' [ε δ]] HΦ".
    destruct (dA_nat a a') as [n Hn].
    assert (Hnc : INR n <= c) by (rewrite -Hn; exact adj).
    assert (Hn0 : 0 <= INR n) by apply pos_INR.
    assert (Hsum_pos : 0 < εf + εg) by lra.
    (* Split the multiplicative credit *)
    replace (c * (εf + εg)) with
      ((INR n * εf) + ((INR n * εg) +
        (c * (εf + εg) - INR n * εf - INR n * εg))) by lra.
    iDestruct (ecm_split with "ε") as "[εf_n εg_slack]".
    { apply Rmult_le_pos; lra. }
    { nra. }
    iDestruct (ecm_split with "εg_slack") as "[εg_n _εslack]".
    { apply Rmult_le_pos; lra. }
    { nra. }
    (* Prove the δ slack is nonneg *)
    assert (Hδ_le : δf * grp εf (INR n) + δg * grp εg (INR n) <=
                    (δf + δg) * grp (εf + εg) c).
    {
      have Hf_eps : grp εf (INR n) <= grp (εf + εg) (INR n).
      { apply grp_mono_eps; lra. }
      have Hg_eps : grp εg (INR n) <= grp (εf + εg) (INR n).
      { apply grp_mono_eps; lra. }
      have Hfg_c : grp (εf + εg) (INR n) <= grp (εf + εg) c.
      { apply grp_mono_c; lra. }
      have Hf_nn : 0 <= grp εf (INR n).
      { apply grp_nonneg; lra. }
      have Hg_nn : 0 <= grp εg (INR n).
      { apply grp_nonneg; lra. }
      nra.
    }
    (* Split the additive credit *)
    replace ((δf + δg) * grp (εf + εg) c) with
      ((δf * grp εf (INR n)) + ((δg * grp εg (INR n)) +
        ((δf + δg) * grp (εf + εg) c -
          δf * grp εf (INR n) - δg * grp εg (INR n)))) by lra.
    iDestruct (ec_split with "δ") as "[δf_n δg_slack]".
    { apply Rmult_le_pos; [lra | apply grp_nonneg; lra]. }
    { have Hg_nn2 : 0 <= δg * grp εg (INR n).
      { apply Rmult_le_pos; [lra | apply grp_nonneg; lra]. }
      lra. }
    iDestruct (ec_split with "δg_slack") as "[δg_n _δslack]".
    { apply Rmult_le_pos; [lra | apply grp_nonneg; lra]. }
    { have Hg_nn3 : 0 <= δg * grp εg (INR n).
      { apply Rmult_le_pos; [lra | apply grp_nonneg; lra]. }
      lra. }

    tp_pures ; wp_pures.
    tp_bind (f _). wp_bind (f _).
    iApply ("f_dipr" $! _ (INR n) a a' with "[%] [$gfa' εf_n δf_n]").
    { rewrite Hn. lra. }
    - iFrame.
    - iIntros "!>" (b) "gb" => /=.
      iApply ("g_dipr" $! _ _ (INR n) a a' with "[%] [$gb εg_n δg_n]").
      + rewrite Hn. lra.
      + iFrame.
      + iIntros "!>" (y) "gy". iApply "HΦ". iFrame.
  Qed.


  Lemma Rdiv_pos_den_0 x y (div_pos : 0 < x/y) : ¬ y = 0.
  Proof.
    intro d0. rewrite d0 in div_pos. rewrite Rdiv_0_r in div_pos. lra.
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
