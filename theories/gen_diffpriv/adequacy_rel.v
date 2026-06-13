(** Relational adequacy (generic DP, [gen_prob_lang]).

    Ported from [diffpriv/adequacy_rel].  Threads the distribution signature
    [Sg] explicitly (as the [gen_adequacy] corollaries do) and pins
    [lim_exec]/[DPcoupl] to [lang_markov (gen_lang Sg)]. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import na_invariants.
From clutch.gen_diffpriv Require Import primitive_laws.
From clutch.diffpriv Require Import weakestpre.
From clutch.gen_diffpriv Require Import model adequacy.
From clutch.gen_prob_lang Require Import lang.

Class diffprivRGpreS Σ := DiffprivRGPreS {
  diffprivRGpreS_diffpriv :: diffprivGpreS Σ;
  prelorelGpreS_na_inv :: na_invG Σ;
}.

Definition diffprivRΣ : gFunctors := #[diffprivΣ; na_invΣ].
Global Instance subG_diffprivRGPreS {Σ} : subG diffprivRΣ Σ → diffprivRGpreS Σ.
Proof. solve_inG. Qed.

Theorem approximates_coupling (Sg : Sig) Σ `{diffprivRGpreS Σ}
  (A : ∀ `{diffprivRGS Sg Σ}, lrel Σ) (φ : val → val → Prop) e e' σ σ' ε δ :
  (0 <= ε)%R →
  (0 <= δ)%R →
  (∀ `{diffprivRGS Sg Σ}, ∀ v v', A v v' -∗ ⌜φ v v'⌝) →
  (∀ `{diffprivRGS Sg Σ}, ↯m ε ∗ ↯ δ ⊢ REL e << e' : A) →
  DPcoupl (lim_exec (δ := lang_markov (gen_lang Sg)) (e, σ))
          (lim_exec (δ := lang_markov (gen_lang Sg)) (e', σ')) φ ε δ.
Proof.
  intros Hε Hδ HA Hlog.
  eapply (wp_adequacy_error_lim Sg Σ); [done|done|].
  intros H0 δ' Hpos.
  iIntros "He' Hε Hδ".
  iMod na_alloc as "[%γ Htok]".
  set (HclutchR := DiffprivRGS Sg Σ _ _ γ).
  iPoseProof (Hlog _) as "Hlog".
  iDestruct ((ec_split_le δ δ') with "Hδ") as "[δ δ']" ; [real_solver|].
  iSpecialize ("Hlog" with "[$Hε $δ]").
  rewrite refines_eq /refines_def.
  assert (0 < δ' - δ)%R by real_solver.
  iSpecialize ("Hlog" $! [] (δ' - δ)%R with "He' Htok δ' [//]").
  iApply (wp_mono with "Hlog").
  iIntros (?) "H /=".
  iDestruct "H" as (??) "(? & ? & ? & ? & ?) /=".
  iExists _. iFrame. by iApply HA.
Qed.

Corollary refines_coupling (Sg : Sig) Σ `{diffprivRGpreS Σ}
  (A : ∀ `{diffprivRGS Sg Σ}, lrel Σ) (φ : val → val → Prop) e e' σ σ' :
  (∀ `{diffprivRGS Sg Σ}, ∀ v v', A v v' -∗ ⌜φ v v'⌝) →
  (∀ `{diffprivRGS Sg Σ}, ⊢ REL e << e' : A) →
  DPcoupl (lim_exec (δ := lang_markov (gen_lang Sg)) (e, σ))
          (lim_exec (δ := lang_markov (gen_lang Sg)) (e', σ')) φ 0 0.
Proof.
  intros ? Hlog. intros. eapply approximates_coupling ; eauto. 1,2: lra.
  iIntros.
  iApply Hlog.
Qed.
