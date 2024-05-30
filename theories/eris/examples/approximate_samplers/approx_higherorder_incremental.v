(** * Higher order specification for incremental sampling algorithms *)
From clutch.eris Require Export eris error_rules.
From clutch.eris Require Export examples.approximate_samplers.approx_sampler_lib.
From Coquelicot Require Import Series.
Require Import Lra.

Section incremental_spec.
  Local Open Scope R.
  Context `{!erisGS Σ}.

  Definition incr_sampling_scheme_spec (sampler checker : val) (Ψ : nat -> iProp Σ) (ξ : nat -> nonnegreal) L iL E Θ : iProp Σ :=
    ( (* Either 0 credit or 0 progress => we will sample a value which the checker accepts
         Allowed to consume (or invalidate Ψ) in this process *)
      ((€ (ξ 0%nat) ∨ Ψ 0%nat) -∗ WP sampler #() @ E [{ fun s => WP checker (Val s) @ E [{fun v => ⌜v = #true⌝ ∗ Θ s }] }]) ∗
      (* Given any amount of credit and progress, we can get a sample such that... *)
     □ (∀ i p, (⌜((S p) <= L)%nat ⌝ ∗ ⌜(i <= iL)%nat ⌝ ∗ € (ξ (S i)) ∗ Ψ (S p)) -∗
            WP sampler #() @ E [{ fun s =>
                   (*...we're done by chance alone, or... *)
                  (WP checker (Val s) @ E [{fun v => ⌜v = #true⌝ ∗ (Θ s)}]) ∨
                   (*... we make prgress, and can run the checker on the sample without losing progress, or *)
                  (€ (ξ (S i)) ∗ WP checker (Val s) @ E [{fun v => ((⌜v = #false⌝ ∗ Ψ p) ∨ (⌜v = #true⌝ ∗ Θ s))}]) ∨
                   (*... we lose progress & amplify error, and can run the checker on the sample without losing progress. *)
                  (∃ p', ⌜(p' <= L)%nat ⌝ ∗ € (ξ i) ∗ WP checker (Val s) @ E [{fun v => ((⌜v = #false⌝ ∗ Ψ p') ∨ (⌜v = #true⌝ ∗ Θ s))}])}]))%I.


  Lemma ho_incremental_ubdd_approx_safe (sampler checker : val) Ψ ξ L E i iL p Θ :
    ⊢ ⌜(p <= L)%nat ⌝ ∗
      ⌜(i < iL)%nat ⌝ ∗
    incr_sampling_scheme_spec sampler checker Ψ ξ L iL E Θ ∗
    € (ξ i) ∗
    Ψ p -∗
    WP (gen_rejection_sampler sampler checker) @ E [{ fun v => Θ v }].
  Proof.
    rewrite /incr_sampling_scheme_spec.
    iIntros "(%Hl&%Hil&(Hfinal&#Hamp)&Hcr&HΨ)".
    rewrite /gen_rejection_sampler.
    do 7 wp_pure.
    iRevert (Hl).
    iInduction i as [|i'] "IHerror" forall (p).
    - (* base case for error credits *)
      iIntros "%Hl".
      wp_pures.
      wp_bind (sampler _).
      wp_apply (ub_twp_wand with "[Hfinal Hcr]"); first (iApply "Hfinal"; iFrame).
      iIntros (s) "Hcheck"; wp_pures.
      wp_apply (ub_twp_wand with "Hcheck").
      iIntros (v) "(-> & HΘ)"; wp_pures.
      eauto.
    - (* inductive case for error credits *)
      iIntros "%Hl".
      iInduction p as [|p'] "IHp".
      + (* base case for progress measure *)
        wp_pures.
        wp_bind (sampler _).
        wp_apply (ub_twp_wand with "[Hfinal HΨ]"); first (iApply "Hfinal"; iFrame).
        iIntros (s) "Hcheck"; wp_pures.
        wp_apply (ub_twp_wand with "Hcheck").
        iIntros (v) "(-> & HΘ)"; wp_pures.
        eauto.
      + (* Inductive case for progress measure *)
        wp_pures.
        wp_bind (sampler _).
        wp_apply (ub_twp_wand with "[Hamp Hcr HΨ]").
        {  iApply "Hamp". iFrame; eauto. iPureIntro; split; try lia. }
        iIntros (s) "[Hluck | [(Hcr & Hcheck)| (%p'' & %Hp'' & Hcr & Hcheck)]]".
        * (* luck *)
          wp_pures.
          wp_bind (checker _).
          wp_apply (ub_twp_wand with "Hluck").
          iIntros (?) "(-> & HΘ)".
          wp_pures.
          eauto.
        * (* progress *)
          wp_pures.
          wp_bind (checker _).
          wp_apply (ub_twp_wand with "Hcheck").
          iIntros (r) "[(-> & HΨ) | (-> & HΘ)]".
          -- (* not lucky: checker rejects *)
             wp_pure. iApply ("IHp" with "[] Hfinal Hcr HΨ").
             iPureIntro. lia.
          -- (* lucky: checker accepts *)
             wp_pures. eauto.
        * (* amplification *)
          wp_pures.
          wp_bind (checker _).
          wp_apply (ub_twp_wand with "Hcheck").
          iIntros (r) "[(-> & HΨ) | (-> & HΘ)]".
          -- (* not lucky: checker rejects *)
             assert (HiL' : (i' < iL)%nat) by lia.
             wp_pure. iApply ("IHerror" $! HiL' with "Hfinal Hcr HΨ"). eauto.
          -- (* lucky: checker accepts *)
             wp_pures. eauto.
    Qed.
End incremental_spec.
