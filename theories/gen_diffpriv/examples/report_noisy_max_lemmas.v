(** Discrete-Laplace instantiation of the generic report-noisy-max library
    ([report_noisy_max_generic_lemmas]).  The ~700-line argmax + tape-state-step
    machinery is INHERITED from the generic library; only the two per-draw
    couplings are Laplace-specific:

      - [Hiso_laplace]   : the 0-cost location isometry;
      - [Hshift_laplace] : the costly +1 shift (cost [num/den]) at the argmax
                           coordinate, valid when [dZ loc loc' ≤ 1].

    Re-exports the noise-independent pure lemmas ([report_noisy_max_pure]) so
    downstream clients (e.g. [report_noisy_max]) keep seeing [list_max_index_eq]
    etc. unchanged. *)
From clutch.prob Require Import couplings_dp couplings differential_privacy distribution.
From clutch.gen_diffpriv Require Import all.
From clutch.gen_diffpriv.lib Require Import laplace laplace_tapes.
From clutch.gen_prob_lang Require Import gwp.list families.
From clutch.gen_diffpriv.examples Require Export report_noisy_max_pure.
From clutch.gen_diffpriv.examples Require Import report_noisy_max_generic_lemmas.

(** [Hiso] for Laplace: the 0-cost location isometry on the rational-rate draw,
    handling both the [ε>0] branch and the degenerate [dret] branch. *)
Fact Hiso_laplace (num den loc loc' : Z) :
  Mcoupl (laplace_rat num den loc) (laplace_rat num den loc')
         (λ z z', z - z' = loc - loc')%Z 0.
Proof.
  intros ?? Hf Hg Hfg.
  rewrite exp_0. ring_simplify.
  rewrite -(SeriesC_translate _ (loc - loc')).
  2:{ intros. apply Rmult_le_pos. 1: auto. apply Hf. }
  2:{ eapply ex_seriesC_le. 2: apply (pmf_ex_seriesC (laplace_rat num den loc)).
      intros z. simpl. split.
      - apply Rmult_le_pos => //. apply Hf.
      - destruct (Hf z). etrans. 2: right ; apply Rmult_1_r.
        apply Rmult_le_compat => //.
  }
  apply SeriesC_le.
  2:{ eapply ex_seriesC_le. 2: apply (pmf_ex_seriesC (laplace_rat num den loc')).
      intros z. simpl. split.
      - apply Rmult_le_pos => //. apply Hg.
      - destruct (Hg z). etrans. 2: right ; apply Rmult_1_r.
        apply Rmult_le_compat => //.
  }
  intros z. split.
  { apply Rmult_le_pos => //. apply Hf. }
  opose proof (Hfg ((z + (loc - loc'))) z _)%Z.
  1: lia.
  apply Rmult_le_compat => //.
  1: apply Hf.
  rewrite /laplace_rat/laplace/laplace'/pmf{1 3}/laplace_f/laplace_f_nat.
  right.
  case_decide.
  1: do 7 f_equal ; lia.
  simpl. rewrite /dret_pmf. repeat case_bool_decide ; try lra. 1,2: qify_r ; zify_q.
  1,2: lia.
Qed.

(** [Hshift] for Laplace: the +1 shift at cost [num/den], from [Mcoupl_laplace_alt]
    at the doubled rate ε = num/(2·den), whose [|1+loc-loc'|·ε] cost is ≤ num/den
    because [dZ loc loc' ≤ 1] gives [|1+loc-loc'| ≤ 2]. *)
Fact Hshift_laplace (num den loc loc' : Z) :
  (0 < IZR num / IZR (2*den))%R → (dZ loc loc' <= 1)%R →
  DPcoupl (laplace_rat num (2*den) loc) (laplace_rat num (2*den) loc')
          (λ z z', z + 1 = z')%Z (IZR num / IZR den) 0.
Proof.
  intros Hproof Hd.
  rewrite /laplace_rat. case_decide ; [|done].
  eapply DPcoupl_mono; [done|done|..]; last apply Mcoupl_to_DPcoupl;
    last eapply (Mcoupl_laplace_alt _ _ _ 1); try done.
  simpl.
  rewrite mult_IZR.
  replace (_/(_*_))%R with (/2 * (IZR num / IZR den))%R; last (rewrite Rdiv_mult_distr; lra).
  rewrite -Rmult_assoc.
  rewrite -{2}(Rmult_1_l (_/_)%R).
  apply Rmult_le_compat_r.
  - left. by apply ineq_convert.
  - cut (IZR (Z.abs (1 + loc - loc')) <=2)%R; first lra.
    rewrite -Rabs_Zabs.
    apply dZ_bounded_cases'.
    apply dZ_bounded_cases in Hd. simpl in *. lia.
Qed.

Section laplace.
  Context {S : Sig} `{!SampleIn laplace_family S} `{!diffprivGS S Σ}.

  (** The Laplace report-noisy-max list coupling: the generic
      [hoare_couple_noise_list] instantiated at [sample := laplace_rat].  Since
      [laplace_family = mkZNoise laplace_rat laplace_rat_mass] (families.v), the
      generic [↪N] tape views ARE the Laplace [↪L] views, so the statement is the
      Laplace one verbatim. *)
  Definition hoare_couple_laplace_list :=
    hoare_couple_noise_list laplace_rat laplace_rat_mass Hiso_laplace Hshift_laplace
      (S := S).

End laplace.
