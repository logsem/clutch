From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import big_op.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.prelude Require Import options.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export ghost_map.

From self.prob Require Export couplings distribution.
From self.program_logic Require Export language exec weakestpre.
From self.prob_lang Require Export lang primitive_laws.
From self.prob_lang Require Export class_instances spec_ra.
From self.prob_lang Require Import tactics notation.
From self.prob Require Export distribution.
Import uPred.

Local Open Scope R.


Section helper_lemma.
  Context `{!irisGS prob_lang Σ}.

  Lemma refRcoupl_bind' `{Countable A, Countable B} μ1 μ2 f g (R S : A → B → Prop) :
    ⌜refRcoupl μ1 μ2 R⌝ -∗
    (∀ a b, ⌜R a b⌝ ={∅}=∗ ⌜refRcoupl (f a) (g b) S⌝) -∗
    |={∅}=> ⌜refRcoupl (dbind f μ1) (dbind g μ2) S⌝ : iProp Σ.
  Proof.
    iIntros (HR) "HS".
    iApply (pure_impl_1 (∀ a b, R a b → refRcoupl (f a) (g b) S)).
    { iPureIntro. by eapply refRcoupl_bind. }
    iIntros (???).
    by iMod ("HS" with "[//]").
  Qed.

  Definition pure_eq (ρ1 ρ2 : cfg) := (ρ1.1 = ρ2.1) ∧ (ρ1.2.(heap) = ρ2.2.(heap)).

  Lemma foo_helper_1 (m : nat) (e1 : expr) (σ1 : state) (e1' : expr) (σ1' : state) (R: cfg -> cfg -> Prop):
    Rcoupl (prim_step e1 σ1) (prim_step e1' σ1') R ->
    (forall ρ2 ρ2', R ρ2 ρ2' -> ∃ n : nat, refRcoupl (prim_exec ρ2 m) (prim_exec ρ2' n) pure_eq)
    -> ∃ n : nat, refRcoupl (prim_exec (e1, σ1) (S m)) (prim_exec (e1', σ1') n) pure_eq.
  Proof.
    intros (μ & ((HμL & HμR) & HμSupp)) Hcont.
    assert (exists n, ∀ ρ2 ρ2' : cfg, μ (ρ2, ρ2') > 0 → refRcoupl (prim_exec ρ2 m) (prim_exec ρ2' n) pure_eq) as (n & Hn).
    (* Somehow use finiteness of the support? *)
    { admit. }
    exists (S n).
    rewrite /prim_exec /=.
    case_match; case_match.
    + specialize (Hn (e1, σ1) (e1', σ1')).
      assert (μ (e1, σ1, (e1', σ1')) > 0) as Haux; [admit | ].
      specialize (Hn Haux).
      destruct m; destruct n;
      rewrite /prim_exec in Hn.
  Admitted.

  Lemma bar (ρ : cfg) :
    dbind (λ ρ', lim_prim_exec ρ') (prim_step_or_val ρ) = (lim_prim_exec ρ).
  Proof. Admitted.

  (* Definition ref_eq_coupl (ρ1 ρ2 : cfg) := *)
  (*   ∀ n, refRcoupl (prim_exec ρ1 n) (lim_prim_exec ρ2) pure_eq. *)

  Lemma qux (μ1 μ2 : distr cfg) :
    Rcoupl μ1 μ2 pure_eq ↔ (dmap (λ '(e, σ), (e, σ.(heap))) μ1) = (dmap (λ '(e, σ), (e, σ.(heap))) μ2).
  Proof. Admitted.

  Lemma quux (μ1 μ2 : distr cfg) :
    refRcoupl μ1 μ2 pure_eq ↔ refRcoupl (dmap (λ '(e, σ), (e, σ.(heap))) μ1) (dmap (λ '(e, σ), (e, σ.(heap))) μ2) eq.
  Proof. Admitted.

  Lemma quuux e1 σ1 α m :
    dmap (λ '(e, σ), (e, heap σ)) (dbind (λ σ2, prim_exec (e1, σ2) m) (state_step σ1 α)) = dmap (λ '(e, σ), (e, heap σ)) (prim_exec (e1, σ1) m).
  Proof. Admitted.

  Lemma qux_something e1 σ1 α :
    Rcoupl (dret (e1, σ1)) (dbind (λ σ2 : state, dret (e1, σ2)) (state_step σ1 α)) pure_eq.
  Proof.
    assert (dret (e1 , σ1) = dbind (λ σ, dret (e1, σ)) (dret σ1)) as Hfck.
    { rewrite dret_id_left//. }
    rewrite Hfck.
    eapply (Rcoupl_bind _ _ _ _ (λ σ σ', σ.(heap) = σ'.(heap))).
    { intros ???. apply Rcoupl_ret. done. }
    clear Hfck.
    exists (dprod (dret σ1) (state_step σ1 α)). split.
    * split.
      { rewrite lmarg_dprod //. }
      { rewrite rmarg_dprod //. }
    * intros [] [->%dret_pos ?]%dprod_pos. simpl.
      apply state_step_support_equiv_rel in H.
      by inversion H.
  Qed.

  (* Lemma alejandro_magic σ1 α m : *)
  (*   Rcoupl (dret σ1) (state_step σ1 α) (λ σ2 σ2', ∀ e, Rcoupl (prim_exec (e, σ2) m) (prim_exec (e, σ2') m) pure_eq). *)
  (* Proof. *)

  Lemma pure_eq_coupl_sym μ1 μ2 :
    Rcoupl μ1 μ2 pure_eq
    -> Rcoupl μ2 μ1 pure_eq.
  Proof.
    intros H.
    apply qux.
    apply qux in H.
    auto.
  Qed.

  Lemma pure_eq_coupl_trans μ1 μ2 μ3 :
    Rcoupl μ1 μ2 pure_eq
    -> Rcoupl μ2 μ3 pure_eq
    -> Rcoupl μ1 μ3 pure_eq.
  Proof.
    intros H12 H23.
    apply qux.
    apply qux in H12.
    apply qux in H23.
    rewrite H12; auto.
  Qed.




  Lemma fooo : forall m e1 σ1 α,
      Rcoupl (prim_exec (e1, σ1) m)
             (fair_conv_comb (prim_exec (e1, (state_upd_tapes <[α := σ1.(tapes) !!! α ++ [true]]> σ1)) m )
                             (prim_exec (e1, (state_upd_tapes <[α := σ1.(tapes) !!! α ++ [false]]> σ1)) m ))
             (pure_eq).
  Proof.
    induction m; intros e1 σ1 α.
    - rewrite /prim_exec/=.
      destruct (to_val e1).
      + exists (dprod (dret (e1, σ1))
    (fair_conv_comb (dret (e1, state_upd_tapes <[α:=tapes σ1 !!! α ++ [true]]> σ1))
       (dret (e1, state_upd_tapes <[α:=tapes σ1 !!! α ++ [false]]> σ1)))).
        split; [split ; [ rewrite lmarg_dprod // | rewrite rmarg_dprod //] | ].
        intros ((e2 & σ2) & (e2' & σ2')) Hpos.
        simpl in *.
        rewrite /pmf/= in Hpos.
        rewrite fair_conv_comb_pmf in Hpos.
        assert ((dret (e1, σ1) (e2, σ2) > 0 /\ dret (e1, state_upd_tapes <[α:=tapes σ1 !!! α ++ [true]]> σ1) (e2', σ2') > 0)
            \/ (dret (e1, σ1) (e2, σ2) > 0 /\ dret (e1, state_upd_tapes <[α:=tapes σ1 !!! α ++ [false]]> σ1) (e2', σ2') > 0))
        as [(Hpos1 & Hpos2) | (Hpos3 & Hpos4)].
        { (* This is a fact about the reals, should be easy *)
          admit. }
        ++ rewrite /pmf/=/dret_pmf/= in Hpos1.
           case_bool_decide as Heq1; try lra.
           rewrite Heq1.
           rewrite /pmf/=/dret_pmf/= in Hpos2.
           case_bool_decide as Heq2; try lra.
           rewrite Heq2.
           rewrite /pure_eq/=//.
        ++ rewrite /pmf/=/dret_pmf/= in Hpos3.
           case_bool_decide as Heq3; try lra.
           rewrite Heq3.
           rewrite /pmf/=/dret_pmf/= in Hpos4.
           case_bool_decide as Heq4; try lra.
           rewrite Heq4.
           rewrite /pure_eq/=//.
    + exists dzero.
    split.
    {
      split.
      { rewrite /lmarg dmap_dzero; auto.}
      { apply distr_ext; intros.
        rewrite rmarg_pmf fair_conv_comb_pmf /pmf /=.
        rewrite SeriesC_0; auto; lra.
      }
    }
    intros ? Hpos.
    rewrite /pmf/= in Hpos.
    lra.
  - rewrite /prim_exec/=.
    destruct (to_val e1) eqn:He1.
    + specialize (IHm e1 σ1 α).
      rewrite /prim_exec/= in IHm.
      destruct m; simpl in *;
      rewrite He1 in IHm; auto.
    + rewrite -/prim_exec. admit.
  Admitted.




  Lemma quuuux e1 σ1 α m :
    dmap (λ '(e, σ), (e, heap σ)) (prim_exec (e1, σ1) m) = dmap (λ '(e, σ), (e, heap σ)) (dbind (λ σ2, (prim_exec (e1, σ2) m)) (state_step σ1 α)).
  Proof.
    apply qux.
    assert
      ((state_step σ1 α ≫= (λ σ2 : language.state prob_lang, prim_exec (e1, σ2) m))=
         (fair_conv_comb (prim_exec (e1, (state_upd_tapes <[α := σ1.(tapes) !!! α ++ [true]]> σ1)) m )
                             (prim_exec (e1, (state_upd_tapes <[α := σ1.(tapes) !!! α ++ [false]]> σ1)) m ))
      ) as ->; [ | apply fooo].
    (* The remaining should be a lemma about the language *)
(*
    induction m=>/=.
    - destruct (to_val e1).
      + apply qux_something.
      + assert ((dbind (λ _ : state, dzero) (state_step σ1 α)) = dzero) as ->.
        { eapply distr_ext. intros ?.
          rewrite /pmf /= /dbind_pmf.
          apply SeriesC_0. intros ?. rewrite {2}/pmf /=. lra. }
        (* TODO: state this as a separate lemma *)
        exists dzero. split.
        { split.
          - rewrite /lmarg  dmap_dzero //.
          - rewrite /rmarg  dmap_dzero //. }
        intros ?. rewrite /pmf /=. lra.
    - destruct (to_val e1) eqn:Heq.
      + apply qux_something.
      + (* rewrite dbind_assoc. *)

        assert (Rcoupl (state_step σ1 α ≫= (λ σ2, prim_step e1 σ2)) (prim_step e1 σ1 ≫= (λ '(e2, σ2), strength_l e2 (state_step σ2 α))) pure_eq).
        { admit. }
        rewrite dbind_assoc.

        assert (Rcoupl ((state_step σ1 α ≫= (λ σ2, prim_step e1 σ2)) ≫= (λ b : language.cfg prob_lang, prim_exec b m)) ((prim_step e1 σ1 ≫= (λ '(e2, σ2), strength_l e2 (state_step σ2 α))) ≫= (λ b : language.cfg prob_lang, prim_exec b m)) pure_eq).
        { eapply Rcoupl_bind; [|done].
*)
          Admitted.


  
  Lemma baz e1 σ1 e1' σ1' α α' R m :
    Rcoupl (state_step σ1 α) (state_step σ1' α') R →
    (∀ σ2 σ2', R σ2 σ2' → refRcoupl (prim_exec (e1, σ2) (S m)) (lim_prim_exec (e1', σ2')) pure_eq) →
    refRcoupl (prim_exec (e1, σ1) (S m)) (lim_prim_exec (e1', σ1')) pure_eq.
  Proof.
    intros HR Hcont.
    assert (refRcoupl (dbind (λ σ2, prim_exec (e1, σ2) (S m)) (state_step σ1 α))
                      (dbind (λ σ2', lim_prim_exec (e1', σ2')) (state_step σ1' α')) pure_eq) as H.
    { eapply refRcoupl_bind; [|done]. by apply weaken_coupl. }

    (* destruct m. *)
    (* - simpl in *. destruct (prob_lang.to_val e1) eqn:Heq.  *)
    (*   +  *)

    apply quux.
    apply quux in H.
    assert ((dmap (λ '(e, σ), (e, heap σ)) (prim_exec (e1, σ1) (S m))) =
            (dmap (λ '(e, σ), (e, heap σ)) (dbind (λ σ2 : language.state prob_lang, prim_exec (e1, σ2) (S m)) (state_step σ1 α)))) as H1.
    { rewrite -prim_step_prim_exec.
      assert ((dbind (λ σ2, prim_exec (e1, σ2) (S m)) (state_step σ1 α)) =
              (dbind (λ σ2 , (dbind (λ ρ' : language.cfg prob_lang, prim_exec ρ' m) (prim_step_or_val (e1, σ2)))) (state_step σ1 α))) as Hfoo by admit.
      rewrite Hfoo. clear Hfoo.
      apply qux.
      rewrite dbind_assoc.
      eapply (Rcoupl_bind _ _ _ _ pure_eq).
      {


      admit. }
    assert ((dmap (λ '(e, σ), (e, heap σ)) (lim_prim_exec (e1', σ1'))) =
            (dmap (λ '(e, σ), (e, heap σ)) (dbind (λ σ2' : language.state prob_lang, lim_prim_exec (e1', σ2')) (state_step σ1' α')))) as H2.
    { admit. }
    Admitted.


  Lemma foo (e1 : expr) (σ1 : state) (e1' : expr) (σ1' : state) (m : nat) :
    to_val e1 = None ->
    exec_coupl  e1 σ1 e1' σ1'
      (λ '(e2, σ2) '(e2', σ2'), ⌜refRcoupl (prim_exec (e2, σ2) m) (lim_prim_exec (e2', σ2')) pure_eq⌝)%I ⊢@{iProp Σ}
    |={∅}=> ⌜refRcoupl (prim_exec (e1, σ1) (S m) ) (lim_prim_exec (e1', σ1')) pure_eq⌝.
  Proof.
    iIntros (Hv) "Hexec".
    iAssert (⌜to_val e1 = None⌝)%I as "-#H"; [done|]. iRevert "Hexec H".
    rewrite /exec_coupl /exec_coupl'.
    iPoseProof (least_fixpoint_iter
                  (exec_coupl_pre 
                     (λ '(e2, σ2) '(e2', σ2'), ⌜refRcoupl (prim_exec (e2, σ2) m) (lim_prim_exec (e2', σ2')) pure_eq⌝)%I)
                  (λ '((e1, σ1), (e1', σ1')), ⌜to_val e1 = None⌝ ={∅}=∗
                      ⌜refRcoupl (prim_exec (e1, σ1) (S m)) (lim_prim_exec (e1', σ1')) pure_eq⌝)%I
                 with "[]") as "H"; last first.
    { iIntros "Hfix %". by iMod ("H" $! ((_, _), (_, _)) with "Hfix [//]"). }
    clear.
    iIntros "!#" ([[e1 σ1] [e1' σ1']]). rewrite /exec_coupl_pre.
    iIntros "[(% & %Hcpl & H) | [? | [? | H]]] %Hv".
    - rewrite -prim_step_prim_exec.
      rewrite -bar.
      rewrite {1}/prim_step_or_val /= Hv.
      assert (to_val e1' = None) as Hv' by admit.
      rewrite {1}/prim_step_or_val /= Hv'.
      iApply (refRcoupl_bind' _ _ _ _ R2).
      { iPureIntro. by apply weaken_coupl. }
      iIntros ([] [] HR2). iMod ("H" with "[//]"). auto.
    - admit.
    - admit.
    - simpl. rewrite Hv.
      iInduction (list_prod (get_active σ1) (get_active σ1')) as [| [α α']] "IH"; [done|].
      rewrite big_orL_cons.
      iDestruct "H" as "[(% & %Hcpl & H) | Ht]"; last first.
      { by iApply "IH". }
      iClear "IH". simpl in *.

Admitted.


End helper_lemma.
