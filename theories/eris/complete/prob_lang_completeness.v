From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import base proofmode classes.
From iris.base_logic Require Export invariants lib.ghost_map lib.cancelable_invariants.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.

From clutch.common Require Export language ectx_language.
From clutch.prob_lang Require Import notation tactics metatheory.
From clutch.prob_lang Require Export lang.
From clutch.eris Require Export weakestpre total_weakestpre lang_completeness proofmode derived_laws.
From clutch.prob Require Import distribution.
From clutch.eris.complete Require Export ectx_lang_completeness lang_completeness.
From clutch.pure_complete Require Export prob_additional.

Local Open Scope R.

Section Instances.

Context `{!erisGS Σ}.

Definition heap_inv (σ : prob_lang.state) : iProp Σ :=
    ([∗ map] ℓ↦v ∈ σ.(heap),  ℓ ↦ v) 
  ∗ ([∗ map] ι↦α ∈ σ.(tapes), ι ↪ α).

Definition na (e : prob_lang.expr) := ∀ n σ e' σ', 
  pexec n (e, σ) (e', σ') > 0 → dom σ.(heap) = dom σ'.(heap) ∧ dom σ.(tapes) = dom σ'.(tapes).

Lemma na_step : ∀ e σ e' σ', 
  step (e, σ) (e', σ') > 0 → na e'.
Proof.
Admitted.

Definition lim_step (ρ : cfg prob_lang) : distr (val prob_lang * state prob_lang). 
Admitted.

Lemma lim_step_fill K e σ : 
  lim_step (fill K e, σ) = dbind (λ '(v, σ'), lim_step (fill K (Val v), σ')) (lim_step (e, σ)).
Admitted.

Lemma lim_step_step ρ : 
  lim_step ρ = dbind lim_step (step ρ).
Admitted.

(* Definition err (φ: prob_lang.val → iProp Σ) (ρ : cfg prob_lang) := probp (lim_exec ρ) (λ v, ¬ ⊢ φ v). *)
Definition err (φ: prob_lang.val → iProp Σ) (ρ : cfg prob_lang) := probp (lim_step ρ) (λ '(v, σ), ¬ ⊢ heap_inv σ -∗ φ v).

Lemma probp_1 `{Countable A} (μ : distr A) (P : A → Prop) : 
  ∀ a, P a → probp μ P = 1.
Admitted.  

(* Lemma head_step_to_val (e0 : expr prob_lang) σ0 e σ:
  head_step e0 σ0 (e, σ) > 0 →
  is_Some (to_val e).
Proof. 
  intros Hhr.
  rewrite head_step_support_equiv_rel in Hhr.
  inversion Hhr; subst; try done.
  (* intros Hna Hhr.
  rewrite head_step_support_equiv_rel in Hhr.
  induction Hhr. *)
Admitted. *)

Lemma err_fill K e σ φ:
  na e →
  err (λ v, WP fill K (of_val v) {{ v0, φ v0 }})%I (e, σ) = err φ (fill K e, σ).
Proof. 
  intros Hna (* [[e' σ'] Hhr] *).
  (* rewrite head_step_support_equiv_rel in Hhr. *)
  rewrite /err lim_step_fill probp_dbind.
  (* inversion Hhr.  *)
  Search head_step_rel.
  (* rewrite /err lim_step_fill probp_dbind.
  unfold probp at 1. simpl.
  apply SeriesC_ext.
  intros [v σ0].
  case_bool_decide.
  - simpl. eassert (probp _ _ = 1) as ->; try lra.
    rewrite /probp. *)
Admitted.


Lemma err_fin: ∀ φ (v : prob_lang.val) σ,
  err φ (of_val v, σ) < 1 →
  heap_inv σ -∗ φ v.
Proof.
  (* intros ???.
  rewrite /err /probp (lim_exec_final (of_val v, σ) v) //=.
  intros.
  destruct (decide (⊢ φ v)). 
  - iIntros. iApply b.
  - apply (probp_dret_true v (λ a, (not (bi_emp_valid (φ a))))) in n.
    rewrite /probp in n. lra. *)
Admitted.

End Instances.

Section Completeness.


End Completeness.

(* From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import base proofmode classes.
From iris.base_logic Require Export invariants lib.ghost_map lib.cancelable_invariants.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.

From clutch.common Require Export language ectx_language.
From clutch.prob_lang Require Export lang notation.
From clutch.eris Require Export weakestpre total_weakestpre lang_completeness proofmode derived_laws.
From clutch.prob Require Import distribution.
From clutch.eris.complete Require Export exec_probs.
From clutch.pure_complete Require Export prob_additional.

Local Open Scope R.

Section completeness.
  Context `{!erisGS Σ}.

  Definition heap_inv (σ : prob_lang.state) : iProp Σ :=
    ([∗ map] ℓ↦v ∈ σ.(heap),  ℓ ↦ v) 
  ∗ ([∗ map] ι↦α ∈ σ.(tapes), ι ↪ α).
  

  (* Lemma eris_complete_pre e σ φ ε E: 
    head_reducible e σ →
    (pgl (exec 1 (e, σ)) φ ε) → 
    (∀ e' σ' ε', 
        0 < step (e, σ) (e', σ') → 
        pgl (exec 1 (e', σ')) φ ε' →
        ↯ ε' -∗ 
        heap_inv σ' -∗ 
        WP e' @ E {{ v,  ⌜φ v⌝ }}) → 
    ↯ ε -∗ 
    heap_inv σ -∗ 
    WP e @ E {{ v,  ⌜φ v⌝ }}.
  Proof.
 *)

  Lemma ex_fresh_loc_heap {V} l (m : gmap loc V) : 
    m !! l = None →
    ∃ m', m ⊆ m' ∧ fresh_loc m' = l.
  Proof.
    Local Transparent fresh_loc.
    Search fresh_loc.
    unfold fresh_loc, fresh, set_fresh, fresh, elements, infinite_fresh, gset_elements, loc_infinite.
    simpl.
    Local Opaque fresh_loc.
  Admitted.

  Lemma head_reducible_lim_exec_one (e : expr prob_lang) σ : 
    head_reducible e σ →
    lim_exec (e, σ) = exec 1 (e, σ).
  Proof.

  Admitted.
  (* 
  Lemma eris_complete_pre_exec e σ φ ε :
    (∀ σ0, 
      σ0.(heap) ⊆ σ.(heap) → 
      σ0.(tapes) ⊆ σ.(tapes) →
      pgl (lim_exec (e, σ)) φ ε) → 
      
    ∃ E1, 
      ε >= Expval (prim_step e σ) E1 ∧
      (∀ e' σ', 
        prim_step e σ (e', σ') > 0 → 
        (
          ∀ σ0, 
            σ0.(heap) ⊆ σ'.(heap) → 
            σ0.(tapes) ⊆ σ'.(tapes) →
          pgl (lim_exec (e', σ0)) φ (E1 (e', σ'))
        ) 
      ).
  Proof.
  (* 
    intro Hcond.
    eexists.
    split. 
    { admit. }
    intros e' σ' Hstep. 
    destruct (decomp e) as [K e0] eqn : Hde.
    rewrite /prim_step //= /ectx_language.prim_step //= Hde dmap_pos in Hstep.
    destruct Hstep as ((e0' & σ0')&Hfill&Hhstep).
    inversion Hfill; subst.
    intros σ0 Hhσ0 Htσ0.    *)

    

    (* induction Hhstep.
    1 - 13 : admit.
    2 - 11 : admit. 
    {
      intros σ0 Hhσ0 Htσ0.

    } *)
   *)

  Lemma eris_complete_pre_exec_det e σ φ ε :
    (∀ σ0, 
      σ0.(heap) ⊆ σ.(heap) → 
      σ0.(tapes) ⊆ σ.(tapes) →
      pgl (lim_exec (e, σ)) φ ε) → 
    (∃ ρ', prim_step e σ = dret ρ') →
      (∀ e' σ', 
        prim_step e σ (e', σ') > 0 → 
        (
          ∀ σ0, 
            σ0.(heap) ⊆ σ'.(heap) → 
            σ0.(tapes) ⊆ σ'.(tapes) →
          pgl (lim_exec (e', σ0)) φ ε
        ) 
      ).
  Proof.
    intros Hcond Hdet e' σ' Hstep.
    destruct (decomp e) as [K e0] eqn : Hde.
    rewrite /prim_step //= /ectx_language.prim_step //= Hde dmap_pos in Hstep.
    destruct Hstep as ((e0' & σ0')&Hfill&Hhstep).
    inversion Hfill; subst.
    intros σ0 Hhσ0 Htσ0. 
    assert (head_step e0 σ = dret (e0', σ0')) as Hhdet. {
      admit.
    }
    pose proof Hhstep as H.
    rewrite head_step_support_equiv_rel in H.
    induction H.
    1 - 13 : admit.
    2 - 10 : admit.  
    {
      rewrite /head_step //= in Hhdet. 
      case_bool_decide; last real_solver.
      apply dret_ext_inv in Hhdet. 
      inversion Hhdet; subst.
      clear H2 H4 H5 Hhdet.
      admit.
    }
    (* eexists.
    split. 
    { admit. }
    intros e' σ' Hstep. 
    destruct (decomp e) as [K e0] eqn : Hde.
    rewrite /prim_step //= /ectx_language.prim_step //= Hde dmap_pos in Hstep.
    destruct Hstep as ((e0' & σ0')&Hfill&Hhstep).
    inversion Hfill; subst.
    intros σ0 Hhσ0 Htσ0.    *)

    

    (* induction Hhstep.
    1 - 13 : admit.
    2 - 11 : admit. 
    {
      intros σ0 Hhσ0 Htσ0.

    } *)

  Admitted.

  Lemma eris_complete_pre e σ φ ε E: 
    head_reducible e σ →
    (∀ σ0, 
      σ0.(heap) ⊆ σ.(heap) → 
      σ0.(tapes) ⊆ σ.(tapes) →
      pgl (exec 1 (e, σ)) φ ε) → 
    (∀ e' σ' ε', 
        0 < step (e, σ) (e', σ') → 
        (
          ∀ σ0, 
            σ0.(heap) ⊆ σ'.(heap) → 
            σ0.(tapes) ⊆ σ'.(tapes) →
          pgl (exec 1 (e', σ0)) φ ε'
        ) →
        ↯ ε' -∗ 
        heap_inv σ' -∗ 
        WP e' @ E {{ v,  ⌜φ v⌝ }}) → 
    ↯ ε -∗ 
    heap_inv σ -∗ 
    WP e @ E {{ v,  ⌜φ v⌝ }}.
  Proof.
    iIntros (((e1&σ1)&Hred) Hp Hind) "Herr (Hs & Ht)".
    pose proof Hred as H.
    rewrite head_step_support_equiv_rel in H.
    iInduction H as [] "IH"; simplify_eq.
    1 - 13 : admit.
    2 - 10 : admit. 
    {
      simpl in Hp. rewrite head_prim_step_eq in Hp; auto. 
      rewrite /ectx_language.head_step //= in Hp. case_bool_decide; last admit.
      rewrite dret_id_left' //= in Hp.
      wp_alloc l as "Hl"; simpl; first by lia.
      rewrite -head_prim_step_eq in Hred. 
      destruct ((heap σ) !! l) eqn : Hhl. {
        iPoseProof (big_sepM_lookup _ _ _ _ Hhl with "Hs") as "Hp". 
        admit.
        (* iPoseProof (ghost_map_elem_ne with "Hl Hp") as "?". *)
      }
      pose proof (ex_fresh_loc_heap _ _ Hhl) as (h' & Hh' & <-). 

      specialize (Hind _ _ ε Hred).
      (* erewrite <-(pgl_wp_value_fupd _ E _). *)
      Search ([∗ map] _↦_ ∈ _ , _)%I.
      (* iAssert (WP #l @ E {{ v0, ⌜φ v0⌝ }})%I with "[Herr Hl Hh]" as "Hwp".
      2 : {
        (* rewrite -(pgl_wp_value_fupd wp_default _ (fun v => ⌜φ v⌝)%I).
        Unset Printing Notations. simpl. 
        iApply "Hwp". *)
      } *)
      (* epose proof (Hind #(fresh_loc (heap σ)) (state_upd_heap_N (fresh_loc (heap σ)) (Z.to_nat z) v σ) ε _).  *)
      (* Search wp_allocN.  *)
      (* simpl in *. case_bool_decide; last admit.
      wp_alloc l as "Hl"; simpl; first admit. *)

    }
    (* - simpl in *.  *)

  Admitted.
    
End completeness. *)