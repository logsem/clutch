From iris.proofmode Require Import base proofmode.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.base_logic.lib Require Import ghost_map invariants fancy_updates.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.delay_prob_lang Require Import notation metatheory.
From clutch.common Require Export language.
From clutch.base_logic Require Import error_credits.
From clutch.elton Require Import weakestpre primitive_laws rupd.
From clutch.prob Require Import distribution.
Import uPred.

Set Default Proof Using "Type".

Section adequacy.
  Context `{!eltonGS Σ}.
  Lemma step_fupd_fupdN_S n (P : iProp Σ) :  ((|={∅}▷=>^(S n) P) ⊣⊢ (|={∅}=> |={∅}▷=>^(S n) P))%I.
  Proof. iSplit; iIntros; simpl; iApply fupd_idemp; iFrame. Qed.
  
  Lemma pgl_dbind_adv' `{Countable A, Countable A'}
    (f : A → distr A') (μ : distr A) (T : A' → Prop) ε' n :
    ⌜ exists r, forall a, 0 <= ε' a <= r ⌝ -∗
    (∀ a , |={∅}=> |={∅}▷=>^(n) ⌜pgl (f a) T (ε' a)⌝) -∗
    |={∅}=> |={∅}▷=>^(n) ⌜pgl (dbind f μ) T ( Expval μ ε')⌝ : iProp Σ.
  Proof.
    iIntros (?) "H".
    iApply (step_fupdN_mono _ _ _ (⌜(∀ a, pgl (f a) T (ε' a))⌝)).
    { iIntros (?). iPureIntro. rewrite <-Rplus_0_l. eapply pgl_dbind_adv; try done.
      by apply pgl_trivial.
    }
    by iIntros (?) "/=".
  Qed.
  
End adequacy.


Class eltonGpreS Σ := EltonGpreS {
  eltonGpreS_iris  :: invGpreS Σ;
  eltonGpreS_heap  :: ghost_mapG Σ loc val;
  eltonGpreS_urns :: ghost_mapG Σ loc urn;
  eltonGpreS_err   :: ecGpreS Σ;
                        }.

Definition eltonΣ : gFunctors :=
  #[invΣ; ghost_mapΣ loc val;
    ghost_mapΣ loc urn;
    GFunctor (authR nonnegrealUR)].
Global Instance subG_eltonGPreS {Σ} : subG eltonΣ Σ → eltonGpreS Σ.
Proof. solve_inG. Qed.

Theorem elton_adequacy Σ `{eltonGpreS Σ} (e:expr) (σ:state) (ε:R) ϕ:
  is_well_constructed_expr e = true ->
  expr_support_set e ⊆ urns_support_set (urns σ) ->
  (0<=ε)%R ->
  (∀ `{eltonGS Σ}, ⊢ ↯ ε -∗ WP e {{ rupd ϕ }}) ->
  pgl (urns_f_distr (σ.(urns)) ≫= λ f,
         d_proj_Some (expr_urn_subst f e) ≫= λ e', 
            lim_exec (remove_drand_expr e', σ)) ϕ ε
.
Proof.
Admitted. 
