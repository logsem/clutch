From stdpp Require Import namespaces stringmap.
From iris.base_logic Require Import invariants.
From self.program_logic Require Import weakestpre.
From self.prob_lang Require Import notation proofmode primitive_laws spec_rules.
From self.logrel Require Import model rel_rules rel_tactics adequacy.
From self.typing Require Import types interp contextual_refinement soundness.
From self.prelude Require Import base.
Set Default Proof Using "Type*".

Lemma flip_erasure_l (x : string) :
  {[x := TTape]} ⊨ flip x ≤ctx≤ flip #() : TBool.
Proof.
  eapply (refines_sound_open prelogrelΣ).
  iIntros (??).
  rewrite /bin_log_related.
  iIntros (vs) "H /=".
  rewrite (env_ltyped2_lookup _ _ x) //; last first.
  { rewrite fmap_insert lookup_insert //. }
  iDestruct "H" as (v1 v2 ?) "H"; simplify_map_eq.
  rewrite /lrel_car/=.
  iDestruct "H" as (α1 α2 -> ->) "Hinv".
  iApply (refines_atomic_l _ _ []).
  iIntros (?) "[#Hspec Hr] !>".
  iInv (logN.@(α1, α2)) as "[>Hα1 >Hα2]".
  iApply wp_couple_flip_lbl_flip_eq; [solve_ndisj|].
  iFrame.
  iSplit; [done|].
  iIntros (b) "[Hα Hr]".
  wp_apply wp_value.
  iModIntro. iFrame. iExists _. iFrame "Hr Hspec".
  rel_values.
Qed.

Lemma flip_erasure_r (x : string) :
  {[x := TTape]} ⊨ flip #() ≤ctx≤ flip x : TBool.
Proof.
  eapply (refines_sound_open prelogrelΣ).
  iIntros (??).
  rewrite /bin_log_related.
  iIntros (vs) "H /=".
  rewrite (env_ltyped2_lookup _ _ x) //; last first.
  { rewrite fmap_insert lookup_insert //. }
  iDestruct "H" as (v1 v2 ?) "H"; simplify_map_eq.
  rewrite /lrel_car/=.
  iDestruct "H" as (α1 α2 -> ->) "Hinv".
  iApply (refines_atomic_l _ _ []).
  iIntros (?) "[#Hspec Hr] !>".
  iInv (logN.@(α1, α2)) as "[>Hα1 >Hα2]".
  iApply wp_couple_flip_flip_lbl_eq; [solve_ndisj|].
  iFrame.
  iSplit; [done|].
  iIntros (b) "[Hα Hr]".
  wp_apply wp_value.
  iModIntro. iFrame. iExists _. iFrame "Hr Hspec".
  rel_values.
Qed.

Lemma flip_erasure_ctx (x : string) :
  {[ x := TTape ]} ⊨ flip x =ctx= flip #() : TBool.
Proof.
  split.
  - apply flip_erasure_l.
  - apply flip_erasure_r.
Qed.
