From clutch Require Export clutch.
Set Default Proof Using "Type*".

Lemma rand_erasure_l (x : string) (N : nat) :
  {[x := TTape]} ⊨ rand #N from x ≤ctx≤ rand #N from #() : TNat.
Proof.
  eapply (refines_sound_open clutchRΣ).
  iIntros (??).
  rewrite /bin_log_related.
  iIntros (vs) "H /=".
  rewrite (env_ltyped2_lookup _ _ x) //; last first.
  { rewrite fmap_insert lookup_insert //. }
  iDestruct "H" as (v1 v2 ?) "#H"; simplify_map_eq.
  rewrite /lrel_car/=.
  iDestruct "H" as (α1 α2 M -> ->) "Hinv".
  destruct (decide (N = M)); simplify_eq.
  - (* We unpack the definition of [REL] because the tapes are owned by the
       invariant—the rules of [REL] do not support nice high-level invariant
       access patterns as of now.  *)
    iApply (refines_atomic_l _ _ []).
    iIntros (?) "Hr !>".
    iInv (logN.@(α1, α2)) as "[>Hα1 >Hα2]".
    iApply wp_couple_rand_lbl_rand_eq; [solve_ndisj|].
    iFrame.
    iIntros "!>" (n) "[Hα Hr]".
    iModIntro. iFrame. iExists _. iFrame "Hr".
    rel_values.
  - iApply (refines_atomic_l _ _ []).
    iIntros (?) "Hr !>".
    iInv (logN.@(α1, α2)) as "[>Hα1 >Hα2]".
    iApply wp_couple_rand_lbl_rand_wrong; [done|solve_ndisj|].
    iFrame "Hr Hα1 Hα2".
    iIntros "!>" (m) "[Hα1 Hr] !>".
    iFrame. iExists _. iFrame "Hr".
    rel_values.
Qed.

Lemma rand_erasure_r (x : string) (N : nat) :
  {[x := TTape]} ⊨ rand #N from #() ≤ctx≤ rand #N from x : TNat.
Proof.
  eapply (refines_sound_open clutchRΣ).
  iIntros (??).
  rewrite /bin_log_related.
  iIntros (vs) "H /=".
  rewrite (env_ltyped2_lookup _ _ x) //; last first.
  { rewrite fmap_insert lookup_insert //. }
  iDestruct "H" as (v1 v2 ?) "H"; simplify_map_eq.
  rewrite /lrel_car/=.
  iDestruct "H" as (α1 α2 M -> ->) "Hinv".
  destruct (decide (N = M)); simplify_eq.
  - iApply (refines_atomic_l _ _ []).
    iIntros (?) "Hr !>".
    iInv (logN.@(α1, α2)) as "[>Hα1 >Hα2]".
    iApply wp_couple_rand_rand_lbl_eq; [solve_ndisj|].
    iFrame "Hr Hα1 Hα2".
    iIntros "!>" (b) "[Hα2 Hr]".
    iModIntro. iFrame. iExists _. iFrame.
    rel_values.
  - iApply (refines_atomic_l _ _ []).
    iIntros (?) "Hr !>".
    iInv (logN.@(α1, α2)) as "[>Hα1 >Hα2]".
    iApply wp_couple_rand_rand_lbl_wrong; [done|solve_ndisj|].
    iFrame "Hr Hα1 Hα2".
    iIntros "!>" (m) "[Hα1 Hr] !>".
    iFrame. iExists _. iFrame "Hr".
    rel_values.
Qed.

Lemma rand_erasure_ctx (x : string) (N : nat) :
  {[ x := TTape ]} ⊨ rand #N from x =ctx= rand #N from #() : TNat.
Proof.
  split.
  - apply rand_erasure_l.
  - apply rand_erasure_r.
Qed.
