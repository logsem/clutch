From iris Require Import ghost_map.
From clutch.coneris Require Export coneris hash_view_interface.

Set Default Proof Using "Type*".

(** An implementation of a hash view*)

Section hash_view_impl.
  Context `{Hcon:conerisGS Σ,
              HinG: ghost_mapG Σ nat nat}.
  
  Definition hash_view_auth m γ := (ghost_map_auth γ 1 m ∗
                                   [∗ map] k↦v ∈m, (k ↪[γ]□ v))%I
  .
  Definition hash_view_frag k v γ := (k ↪[γ]□ v)%I.
  
  Lemma hash_view_auth_duplicate_frag m n b γ2:
    m!!n=Some b -> hash_view_auth m γ2 ==∗ hash_view_auth m γ2 ∗ hash_view_frag n b γ2.
  Proof.
    iIntros (Hsome) "[Hauth #Hauth']".
    rewrite /hash_view_auth/hash_view_frag.
    iFrame "Hauth Hauth'".
    by iDestruct (big_sepM_lookup_acc with "[$]") as "[$ K]".
  Qed.
  
  Lemma hash_view_auth_frag_agree m γ2 k v:
    hash_view_auth m γ2  ∗ hash_view_frag k v γ2 -∗
    ⌜m!!k=Some v⌝.
  Proof.
    rewrite /hash_view_auth/hash_view_frag.
    iIntros "[[H1 ?]H2]".
    by iCombine "H1 H2" gives "%".
  Qed.

  Lemma hash_view_auth_insert m n x γ:
    m!!n=None ->
    hash_view_auth m γ ==∗
    hash_view_auth (<[n:=x]> m) γ ∗ hash_view_frag n x γ.
  Proof.
    iIntros (H1) "[Hauth Hauth']".
    rewrite /hash_view_auth/hash_view_frag.
    iMod (ghost_map_insert_persist with "[$]") as "[$ #$]"; first done.
    iModIntro. rewrite big_sepM_insert; last done. by iFrame.
  Qed.
End hash_view_impl.


Class hvG1 Σ := {hvG1_ghost_mapG :: ghost_mapG Σ nat nat}. 
Program Definition hv_impl `{!conerisGS Σ} : hash_view :=
  {|
    hvG := hvG1;
    hv_name := gname;
    hv_auth _ m γ := hash_view_auth m γ;
    hv_frag _ k v γ := hash_view_frag k v γ
  |}.
Next Obligation.
  rewrite /hash_view_auth.
  iIntros. iMod ghost_map_alloc_empty as "[% ?]".
  iFrame. by rewrite big_sepM_empty.
Qed.
Next Obligation.
  simpl. iIntros.
  by iApply hash_view_auth_duplicate_frag.
Qed.
Next Obligation.
  simpl. iIntros.
  by iApply hash_view_auth_frag_agree.
Qed.
Next Obligation.
  simpl.
  iIntros (???????) "H1 H2".
  rewrite /hash_view_frag.
  by iCombine "H1 H2" gives "[? ->]".
Qed.
Next Obligation.
  simpl.
  iIntros.
  by iApply hash_view_auth_insert.
Qed.
