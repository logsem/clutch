From clutch.common Require Import inject.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import adequacy diffpriv proofmode.

Section wp_example.
  Context `{!diffprivGS Σ}.

  #[local] Open Scope R.

  Fact wp_laplace_diffpriv (loc loc' : Z)
    (num den : Z) K :
    0 < IZR num / IZR den →
    let e := (λ: "loc", Laplace #num #den "loc" #())%E in
    {{{ ⤇ fill K (e #loc') ∗ ↯m (IZR (Z.abs (loc - loc')) * (IZR num / IZR den)) }}}
      (e #loc)%E
      {{{ (z : Z), RET #z; ⤇ fill K (Val #z) }}}.
  Proof.
    iIntros (???) "(f' & ε) post". subst e.
    tp_pures.
    wp_pures.
    tp_bind (Laplace _ _ _ _).
    iApply (hoare_couple_laplace _ _ 0%Z with "[$]") => //.
    setoid_rewrite Z.add_0_r. done.
  Qed.

  Definition ID := Fst.
  Definition age := Snd.
  (* Two example databases with three rows each containing a ID number and an age. *)
  Definition db : val := ( (#3, #12), (#1, #42), (#0, #57) ).
  Definition db' : val := ( (#3, #12), (#2, #24), (#0, #57) ).

  (* If we count the database entries with age over 40, the results we get for db and db' differ by 1. *)
  Definition over_40 : val := λ:"r", if: #40 < age "r" then #1 else #0.
  Definition setmap : val := λ: "f" "db", ("f" (Fst (Fst "db")) , "f" (Snd (Fst "db")) , "f" (Snd "db")).
  Definition setsum : val := λ: "db", (Fst (Fst "db")) + (Snd (Fst "db")) + (Snd "db").
  Definition count_query (num den : Z) : val := λ:"b", setsum (setmap (λ:"z", Laplace #num #den "z" #()) (setmap over_40 "b")).

  (* By adding (num/den) Laplacian noise, we get equal results for both databases.
     NB: Since this is done for a specific pair of databases, it doesn't quite
     fit the notion of pure differential privacy defined at the meta-level. *)
  Lemma count_query_db : ∀ (num den : Z),
      (0 < IZR num / IZR den) ->
      {{{ ⤇ count_query num den db' ∗  ↯m (IZR num / IZR den) }}}
        count_query num den db
      {{{ z, RET #z; ⤇ #z }}}.
  Proof.
    intros. rewrite /hoare_diffpriv. intros.
    iIntros "[f' ε] hΦ" ; iRevert "f'" ; iIntros "f'".
    rewrite {2}/count_query /over_40/setmap/setsum/age/db. wp_pures.
    rewrite /count_query /over_40/setmap/setsum/age/db ; tp_pures.

    wp_bind (Laplace _ _ _ _). tp_bind (Laplace _ _ _ _).
    iMod ecm_zero as "ε0".
    iApply (hoare_couple_laplace 1 1 0%Z with "[$ε0 $f']") => //.
    { rewrite {2}abs_IZR. replace (IZR (0 + 1 - 1)) with 0%R by easy. rewrite Rabs_R0. lra. }
    iNext. iIntros (z) "f'". simpl. tp_pures ; wp_pures.

    wp_bind (Laplace _ _ _ _). tp_bind (Laplace _ _ _ _).
    iApply (hoare_couple_laplace 1 0 0%Z with "[$ε $f']") => //.
    { rewrite abs_IZR. replace (IZR (0 + 1 - 0)) with 1%R by easy. rewrite Rabs_R1. lra. }
    iNext. iIntros (z') "f'". simpl. tp_pures ; wp_pures.

    wp_bind (Laplace _ _ _ _). tp_bind (Laplace _ _ _ _).
    iMod ecm_zero as "ε0".
    iApply (hoare_couple_laplace 0 0 0%Z with "[$ε0 $f']") => //.
    { rewrite {2}abs_IZR. replace (IZR (0 + 0 - 0)) with 0%R by easy. rewrite Rabs_R0. lra. }
    iNext. iIntros (z'') "f'". simpl. tp_pures ; wp_pures.

    iApply "hΦ". iModIntro. assert ((z'' + 0 + (z' + 0) + (z + 0)) = z'' + z' + z)%Z as -> by lia. done.

  Qed.

  (* Definition hist_query (num den : Z) : val :=
       λ:"b", listmap (λ:"z", Laplace #num #den "z") (hist (setmap age "b")). *)

End wp_example.

(* The program (λ z . L(ε, z)) is ε-differentially private for ε = num/den. *)
Fact Laplace_diffpriv σ (num den : Z) :
  let ε := (IZR num / IZR den)%R in
  (0 < ε)%R →
  diffpriv_pure
    (λ x y, IZR (Z.abs (x - y)))
    (λ x, lim_exec ((λ:"loc", Laplace #num #den "loc" #())%E #x, σ))
    ε.
Proof.
  intros ε εpos.
  eapply diffpriv_approx_pure.
  eapply (adequacy.wp_diffpriv_Z diffprivΣ) ; eauto ; try lra.
  iIntros (????) "f' ε ?".
  iApply (wp_laplace_diffpriv _ _ _ _ [] with "[f' ε]") => //.
  2: eauto.
  iFrame.
  iApply ecm_weaken. 2: iFrame.
  split.
  - apply Rmult_le_pos. 2: subst ε ; lra. apply IZR_le. lia.
  - etrans. 2: right ; apply Rmult_1_l. apply Rmult_le_compat_r. 1: lra. done.
Qed.
