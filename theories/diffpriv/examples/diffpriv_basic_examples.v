From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import adequacy diffpriv proofmode.

Section wp_example.
  Context `{!diffprivGS Σ}.

  #[local] Open Scope R.

  Fact wp_laplace_diffpriv (loc loc' : Z)
    (num den : Z) K :
    0 < IZR num / IZR den →
    let e := (λ: "loc", Laplace #num #den "loc")%E in
    {{{ ⤇ fill K (e #loc') ∗ ↯ (IZR (Z.abs (loc - loc')) * (IZR num / IZR den)) }}}
      (e #loc)%E
      {{{ (z : Z), RET #z; ⤇ fill K (Val #z) }}}.
  Proof.
    iIntros (???) "(f' & ε) post". subst e.
    tp_pures.
    wp_pures.
    tp_bind (Laplace _ _ _).
    iApply (wp_couple_laplace _ _ 0%Z with "[$]") => //.
    setoid_rewrite Z.add_0_r. done.
  Qed.

  Definition wp_sensitive (f : expr) (c : R) := ∀ (c_pos : 0 <= c) K (x x' : Z),
    {{{ ⤇ fill K (f #x') }}}
      f #x
      {{{ (v : Z), RET #v; ∃ v' : Z, ⤇ fill K (Val #v') ∧ ⌜IZR (Z.abs (v - v')) <= c * IZR (Z.abs (x - x'))⌝ }}}.

  Definition wp_diffpriv (f : expr) ε := ∀ K c (x x' : Z), IZR (Z.abs (x - x')) <= c →
      {{{ ⤇ fill K (f #x') ∗ ↯ (c * ε) }}} f #x {{{ (z : Z), RET #z; ⤇ fill K (Val #z) }}}.

  Fact wp_lap_dipr (num den : Z) :
    0 < IZR num / IZR den →
    wp_diffpriv (λ: "loc", Laplace #num #den "loc")%E ((IZR num / IZR den)).
  Proof.
    intros. rewrite /wp_diffpriv. intros K c x x' adj.
    iIntros (φ) "[f' ε] hφ".
    opose proof (wp_laplace_diffpriv x x' num den _ _) as h => //. simpl in h.
    iPoseProof (h φ with "[f' ε]") as "h".
    { iFrame. iApply ec_weaken. 2: iFrame.
      split. 1: rewrite abs_IZR ; real_solver_partial. 1: apply Rabs_pos. 1: lra.
      apply Rmult_le_compat => //. 1: rewrite abs_IZR ; apply Rabs_pos. lra.
    }
    iApply "h". done.
  Qed.

  Fact sensitive_comp (g f : val) cg cf (cg_pos : 0 <= cg) (cf_pos : 0 <= cf) :
    wp_sensitive g cg → wp_sensitive f cf → wp_sensitive (λ:"x", g (f "x")) (cg * cf).
  Proof.
    rewrite /wp_sensitive. intros g_sens f_sens. intros. iIntros "f' hΦ".
    wp_pures. wp_bind (f _). tp_pures. tp_bind (f _).
    iApply (f_sens with "[$f']") => //.
    iIntros "!>" (fx) "(%fx' & gv' & %sens)".
    iApply (g_sens with "[$gv']") => //.
    iIntros "!>" (gfx) "(%gfx'' & vv' & %sens')".
    iApply "hΦ". iExists _. iFrame. iPureIntro.
    etrans => //.
    rewrite Rmult_assoc.
    eapply Rmult_le_compat_l => //.
  Qed.

  Fact diffpriv_diffpriv_comp (g f : val) εg εf (εg_pos : 0 <= εg) (εf_pos : 0 <= εf) :
    wp_diffpriv g εg → wp_diffpriv f εf → wp_diffpriv (λ:"x", g (f "x")) εf.
  Proof.
    rewrite /wp_sensitive/wp_diffpriv. intros g_dipr f_dipr. intros. iIntros "[gf' εf] hΦ".
    wp_pures. wp_bind (f _). tp_pures. tp_bind (f _).
    iApply (f_dipr with "[$gf' $εf]") => //. iNext. iIntros (?) "g'".
    iPoseProof (g_dipr K 0 z z) as "g_dipr".
    { rewrite !abs_IZR. replace (z-z)%Z with 0%Z by lia. rewrite Rabs_R0. done. }
    iMod ec_zero as "ε0".
    replace (0 * εg) with 0 by lra.
    iApply ("g_dipr" with "[$ε0 $g']"). done.
  Qed.

  Fact diffpriv_sensitive_comp (g f : val) ε c (c_pos : 0 <= c) : wp_diffpriv g ε → wp_sensitive f c → wp_diffpriv (λ:"x", g (f "x")) (c*ε).
  Proof.
    rewrite /wp_sensitive/wp_diffpriv. intros g_dipr f_sens. intros K c'. intros. iIntros "[f' ε] hΦ".
    wp_pures. wp_bind (f _). tp_pures. tp_bind (f _).
    iApply (f_sens with "[$f']") => //.
    iIntros "!>" (?) "(%v' & gv' & %sens)".
    iPoseProof (g_dipr K (c * c')) as "g_dipr".
    { etrans => //. apply Rmult_le_compat_l => //. }
    iApply ("g_dipr" with "[$gv' ε]") => //. rewrite (Rmult_comm c) Rmult_assoc. done.
  Qed.

  Fact ne_diffpriv_comp (g f : val) ε c (c_pos : 0 < c) (f_ne : c <= 1)
    : wp_diffpriv g ε → wp_sensitive f c → wp_diffpriv (λ:"x", f (g "x")) (ε/c).
  Proof.
    rewrite /wp_sensitive/wp_diffpriv. intros g_dipr f_sens. intros K c' ?? adj ?. intros. iIntros "[g ε] hΦ".
    wp_pures. wp_bind (g _). tp_pures. tp_bind (g _).
    iApply (g_dipr _ (c' / c) with "[$g ε]") => //. 2: rewrite Rmult_assoc ; iFrame.
    { transitivity (c' * 1). 1: lra. rewrite /Rdiv. apply Rmult_le_compat_l.
      { rewrite abs_IZR in adj. pose proof (Rabs_pos (IZR (x - x'))). lra. }
      rewrite -Rinv_1.
      apply Rinv_le_contravar. 1: lra. exact f_ne.
    }
    { rewrite /Rdiv. rewrite (Rmult_comm ε). done. }
    iNext. iIntros (?) "f'".
    iApply (f_sens with "[$f']"). 1: lra.
    iIntros "!>" (?) "(%v' & gv' & %ne)".
    iApply "hΦ".
    assert (v = v') as -> => //.
    move: ne. rewrite !abs_IZR. replace (z-z)%Z with 0%Z by lia. rewrite Rabs_R0.
    pose proof (Rabs_pos (IZR (v - v'))) as h. intros. assert (Rabs (IZR (v - v')) = 0) as h' by lra.
    rewrite -abs_IZR in h'. revert h'. apply Zabs_ind.
    - intros. assert (v - v' = 0)%Z by apply eq_IZR =>//. lia.
    - intros. assert (- (v - v') = 0)%Z by apply eq_IZR =>//. lia.
  Qed.

  Fact e_diffpriv_comp (g f : val) ε c (c_pos : 0 < c) (f_e : 1 <= c)
    : wp_diffpriv g ε → wp_sensitive f c → wp_diffpriv (λ:"x", f (g "x")) (ε * c).
  Proof.
    rewrite /wp_sensitive/wp_diffpriv. intros g_dipr f_sens. intros K c' ?? adj ?. intros. iIntros "[g ε] hΦ".
    wp_pures. wp_bind (g _). tp_pures. tp_bind (g _).
    iApply (g_dipr _ (c' * c) with "[$g ε]") => //. 2: rewrite Rmult_assoc ; iFrame.
    { transitivity (c' * 1). 1: lra. apply Rmult_le_compat_l.
      { rewrite abs_IZR in adj. pose proof (Rabs_pos (IZR (x - x'))). lra. }
      exact f_e.
    }
    { rewrite /Rdiv. rewrite (Rmult_comm ε). done. }
    iNext. iIntros (?) "f'".
    iApply (f_sens with "[$f']"). 1: lra.
    iIntros "!>" (?) "(%v' & gv' & %ne)".
    iApply "hΦ".
    assert (v = v') as -> => //.
    move: ne. rewrite !abs_IZR. replace (z-z)%Z with 0%Z by lia. rewrite Rabs_R0.
    pose proof (Rabs_pos (IZR (v - v'))) as h. intros. assert (Rabs (IZR (v - v')) = 0) as h' by lra.
    rewrite -abs_IZR in h'. revert h'. apply Zabs_ind.
    - intros. assert (v - v' = 0)%Z by apply eq_IZR =>//. lia.
    - intros. assert (- (v - v') = 0)%Z by apply eq_IZR =>//. lia.
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
  Definition count_query (num den : Z) : val := λ:"b", setsum (setmap (λ:"z", Laplace #num #den "z") (setmap over_40 "b")).

  (* By adding (num/den) Laplacian noise, we get equal results for both databases.
     NB: Since this is done for a specific pair of databases, it doesn't quite
     fit the notion of pure differential privacy defined at the meta-level. *)
  Lemma count_query_db : ∀ (num den : Z),
      (0 < IZR num / IZR den) ->
      {{{ ⤇ count_query num den db' ∗  ↯ (IZR num / IZR den) }}}
        count_query num den db
      {{{ z, RET #z; ⤇ #z }}}.
  Proof.
    intros. rewrite /wp_diffpriv. intros.
    iIntros "[f' ε] hΦ" ; iRevert "f'" ; iIntros "f'".
    rewrite {2}/count_query /over_40/setmap/setsum/age/db. wp_pures.
    rewrite /count_query /over_40/setmap/setsum/age/db ; tp_pures.

    wp_bind (Laplace _ _ _). tp_bind (Laplace _ _ _).
    iMod ec_zero as "ε0".
    iApply (wp_couple_laplace 1 1 0%Z with "[$ε0 $f']") => //.
    { rewrite {2}abs_IZR. replace (IZR (0 + 1 - 1)) with 0%R by easy. rewrite Rabs_R0. lra. }
    iNext. iIntros (z) "f'". simpl. tp_pures ; wp_pures.

    wp_bind (Laplace _ _ _). tp_bind (Laplace _ _ _).
    iApply (wp_couple_laplace 1 0 0%Z with "[$ε $f']") => //.
    { rewrite abs_IZR. replace (IZR (0 + 1 - 0)) with 1%R by easy. rewrite Rabs_R1. lra. }
    iNext. iIntros (z') "f'". simpl. tp_pures ; wp_pures.

    wp_bind (Laplace _ _ _). tp_bind (Laplace _ _ _).
    iMod ec_zero as "ε0".
    iApply (wp_couple_laplace 0 0 0%Z with "[$ε0 $f']") => //.
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
    (λ x, lim_exec ((λ:"loc", Laplace #num #den "loc")%E #x, σ))
    ε.
Proof.
  intros ε εpos.
  eapply (adequacy.wp_diffpriv diffprivΣ) ; eauto ; try lra.
  iIntros (????) "f' ε".
  iApply (wp_laplace_diffpriv _ _ _ _ [] with "[f' ε]") => //.
  2: eauto.
  iFrame.
  iApply ec_weaken. 2: iFrame.
  split.
  - apply Rmult_le_pos. 2: subst ε ; lra. apply IZR_le. lia.
  - etrans. 2: right ; apply Rmult_1_l. apply Rmult_le_compat_r. 1: lra. done.
Qed.

(* wp_diffpriv implies pure diffpriv *)
Fact wp_diffpriv_pure f ε (εpos : (0 < ε)%R) :
  (∀ `{diffprivGS Σ}, wp_diffpriv f ε)
  →
    ∀ σ,
    diffpriv_pure
      (λ x y, IZR (Z.abs (x - y)))
      (λ x, lim_exec (f #x, σ))
      ε.
Proof.
  intros hwp ?.
  eapply (adequacy.wp_diffpriv diffprivΣ) ; eauto ; try lra.
  iIntros (????) "f' ε".
  iApply (hwp _ _ [] 1%R with "[$f' ε]") => //. 1: rewrite Rmult_1_l ; done.
  iNext. iIntros. iExists _. eauto.
Qed.
