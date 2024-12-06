From stdpp Require Export fin_maps.
From iris.algebra Require Import excl_auth numbers gset_bij.
From clutch.coneris Require Import coneris lib.map hocap_rand abstract_tape hash_view_interface.
Set Default Proof Using "Type*".

Section seq_hash_impl.

  Context `{Hcon:conerisGS Σ, r1:!@rand_spec Σ Hcon, L:!randG Σ,
              hv1: !@hash_view Σ Hcon, L':!hvG Σ, HinG': abstract_tapesGS Σ}.

  Variable val_size : nat.

  (* A hash function's internal state is a map from previously queried keys to their hash value *)
  Definition init_hash_state : val := init_map.

  (* To hash a value v, we check whether it is in the map (i.e. it has been previously hashed).
     If it has we return the saved hash value, otherwise we draw a hash value and save it in the map *)
  Definition compute_hash_specialized hm : val :=
    λ: "v" "α",
      match: get hm "v" with
      | SOME "b" => "b"
      | NONE =>
          let: "b" := (rand_tape "α" #val_size) in
          set hm "v" "b";;
          "b"
      end.
  Definition compute_hash : val :=
    λ: "hm" "v" "α",
      match: get "hm" "v" with
      | SOME "b" => "b"
      | NONE =>
          let: "b" := (rand_tape "α" #val_size) in
          set "hm" "v" "b";;
          "b"
      end.

  (* init_hash returns a hash as a function, basically wrapping the internal state
     in the returned function *)
  Definition init_hash : val :=
    λ: "_",
      let: "hm" := init_hash_state #() in
      compute_hash "hm".

  Definition allocate_tape : val :=
    λ: "_",
      rand_allocate_tape #val_size.


  Definition hashfun f m (tape_m: gmap _ _) γ: iProp Σ :=
    ∃ (hm : loc), ⌜ f = compute_hash_specialized #hm ⌝ ∗
                  map_list hm ((λ b, LitV (LitInt (Z.of_nat b))) <$> m) ∗
                  ⌜map_Forall (λ ind i, (0<= i <=val_size)%nat) m⌝ ∗
                  (* the tapes*)
                  ● ((λ x, (val_size, x))<$>tape_m) @ γ ∗
                  [∗ map] α ↦ t ∈ tape_m,  rand_tapes (L:=L) α (val_size, t)
  .

  Definition tape_m_elements (tape_m : gmap val (list nat)) :=
    concat (map_to_list tape_m).*2.

  Definition hash_tape α ns γ:=
    (α ◯↪N (val_size; ns) @ γ)%I .
  
  Definition coll_free_hashfun f m tape_m γ1 γ2: iProp Σ :=
    hashfun f m tape_m γ1 ∗ hv_auth (L:=L') m γ2 ∗
    ⌜NoDup (tape_m_elements tape_m ++ (map_to_list m).*2)⌝.

  Lemma coll_free_hashfun_implies_hashfun f m γ1 γ2 tape_m:
    coll_free_hashfun f m tape_m γ1 γ2 -∗ hashfun f m tape_m γ1.
  Proof.
    by iIntros "[??]".
  Qed.

  #[global] Instance timeless_hashfun f m tape_m γ:
    Timeless (hashfun f m tape_m γ).
  Proof. apply _. Qed.

  #[global] Instance timeless_hashfun_amortized f m tape_m γ1 γ2:
    Timeless (coll_free_hashfun f m tape_m γ1 γ2).
  Proof. apply _. Qed.

  Lemma coll_free_hashfun_implies_coll_free f m tape_m γ1 γ2:
    coll_free_hashfun f m tape_m γ1 γ2-∗ ⌜coll_free m⌝.
  Proof.
    iIntros "(?&?&?)".
    by iApply hv_auth_coll_free.
  Qed.

  Lemma hashfun_implies_bounded_range f m tape_m γ idx x:
    hashfun f m tape_m γ -∗ ⌜m!!idx = Some x⌝ -∗ ⌜(0<=x<=val_size)%nat⌝.
  Proof.
    iIntros "(%&->&?&%K&?&?) %".
    iPureIntro.
    by eapply map_Forall_lookup_1 in K.
  Qed.

  Lemma coll_free_hashfun_implies_bounded_range f m tape_m idx x γ1 γ2:
    coll_free_hashfun f m tape_m γ1 γ2 -∗ ⌜m!!idx = Some x⌝ -∗ ⌜(0<=x<=val_size)%nat⌝.
  Proof.
    iIntros "(H&?) %".
    by iApply (hashfun_implies_bounded_range with "[$]").
  Qed.

  Lemma wp_init_hash E :
    {{{ True }}}
      init_hash #() @ E
    {{{ f, RET f; ∃ γ1 γ2, |={E}=> coll_free_hashfun f ∅ ∅ γ1 γ2}}}.
  Proof.
    rewrite /init_hash.
    iIntros (Φ) "_ HΦ".
    wp_pures. rewrite /init_hash_state.
    wp_apply (wp_init_map with "[//]").
    iIntros (?) "Hm". wp_pures.
    rewrite /compute_hash. wp_pures.
    iDestruct hv_auth_init as ">(%γ2 & Hview)".
    iMod (abstract_tapes_alloc ∅) as "(%γ1&Htauth&Htape)".
    iApply "HΦ". repeat iModIntro. rewrite /coll_free_hashfun. iFrame.
    iModIntro. repeat iSplit; try done.
    rewrite /tape_m_elements!map_to_list_empty concat_nil/=. iPureIntro.
    constructor.
  Qed.

  Lemma coll_free_insert (m : gmap nat nat) (n : nat) (z : nat) :
    m !! n = None ->
    coll_free m ->
    Forall (λ x, z ≠ snd x) (map_to_list m) ->
    coll_free (<[ n := z ]>m).
  Proof.
    intros Hnone Hcoll HForall.
    intros k1 k2 Hk1 Hk2 Heq.
    apply lookup_insert_is_Some' in Hk1.
    apply lookup_insert_is_Some' in Hk2.
    destruct (decide (n = k1)).
    - destruct (decide (n = k2)); simplify_eq; auto.
      destruct Hk2 as [|Hk2]; auto.
      rewrite lookup_total_insert in Heq.
      rewrite lookup_total_insert_ne // in Heq.
      apply lookup_lookup_total in Hk2.
      rewrite -Heq in Hk2.
      eapply (Forall_iff (uncurry ((λ (k : nat) (v : nat), z ≠ v)))) in HForall; last first.
      { intros (?&?); eauto. }
      eapply map_Forall_to_list in HForall.
      rewrite /map_Forall in HForall.
      eapply HForall in Hk2; congruence.
    - destruct (decide (n = k2)); simplify_eq; auto.
      {
        destruct Hk1 as [|Hk1]; auto.
        rewrite lookup_total_insert in Heq.
        rewrite lookup_total_insert_ne // in Heq.
        apply lookup_lookup_total in Hk1.
        rewrite Heq in Hk1.
        eapply (Forall_iff (uncurry ((λ (k : nat) (v : nat), z ≠ v)))) in HForall; last first.
        { intros (?&?); eauto. }
        eapply map_Forall_to_list in HForall.
        rewrite /map_Forall in HForall.
        eapply HForall in Hk1; congruence.
      }
      rewrite ?lookup_total_insert_ne // in Heq.
      destruct Hk1 as [|Hk1]; try congruence; [].
      destruct Hk2 as [|Hk2]; try congruence; [].
      apply Hcoll; eauto.
  Qed.


  Lemma wp_hashfun_prev E f m (n : nat) (b : nat) tape_m γ (α:loc) :
    m !! n = Some b →
    {{{ hashfun f m tape_m γ }}}
      f #n #α @ E
    {{{ RET #b; hashfun f m tape_m γ }}}.
  Proof.
    iIntros (Hlookup Φ) "Hhash HΦ".
    iDestruct "Hhash" as (hm ->) "(H &Hbound&?&?)".
    rewrite /compute_hash_specialized.
    wp_pures.
    wp_apply (wp_get with "[$]").
    iIntros (vret) "(Hhash&->)".
    rewrite lookup_fmap Hlookup /=. wp_pures. iModIntro. iApply "HΦ".
    iExists _. eauto.
    by iFrame.
  Qed.

  
  Lemma wp_coll_free_hashfun_prev E f m tape_m γ1 γ2 (n : nat) (b : nat) (α:loc) :
    m !! n = Some b →
    {{{ coll_free_hashfun f m tape_m γ1 γ2 }}}
      f #n #α @ E
    {{{ RET #b; coll_free_hashfun f m tape_m γ1 γ2 ∗ hv_frag (L:=L') n b γ2 }}}.
  Proof.
    iIntros (Hlookup Φ) "(Hhash & Hauth & %) HΦ".
    iDestruct "Hhash" as (hm ->) "(H & Hbound&?&?)".
    rewrite /compute_hash_specialized.
    wp_pures.
    wp_apply (wp_get with "[$]").
    iIntros (vret) "(Hhash&->)".
    rewrite lookup_fmap Hlookup /=. wp_pures.
    iMod (hv_auth_duplicate_frag with "[$]") as "[??]"; first done.
    iModIntro. iApply "HΦ". by iFrame.
  Qed.

  Lemma wp_coll_free_hashfun_frag_prev E f m tape_m γ1 γ2 (n : nat) (b : nat) (α:loc) :
    {{{ coll_free_hashfun f m tape_m γ1 γ2 ∗ hv_frag (L:=L') n b γ2}}}
      f #n #α @ E
    {{{ RET #b; coll_free_hashfun f m tape_m γ1 γ2 }}}.
  Proof.
    iIntros (Φ) "[(Hhash &?&?) #Hfrag] HΦ".
    iDestruct (hv_auth_frag_agree with "[$]") as "%".
    iApply (wp_coll_free_hashfun_prev with "[$]"); first done.
    iIntros "!> [??]".
    by iApply "HΦ".
  Qed.

  (** allocate spec*)
  Lemma wp_hash_allocate_tape f m tape_m γ1 γ2 E:
    {{{ coll_free_hashfun f m tape_m γ1 γ2 }}}
      allocate_tape #() @ E
      {{{ (α:val), RET α;
          coll_free_hashfun f m (<[α:=[]]> tape_m) γ1 γ2 ∗
          hash_tape α [] γ1
      }}}.
  Proof.
    iIntros (Φ) "((%&->&Hmap&%Hforall &Hauth &Htapes)&Hview&%) HΦ".
    rewrite /allocate_tape.
    wp_pures.
    iApply pgl_wp_fupd.
    wp_apply (rand_allocate_tape_spec with "[//]") as (v) "Htape".
    iApply "HΦ". rewrite /hash_tape.
    iFrame.
    iAssert (⌜((λ x : list nat, (val_size, x)) <$> tape_m) !! v = None⌝)%I as "%H0".
    { rewrite lookup_fmap fmap_None.
      destruct (tape_m!!v) eqn:K; last done.
      rewrite big_sepM_lookup; last done.
      iDestruct (rand_tapes_exclusive with "[$][$]") as "[]".
    }
    iMod (abstract_tapes_new with "[$]") as "[?$]"; first done.
    iModIntro.
    rewrite lookup_fmap fmap_None in H0.
    rewrite big_sepM_insert; last done.
    rewrite fmap_insert. iFrame.
    repeat iSplit; try done.
    iPureIntro.
    rewrite /tape_m_elements.
    eapply NoDup_Permutation_proper; last done.
    by rewrite map_to_list_insert/=.
  Qed.
  
  (* not the most general. Theoretically, you can even choose how to distribute the residue error*)
  Lemma coll_free_hash_presample f m tape_m γ1 γ2 α E (ε:nonnegreal) ns:
    coll_free_hashfun f m tape_m γ1 γ2 -∗
    hash_tape α ns γ1 -∗
    ↯ (nnreal_div (nnreal_nat (length (map_to_list m) + length (tape_m_elements tape_m))) (nnreal_nat(val_size+1))) -∗
    ↯ ε -∗
    state_update E E (∃ (n:nat),
          ↯ ((nnreal_div (nnreal_nat(val_size+1)) (nnreal_nat (S val_size - (length (map_to_list m) + length (tape_m_elements tape_m))))) *ε) ∗
          hash_tape α (ns++[n]) γ1 ∗
          coll_free_hashfun f m (<[α:=ns++[n]]> tape_m) γ1 γ2
      ).
  Proof.
    rewrite /hash_tape.
    iIntros "((%&->&Hmap&%Hforall &Hauth &Htapes)&Hview&%) Hfrag Herr1 Herr2".
    iDestruct (ec_valid with "[$Herr1]") as "%Hineq".
    iDestruct (abstract_tapes_agree with "[$][$]") as "%Hlookup".
    rewrite lookup_fmap fmap_Some in Hlookup.
    destruct Hlookup as (?&?&?).
    simplify_eq.
    iAssert (⌜Forall (λ i, 0<=i<=val_size)%nat (tape_m_elements tape_m)⌝)%I as "%Hforall2".
    { rewrite /tape_m_elements.
      rewrite Forall_concat Forall_fmap.
      iAssert (⌜Forall (uncurry (λ _ ns, Forall (λ i, 0<=i<=val_size)%nat ns)) (map_to_list tape_m)⌝)%I as "%K"; last first.
      { iPureIntro.
        eapply (List.Forall_impl); last done.
        intros []. by simpl.
      }
      rewrite -map_Forall_to_list.
      rewrite /map_Forall.
      iIntros (?? Hlookup).
      iDestruct (big_sepM_lookup with "[$]") as "?"; first apply Hlookup.
      iDestruct (rand_tapes_valid with "[$]") as "%".
      iPureIntro.
      eapply Forall_impl; first done.
      intros. simpl in *. lia.
    }
    iDestruct (big_sepM_insert_acc with "[$]") as "[Htapes1 Htapes2]"; first done.
    iDestruct (ec_combine with "[$]") as "Herr".
    pose (ε2 := (λ (x:fin (S val_size)), if bool_decide (fin_to_nat x ∈ tape_m_elements tape_m ++ (map_to_list m).*2)
                                         then 1 else ((nnreal_nat (val_size + 1) /
                                                         nnreal_nat (S val_size - (length (map_to_list m) + length (tape_m_elements tape_m))))%NNR * ε)
                )%R).
    iMod (rand_tapes_presample _ _ _ _ _ ε2 with "[$][$]") as "(%n&Herr&Htape)".
    - intros. rewrite /ε2.
      case_bool_decide; first lra.
      apply Rmult_le_pos; apply cond_nonneg.
    - rewrite /ε2.
      rewrite SeriesC_scal_l.
      erewrite (SeriesC_ext _ (λ x0 : fin (S val_size),
                                 (if bool_decide ((fin_to_nat x0) ∈ elements ((set_seq 0 (val_size+1))∖(list_to_set  (tape_m_elements tape_m ++ (map_to_list m).*2)):gset _))
                                  then (nnreal_nat (val_size + 1) /
                                          nnreal_nat (S val_size-(length (map_to_list m) + length (tape_m_elements tape_m))))%NNR * ε else 0)+
                                   (if bool_decide ((fin_to_nat x0) ∈ tape_m_elements tape_m ++ (map_to_list m).*2)
                                    then 1 else 0)))%R; last first.
      { simpl. intros n.
        case_bool_decide as H1; case_bool_decide as H2; try lra.
        - rewrite elem_of_elements elem_of_difference elem_of_list_to_set in H2.
          naive_solver.
        - rewrite elem_of_elements elem_of_difference elem_of_list_to_set in H2.
          exfalso. apply H2; split; last done.
          rewrite elem_of_set_seq.
          pose proof fin_to_nat_lt n. lia.
      }
      rewrite SeriesC_plus; [|apply ex_seriesC_finite..]. rewrite  Rmult_plus_distr_l.
      apply Rplus_le_compat.
      + replace (SeriesC _) with (SeriesC (λ x:nat, if
                                                    bool_decide
                                                      (x
                                                         ∈ elements
                                                         (set_seq 0 (val_size + 1)
                                                            ∖ list_to_set (tape_m_elements tape_m ++ (map_to_list m).*2):gset _))
                                                  then
                                                    (nnreal_nat (val_size + 1) /
                                                       nnreal_nat (S val_size-(length (map_to_list m) + length (tape_m_elements tape_m))))%NNR * ε
                                                  else 0))%R.
        * rewrite SeriesC_list_2; last apply NoDup_elements.
          rewrite -length_elements_size_gset size_difference.
          -- rewrite size_set_seq size_list_to_set; last done.
             rewrite app_length fmap_length S_INR/= plus_INR/=.
             right. rewrite -!Rmult_assoc. rewrite (Rmult_comm _ (val_size+1)).
             rewrite Rdiv_1_l Rmult_inv_r; last first.
             { pose proof pos_INR val_size. lra. }
             rewrite Rmult_1_l Rmult_comm -!Rmult_assoc.
             replace (val_size + 1)%nat with (S val_size) by lia.
             rewrite Nat.add_comm.
             rewrite Rmult_inv_r; first lra.
             replace 0%R with (INR 0) by done.
             destruct Hineq as [Hineq1 Hineq2].
             simpl in Hineq2.
             rewrite -Rdiv_def Rcomplements.Rlt_div_l in Hineq2; last first.
             { rewrite plus_INR. pose proof pos_INR val_size. simpl. lra. }
             apply not_INR.
             intro Hcontra.
             assert (val_size + 1 <=(length (map_to_list m) + length (tape_m_elements tape_m)))%nat by lia.
             apply le_INR in H1.
             lra.
          -- rewrite elem_of_subseteq.
             intros y. rewrite elem_of_list_to_set elem_of_set_seq elem_of_app.
             intros [H1|H1].
             ++ rewrite Forall_forall in Hforall2.
                apply Hforall2 in H1. lia.
             ++ rewrite /map_Forall in Hforall.
                rewrite elem_of_list_fmap in H1.
                destruct H1 as ([]&->&H1).
                rewrite elem_of_map_to_list in H1.
                apply Hforall in H1. simpl. lia.
        * set (f:=(λ x0 : nat,
                     if
                       bool_decide
                         (x0 ∈ elements
                            (set_seq 0 (val_size + 1) ∖ list_to_set (tape_m_elements tape_m ++ (map_to_list m).*2)))
                     then
                       (NNRbar_to_real
                          (NNRbar.Finite
                             (nnreal_nat (val_size + 1) /
                                nnreal_nat (S val_size - (length (map_to_list m) + length (tape_m_elements tape_m))))%NNR) *
                          NNRbar_to_real (NNRbar.Finite ε))%R
                     else 0%R)).
          erewrite (SeriesC_ext (λ _:fin _, _) (λ x, f (fin_to_nat x))).
          -- rewrite -SeriesC_nat_bounded_fin.
             apply SeriesC_ext.
             intros. case_bool_decide; first done.
             rewrite /f. rewrite bool_decide_eq_false_2; first done.
             rewrite elem_of_elements elem_of_difference elem_of_set_seq. lia.
          -- naive_solver.
      + set (f:=(λ x0 : nat,
                   if bool_decide ( x0 ∈ tape_m_elements tape_m ++ (map_to_list m).*2) then 1 else 0)%R).
        erewrite (SeriesC_ext _ (λ x, f (fin_to_nat x))); last done.
        rewrite -SeriesC_nat_bounded_fin.
        erewrite (SeriesC_ext _ f).
        -- rewrite /f. rewrite S_INR.
           rewrite SeriesC_list_2; last done.
           simpl.
           rewrite app_length fmap_length. right. rewrite Nat.add_comm.
           rewrite !plus_INR/=. lra.
        -- rewrite /f.
           intros. case_bool_decide; first done.
           rewrite bool_decide_eq_false_2; first done.
           rewrite elem_of_app.
           intros [Hcontra|Hcontra].
           ++ rewrite Forall_forall in Hforall2.
              apply Hforall2 in Hcontra. lia.
           ++ rewrite elem_of_list_fmap in Hcontra.
              destruct Hcontra as ([]&->&Hcontra).
              rewrite elem_of_map_to_list in Hcontra.
              rewrite /map_Forall in Hforall.
              apply Hforall in Hcontra. 
              simpl in *. lia.
    - rewrite /ε2. case_bool_decide as H'; first by iDestruct (ec_contradict with "[$]") as "[]".
      iMod (abstract_tapes_presample _ _ _ _ _ n with "[$][$]") as "[Hauth Hfrag]".
      iDestruct ("Htapes2" with "[$]") as "$".
      rewrite fmap_insert; iFrame.
      iPureIntro; split; try done.
      rewrite /tape_m_elements.
      apply NoDup_Permutation_proper with (((fin_to_nat n)::tape_m_elements tape_m) ++ (map_to_list m).*2).
      + apply Permutation_app_tail.
        rewrite <-insert_delete_insert.
        erewrite <-(insert_delete tape_m) at 2; last done.
        rewrite /tape_m_elements.
        rewrite !map_to_list_insert; try apply lookup_delete.
        rewrite fmap_cons. simpl.
        rewrite app_comm_cons. apply Permutation_app_tail.
        by rewrite -Permutation_cons_append.
      + rewrite -app_comm_cons.
        by apply NoDup_cons.
  Qed.

  Lemma wp_insert_no_coll E f m (n : nat) tape_m x xs γ1 γ2 α:
    m !! n = None →
    {{{ coll_free_hashfun f m tape_m γ1 γ2 ∗ hash_tape α (x::xs) γ1
    }}}
      f #n α @ E
      {{{ RET #x; coll_free_hashfun f (<[ n := x ]>m) (<[α:=xs]> tape_m) γ1 γ2 ∗
                  hv_frag (L:=L') n x γ2 ∗
                  hash_tape α xs γ1
      }}}.
  Proof.
    iIntros (Hlookup Φ) "[Hhash Htape] HΦ".
    iDestruct "Hhash" as "((%h&->&Hmap & %Hbound&Hauth&Htapes)&Hview&%Hnodup)".
    rewrite /compute_hash_specialized.
    wp_pures.
    wp_apply (wp_get with "[$]").
    iIntros (vret) "(Hhash&->)".
    iDestruct (abstract_tapes_agree with "[$][$]") as "%H".
    rewrite lookup_fmap_Some in H.
    destruct H as (?&?&?). simplify_eq.
    rewrite lookup_fmap Hlookup /=. wp_pures.
    iDestruct (big_sepM_insert_acc with "[$]") as "[Htapes1 Htapes2]"; first done.
    iDestruct (rand_tapes_valid with "[$]") as "%H'".
    inversion H'; simplify_eq.
    wp_apply (rand_tape_spec_some with "[$]") as "Htapes1".
    wp_pures.
    wp_apply (wp_set with "Hhash").
    iIntros "Hlist".
    wp_pures.
    iMod (hv_auth_insert _ _ x with "[$]") as "[??]".
    { done. }
    { rewrite NoDup_app in Hnodup.
      destruct Hnodup as (?&H1&?).
      rewrite List.Forall_forall.
      intros x'. rewrite -elem_of_list_In.
      specialize (H1 x). rewrite /not in H1 *.
      intros. subst. apply H1; last done.
      rewrite /tape_m_elements.
      rewrite elem_of_list_In.
      rewrite in_concat.
      exists (x'::xs); split; last by constructor.
      rewrite -elem_of_list_In.
      eapply elem_of_list_fmap_1_alt with (α, x'::xs); last done.
      by rewrite elem_of_map_to_list.
    }
    iMod (abstract_tapes_pop with "[$][$]") as "[Hauth Htape]".
    iModIntro.
    iDestruct ("Htapes2" with "[$]") as "Htapes".
    iApply "HΦ".
    iFrame.
    iSplit; first iExists _.
    - repeat iSplit; try done.
      rewrite !fmap_insert. iFrame.
      rewrite map_Forall_insert; last done.
      iSplit; first (iPureIntro; split; [lia|done]). done.
    - iPureIntro.
      eapply NoDup_Permutation_proper; last done.
      rewrite /tape_m_elements.
      rewrite (map_to_list_insert m); last done.
      erewrite <-insert_delete_insert.
      rewrite map_to_list_insert; last apply lookup_delete.
      replace tape_m with (<[α:=x::xs]> tape_m) at 2; last by apply insert_id.
      erewrite <-insert_delete_insert.
      rewrite map_to_list_insert; last apply lookup_delete.
      rewrite !fmap_cons.
      rewrite !concat_cons.
      simpl; by rewrite Permutation_middle.
  Qed.

End seq_hash_impl.



(* Section amortized_hash. *)

(*   Class amortized_hashG Σ := *)
(*     { *)
(*         amortized_hash_credit :: inG Σ (authR natR) ; *)
(*         amortized_hash_gset_bij :: inG Σ (gset_bijR nat nat) *)
(*       }. *)
       
(*   Context `{!conerisGS Σ, Hah: amortized_hashG Σ}. *)
(*   Variable val_size:nat. *)
(*   Variable max_hash_size : nat. *)
(*   Hypothesis max_hash_size_pos: (0<max_hash_size)%nat. *)
(*   (* Variable Hineq : (max_hash_size <= (val_size+1))%nat. *) *)
(*   Program Definition amortized_error : nonnegreal := *)
(*     mknonnegreal ((max_hash_size-1) /(2*(val_size + 1)))%R _. *)
(*   Next Obligation. *)
(*     pose proof (pos_INR val_size) as H. *)
(*     pose proof (pos_INR max_hash_size) as H'. *)
(*     apply Rcomplements.Rdiv_le_0_compat; try lra. *)
(*     assert (1 <= INR max_hash_size); try lra. *)
(*     replace 1 with (INR 1); last simpl; [by apply le_INR|done]. *)
(*   Qed. *)

  
(*   Definition hashfun_amortized f m γ: iProp Σ := *)
(*     ∃ (k : nat) (ε : nonnegreal), *)
(*       hashfun val_size f m ∗ *)
(*       ⌜k = size m⌝ ∗ *)
(*       ⌜ (ε.(nonneg) = (((max_hash_size-1) * k)/2 - sum_n_m (λ x, INR x) 0%nat (k-1)) / (val_size + 1))%R⌝ ∗ *)
(*       ↯ ε ∗ *)
(*       (** token *) *)
(*       own γ (● max_hash_size) ∗ *)
(*       own γ (◯ k)  *)
(*   . *)

  
(*   Definition coll_free_hashfun_amortized f m γ1 γ2: iProp Σ := *)
(*     hashfun_amortized f m γ1 ∗ *)
(*       (** gset_bij *) *)
(*       hash_view_auth m γ2. *)

(*   #[global] Instance timeless_coll_free_hashfun_amortized f m γ: *)
(*     Timeless (hashfun_amortized f m γ). *)
(*   Proof. apply _. Qed. *)


(*   Lemma coll_free_hashfun_amortized_implies_coll_free f m γ1 γ2: *)
(*     coll_free_hashfun_amortized f m γ1 γ2 -∗ ⌜coll_free m⌝. *)
(*   Proof. *)
(*     iIntros "[??]". *)
(*     by iApply hash_view_auth_coll_free.  *)
(*   Qed. *)

(*   Lemma hashfun_amortized_implies_bounded_range f m γ idx x: *)
(*     hashfun_amortized f m γ -∗ ⌜m!!idx = Some x⌝ -∗ ⌜(0<=x<=val_size)%nat⌝. *)
(*   Proof. *)
(*     iIntros "H %". *)
(*     iApply (hashfun_implies_bounded_range with "[H]"); [by iDestruct "H" as "(%&%&H&H')"|done]. *)
(*   Qed. *)

(*   Lemma coll_free_hashfun_amortized_implies_bounded_range f m γ1 γ2 idx x: *)
(*     coll_free_hashfun_amortized f m γ1 γ2 -∗ ⌜m!!idx = Some x⌝ -∗ ⌜(0<=x<=val_size)%nat⌝. *)
(*   Proof. *)
(*     iIntros "(H&?) %". *)
(*     by iApply (hashfun_amortized_implies_bounded_range with "[$]"). *)
(*   Qed. *)

(*   Lemma wp_init_hash_amortized E : *)
(*     {{{ True }}} *)
(*       init_hash val_size #() @ E *)
(*       {{{ f, RET f; |={E}=> ∃ γ1 γ2,  coll_free_hashfun_amortized f ∅ γ1 γ2 ∗ own γ1 (◯ max_hash_size) }}}. *)
(*   Proof. *)
(*     iIntros (Φ) "_ HΦ". *)
(*     wp_apply wp_init_hash; first done. *)
(*     iIntros (f) "(%γ2&H)". *)
(*     iApply "HΦ". *)
(*     iMod ec_zero. *)
(*     iMod "H". *)
(*     iMod (own_alloc (● max_hash_size ⋅ ◯ (0+max_hash_size)%nat)) as (γ1) "[H● [? H◯]]"; first (simpl; by apply auth_both_valid_2). *)
(*     iModIntro. *)
(*     iExists _, _. *)
(*     iSplitR "H◯"; last done. *)
(*     iDestruct "H" as "[??]". *)
(*     (* iExists 0%nat, nnreal_zero. *) *)
(*     iFrame. *)
(*     iExists nnreal_zero. *)
(*     repeat (iSplit; [done|]). iFrame. *)
(*     iPureIntro. *)
(*     simpl. *)
(*     replace (sum_n_m _ _ _) with 0; first lra. *)
(*     rewrite sum_n_n. by simpl. *)
(*   Qed. *)


(*   Lemma hashfun_amortized_hashfun f m γ: ⊢ hashfun_amortized f m γ -∗ hashfun val_size f m. *)
(*   Proof. *)
(*     by iIntros "(%&%&?&?)". *)
(*   Qed. *)

(*   Lemma wp_hashfun_prev_amortized E f m γ (n : nat) (b : nat) : *)
(*     m !! n = Some b → *)
(*     {{{ hashfun_amortized f m γ }}} *)
(*       f #n @ E *)
(*       {{{ RET #b; hashfun_amortized f m γ}}}. *)
(*   Proof. *)
(*     iIntros (Hlookup Φ) "(%&%&Hhash&->&%&Herr) HΦ". *)
(*     wp_apply (wp_hashfun_prev with "[$Hhash]"); [done|]. *)
(*     iIntros "H". iApply "HΦ". *)
(*     iExists _, _. iFrame. naive_solver. *)
(*   Qed. *)

(*   Lemma wp_coll_free_hashfun_prev_amortized E f m γ1 γ2 (n : nat) (b : nat) : *)
(*     m !! n = Some b → *)
(*     {{{ coll_free_hashfun_amortized f m γ1 γ2 }}} *)
(*       f #n @ E *)
(*       {{{ RET #b; coll_free_hashfun_amortized f m γ1 γ2 ∗ hash_view_frag n b γ2 }}}. *)
(*   Proof. *)
(*     iIntros (Hlookup Φ) "(H & Hauth) HΦ". *)
(*     iMod (hash_view_auth_duplicate_frag with "[$]") as "[??]"; first done. *)
(*     wp_apply (wp_hashfun_prev_amortized with "[$]"); [done|]. *)
(*     iIntros "H". iApply "HΦ". *)
(*     by iFrame.  *)
(*   Qed. *)

  
(*   Lemma wp_coll_free_hashfun_prev_frag_amortized E f m γ1 γ2 (n : nat) (b : nat) : *)
(*     {{{ coll_free_hashfun_amortized f m γ1 γ2 ∗ hash_view_frag n b γ2 }}} *)
(*       f #n @ E *)
(*       {{{ RET #b; coll_free_hashfun_amortized f m γ1 γ2 }}}. *)
(*   Proof. *)
(*     iIntros (Φ) "([??] & #H') HΦ". *)
(*     iDestruct (hash_view_auth_frag_agree with "[$]") as "%". *)
(*     iApply (wp_coll_free_hashfun_prev_amortized with "[$]"); first done. *)
(*     iIntros "!> [??]". *)
(*     by iApply "HΦ". *)
(*   Qed. *)

(*   Lemma amortized_inequality (k : nat): *)
(*     (k <= max_hash_size)%nat -> *)
(*     0 <= ((max_hash_size-1) * k / 2 - sum_n_m (λ x : nat, INR x) 0 (k - 1)) / (val_size + 1). *)
(*   Proof. *)
(*     intros H. *)
(*     pose proof (pos_INR max_hash_size) as H1. *)
(*     pose proof (pos_INR val_size) as H2. *)
(*     pose proof (pos_INR k) as H3. *)
(*     apply Rcomplements.Rdiv_le_0_compat; last lra. *)
(*     assert (sum_n_m (λ x : nat, INR x) 0 (k - 1) = (k-1)*k/2) as ->. *)
(*     - clear. *)
(*       induction k. *)
(*       + simpl. rewrite sum_n_n. *)
(*         rewrite Rmult_0_r. by assert (0/2 = 0) as -> by lra. *)
(*       + clear. induction k. *)
(*         * simpl. rewrite sum_n_n. *)
(*           replace (_-_) with 0 by lra. *)
(*           rewrite Rmult_0_l. by assert (0/2 = 0) as -> by lra. *)
(*         * assert (S (S k) - 1 = S (S k - 1))%nat as -> by lia. *)
(*           rewrite sum_n_Sm; last lia. *)
(*           rewrite IHk. *)
(*           replace (plus _ _) with (((S k - 1) * S k / 2) + (S (S k - 1))) by done. *)
(*           assert (∀ k, (INR (S k) - 1) = (INR k)) as H'. *)
(*           { intros. simpl. case_match; first replace (1 - 1) with 0 by lra. *)
(*             - done. *)
(*             - by replace (_+1-1) with (INR (S n)) by lra. *)
(*           } *)
(*           rewrite !H'. *)
(*           replace (S k - 1)%nat with (k)%nat by lia. *)
(*           assert (k * (S k) + S k + S k = S k * S (S k)); last lra. *)
(*           assert (k * S k + S k + S k = S k * (k+1+1)) as ->; try lra. *)
(*           assert (k+1+1 = S (S k)). *)
(*           -- rewrite !S_INR. lra. *)
(*           -- by rewrite H. *)
(*     - rewrite -!Rmult_minus_distr_r. *)
(*       apply Rcomplements.Rdiv_le_0_compat; try lra. *)
(*       apply Rmult_le_pos; try lra. *)
(*       assert (INR k <= INR max_hash_size); try lra. *)
(*       by apply le_INR. *)
(*   Qed. *)

(*   Lemma hashfun_amortized_token_ineq f m γ: *)
(*     hashfun_amortized f m γ -∗ own γ (◯ 1%nat) -∗ ⌜(size m < max_hash_size)%nat⌝. *)
(*   Proof. *)
(*     iIntros "H1 H2". *)
(*     destruct (Nat.lt_ge_cases (size m) max_hash_size); first done. *)
(*     iDestruct "H1" as "(%&%&_&->&_&_&H1&H3)". *)
(*     iCombine "H2 H3" as "H2". *)
(*     iCombine "H1 H2" gives "H'". *)
(*     rewrite auth_both_validI. *)
(*     iDestruct "H'" as "[[% %H']_]". simpl in *. *)
(*     rewrite nat_op in H'. lia. *)
(*   Qed. *)

(*   Lemma wp_insert_new_amortized E f m γ1 γ2  (n : nat) : *)
(*     m !! n = None → *)
(*     (size m < max_hash_size)%nat -> *)
(*     {{{ coll_free_hashfun_amortized f m γ1 γ2 ∗ ↯ amortized_error ∗ own γ1 (◯ 1%nat)}}} *)
(*       f #n @ E *)
(*       {{{ (v : nat), RET #v; coll_free_hashfun_amortized f (<[ n := v ]>m) γ1 γ2 ∗ hash_view_frag n v γ2}}}. *)
(*   Proof. *)
(*     iIntros (Hlookup Hineq Φ) "([Hhash Hview] & Herr & Htoken) HΦ". *)
(*     iDestruct (hashfun_amortized_token_ineq with "[$Hhash][$]") as "%". *)
(*     iDestruct "Hhash" as (k ε) "(H&->&%H0&Herr'& Hauth &Hfrag)". *)
(*     set (ε' := (((max_hash_size-1) * size (<[n:=0%nat]> m) / 2 - *)
(*                    sum_n_m (λ x, INR x) 0%nat (size (<[n:=0%nat]> m) - 1)) / (val_size + 1))). *)
(*     assert (0 <= ε') as Hε'. *)
(*     { apply amortized_inequality. *)
(*       rewrite map_size_insert. *)
(*       case_match => /=; lia. } *)
(*     set (ε'' := mknonnegreal _ Hε'). *)

(*     iAssert (↯ (nnreal_div (nnreal_nat (size m)) (nnreal_nat (val_size + 1))) ∗ ↯ ε'')%I *)
(*       with "[Herr Herr']" as "[Hε Herr]". *)
(*     - iApply ec_split; [apply cond_nonneg|apply cond_nonneg|]. *)
(*       iCombine "Herr Herr'" as "H". *)
(*       iApply (ec_eq with "[$]"). *)
(*       rewrite /ε'' /ε'. *)
(*       simpl. rewrite H0. rewrite map_size_insert_None //. *)
(*       remember (size m) as k. *)
(*       remember (val_size + 1) as v. *)
(*       remember (max_hash_size) as h. *)
(*       assert (∀ x y, x/y = x*/y) as Hdiv. *)
(*       { intros. lra. } *)
(*       destruct k. *)
(*       + simpl. rewrite sum_n_n. rewrite Rmult_0_l Rmult_0_r. *)
(*         replace (INR 0%nat) with 0; last done. *)
(*         rewrite !Rminus_0_r. *)
(*         replace (0/_/_) with 0; last lra. *)
(*         rewrite !Rplus_0_l. *)
(*         rewrite Rmult_1_r. *)
(*         rewrite !Hdiv. *)
(*         rewrite Rinv_mult. *)
(*         lra. *)
(*       + assert (forall k, S k - 1 = k)%nat as H' by lia. *)
(*         rewrite !H'. *)
(*         clear H'. *)
(*         rewrite sum_n_Sm; last lia. *)
(*         replace (plus _ (INR (S k))) with ((sum_n_m (λ x : nat, INR x) 0 k) + (S k)) by done. *)
(*         rewrite !Hdiv. *)
(*         rewrite !Rmult_minus_distr_r. *)
(*         rewrite (Rmult_plus_distr_r (sum_n_m _ _ _)). *)
(*         rewrite -!Rplus_assoc. *)
(*         rewrite Ropp_plus_distr. *)
(*         rewrite -!Rplus_assoc. *)
(*         assert ((h-1) * S k * / 2 * / v+ (h-1) * / (2 * v) = S k * / (val_size + 1)%nat + (h-1) * S (S k) * / 2 * / v  + - (S k * / v)); try lra. *)
(*         replace (INR((_+_)%nat)) with v; last first. *)
(*         { rewrite Heqv. rewrite -S_INR. f_equal. lia. } *)
(*         assert ( (h-1) * S k * / 2 * / v + (h-1) * / (2 * v) = (h-1) * S (S k) * / 2 * / v); try lra. *)
(*         replace (_*_*_*_) with ((h-1) * (S k) * /(2*v)); last first. *)
(*         { rewrite Rinv_mult. lra. } *)
(*         replace (_*_*_*_) with ((h-1) * (S(S k)) * /(2*v)); last first. *)
(*         { rewrite Rinv_mult. lra. } *)
(*         rewrite -Rdiv_plus_distr. *)
(*         rewrite Hdiv. *)
(*         f_equal. *)
(*         rewrite -{2}(Rmult_1_r (h-1)). *)
(*         rewrite -Rmult_plus_distr_l. *)
(*         f_equal. *)
(*     - wp_apply (wp_insert_no_coll with "[H Hε Hview]"); [done|..]. *)
(*       + rewrite map_to_list_length. iFrame.  *)
(*       + iIntros (v) "[[??] ?]". *)
(*         iApply "HΦ". *)
(*         iCombine "Hfrag Htoken" as "Hfrag". *)
(*         iFrame. *)
(*         rewrite !map_size_insert Hlookup. *)
(*         iPureIntro. split; first lia. *)
(*         rewrite /ε''. simpl. rewrite /ε'. do 3 f_equal. *)
(*         all: repeat rewrite map_size_insert Hlookup; try (simpl; lia). *)
(*         rewrite S_INR plus_INR; simpl; lra. *)
(*   Qed. *)

(*   Lemma wp_insert_amortized E f m γ1 γ2 (n : nat) : *)
(*     {{{ coll_free_hashfun_amortized f m γ1 γ2 ∗ ↯ amortized_error ∗ own γ1 (◯ 1%nat)}}} *)
(*       f #n @ E *)
(*       {{{ (v : nat), RET #v; ∃ m', coll_free_hashfun_amortized f m' γ1 γ2 ∗ ⌜m'!!n = Some v⌝ ∗ ⌜(size m' <= S $ size(m))%nat⌝ ∗ ⌜m⊆m'⌝ ∗ hash_view_frag n v γ2 }}}. *)
(*   Proof. *)
(*     iIntros (Φ) "([Hh Hview]& Herr & Hfrag) HΦ". *)
(*     iDestruct (hashfun_amortized_token_ineq with "[$Hh][$]") as "%". *)
(*     destruct (m!!n) eqn:Heq. *)
(*     - wp_apply (wp_coll_free_hashfun_prev_amortized with "[$Hh $Hview]") as "[??]"; first done. *)
(*       iIntros. iApply "HΦ". *)
(*       iExists _; iFrame. *)
(*       repeat iSplit; try done. iPureIntro; lia. *)
(*     - wp_apply (wp_insert_new_amortized with "[$Hh $Herr $Hfrag $Hview]"); try done. *)
(*       iIntros (?) "[??]"; iApply "HΦ". *)
(*       iExists _; iFrame. iPureIntro. repeat split. *)
(*       + rewrite lookup_insert_Some. naive_solver. *)
(*       + rewrite map_size_insert. case_match; try (simpl; lia). *)
(*       + by apply insert_subseteq. *)
(*   Qed. *)

  
  
(* End amortized_hash. *)

  
