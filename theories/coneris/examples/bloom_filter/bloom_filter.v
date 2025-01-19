From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import gset_bij.
From clutch.coneris Require Import coneris par spawn spin_lock hash atomic lock concurrent_hash.
From clutch.coneris.lib Require Import list array.

Set Default Proof Using "Type*".

Section bloom_filter.

  Variable filter_size : nat.
  Variable num_hash : nat.
  (* Variable insert_num : nat. *)
  (* Variable max_hash_size : nat.*)
  (* Hypothesis max_hash_size_pos: (0<max_hash_size)%nat. *)

  Context `{!conerisGS Σ, HinG: inG Σ (gset_bijR nat nat)}.

  Search nonnegreal.

  Fixpoint fp_error (m l b : nat) : R :=
      (match m with
      | 0 => let fix fp_error_Z (l b : nat) : R :=
              match l with
              | 0 => pow (b/(filter_size + 1)) num_hash
              | S l' => (b / (filter_size + 1)) * fp_error_Z l' b + ((filter_size + 1 - b) / (filter_size + 1)) * fp_error_Z l' (S b)
              end
              in fp_error_Z l b
      | S m' => let fix fp_error_m (l b : nat) : R :=
                 match l with
                 | 0 => fp_error m' num_hash b
                 | S l' => (b / (filter_size + 1)) * fp_error_m l' b + ((filter_size + 1 - b) / (filter_size + 1)) * fp_error_m l' (S b)
                 end
               in fp_error_m l b
       end)%R.


  Lemma fp_error_Z_Z (m b : nat) : fp_error 0 0 b = pow (b/(filter_size + 1)) num_hash.
  Proof.
    done.
  Qed.

  Lemma fp_error_S_Z (m b : nat) : fp_error (S m) 0 b = fp_error m num_hash b.
  Proof.
    done.
  Qed.

  Lemma fp_error_m_S (m l b : nat) :
    fp_error m (S l) b = ((b / (filter_size + 1)) * fp_error m l b + ((filter_size + 1 - b) / (filter_size + 1)) * fp_error m l (S b))%R.
  Proof.
    destruct m; done.
  Qed.

  Lemma fp_error_weaken (m l b : nat) :
    (fp_error 0 0 b <= fp_error m l b)%R.
  Admitted.

  Lemma fp_error_nonneg (m l b : nat) :
    (0 <= fp_error m l b)%R.
  Admitted.



  Definition init_bloom_filter : expr :=
    λ: "_" ,
      let: "hfuns" := list_seq_fun #0 #num_hash (λ: "_", init_hash filter_size #())%E in
      let: "arr" := array_init #(S filter_size) (λ: "x", #false)%E in
      let: "l" := ref ("hfuns", "arr") in
      "l".

  Definition insert_bloom_filter : expr :=
    λ: "l" "v" ,
      let, ("hfuns", "arr") := !"l" in
      list_iter (λ: "h",
          let: "i" := "h" "v" in
          "arr" +ₗ "i" <- #true) "hfuns".


  Definition lookup_bloom_filter : expr :=
    λ: "l" "v" ,
      let, ("hfuns", "arr") := !"l" in
      let: "res" := ref #true in
      list_iter (λ: "h",
          let: "i" := "h" "v" in
          if: !("arr" +ₗ "i") then #() else "res" <- #false) "hfuns";;
      !"res".


  Definition is_bloom_filter (l : loc) (els : gset nat) (rem : nat) : iProp Σ :=
    ∃ hfuns hs ms a arr (idxs : gset nat),
      ↯ (fp_error rem 0 (size idxs)) ∗
      l ↦ (hfuns, LitV (LitLoc a))%V ∗
        ⌜ is_list_HO hs hfuns ⌝ ∗
        ⌜ length hs = num_hash ⌝ ∗
        ([∗ list] k↦h;m ∈ hs;ms, hashfun filter_size h m) ∗
        ⌜ length arr = S filter_size ⌝ ∗
        (a ↦∗ arr) ∗
        ⌜ Forall (λ m, els = dom m) ms ⌝ ∗
        ⌜ forall e, e ∈ els -> Forall (λ m, (m !!! e) ∈ idxs ) ms ⌝ ∗
        ⌜ forall i, i ∈ idxs -> arr !! i = Some #true  ⌝ ∗
        ⌜ forall i, i ∈ idxs -> (i < S filter_size)%nat  ⌝ ∗
        ⌜ forall i, i < S filter_size -> i ∉ idxs -> arr !! i = Some #false  ⌝.


  Definition is_bloom_filter_partial (l : loc) (e_new : nat)
    (els : gset nat) (rem : nat) hs_new hs_old a : iProp Σ :=
    ∃ hfuns ms_new ms_old arr (idxs : gset nat),
      ↯ (fp_error rem (length hs_old) (size idxs)) ∗
      l ↦ (hfuns, LitV (LitLoc a))%V ∗
        ⌜ is_list_HO (hs_new ++ hs_old) hfuns ⌝ ∗
        ⌜ length (hs_new ++ hs_old) = num_hash ⌝ ∗
        ([∗ list] k↦h;m ∈ hs_new;ms_new, hashfun filter_size h m) ∗
        ([∗ list] k↦h;m ∈ hs_old;ms_old, hashfun filter_size h m) ∗
        ⌜ length arr = S filter_size ⌝ ∗
        (a ↦∗ arr) ∗
        ⌜ Forall (λ m, els = dom m) ms_old ⌝ ∗
        ⌜ Forall (λ m, ({[e_new]} ∪ els) = dom m) ms_new ⌝ ∗
        ⌜ forall e, e ∈ els -> Forall (λ m, (m !!! e) ∈ idxs ) ms_old ⌝ ∗
        ⌜ forall e, e ∈ ({[e_new]} ∪ els) ->
               Forall (λ m, (m !!! e) ∈ idxs ) ms_new ⌝ ∗
        ⌜ forall i, i ∈ idxs -> arr !! i = Some #true  ⌝ ∗
        ⌜ forall i, i ∈ idxs -> (i < S filter_size)%nat  ⌝ ∗
        ⌜ forall i, i < S filter_size -> i ∉ idxs -> arr !! i = Some #false  ⌝.

  Definition bloom_filter_to_partial l e_new els rem :
    is_bloom_filter l els (S rem) -∗
     ∃ hs a , is_bloom_filter_partial l e_new els rem [] hs a.
  Proof.
    iIntros "Hbf".
    iDestruct "Hbf" as (hfuns hs ms a arr idxs) "(Hl & Herr & %Hhfuns & %Hlenhs & Hhs & %HlenA & Ha & %Hms & %Hidxs & %Htrue & %Hbd & %Hfalse)".
    rewrite fp_error_S_Z.
    iExists hs, a.
    rewrite /is_bloom_filter_partial.
    iExists hfuns, [] , ms , arr, idxs.
    simpl.
    rewrite Hlenhs.
    iFrame.
    iPureIntro.
    repeat split; auto.
  Qed.

  Definition bloom_filter_from_partial l e_new els hs a rem :
    is_bloom_filter_partial l e_new els rem hs [] a -∗
      is_bloom_filter l ({[e_new]} ∪ els) rem.
  Proof.
    iIntros "Hbfp".
    iDestruct "Hbfp" as (hfuns ms_new ms_old arr idxs)
                          "(Hl & Herr & %Hhfuns & %Hlenhs & Hhs_new & Hhs_old & %HlenA & Ha & %Hms_old & %Hms_new & %Hidxs_old & %Hidxs_new & %Htrue & %Hbd & %Hfalse)".
    rewrite /is_bloom_filter.
    iExists hfuns, hs, ms_new, a, arr, idxs.
    iFrame.
    iPureIntro.
    rewrite app_nil_r in Hhfuns.
    rewrite app_nil_r in Hlenhs.
    repeat split; auto.
  Qed.


  Lemma bloom_filter_init_spec (rem : nat) :
    {{{ ↯ (fp_error rem 0 0) }}}
      init_bloom_filter #()
      {{{ (l:loc), RET #l ; is_bloom_filter l ∅ rem }}}.
  Proof using HinG conerisGS0 filter_size Σ.
    iIntros (Φ) "Herr HΦ".
    rewrite /init_bloom_filter.
    wp_pures.
    wp_bind (list_seq_fun _ _ _).
    wp_apply (wp_list_seq_fun_HO _ 0 num_hash _
                (λ _ v, hashfun filter_size v ∅)%I).
    {
      iIntros (i Φ').
      iModIntro.
      iIntros "_ HΦ".
      wp_pures.
      wp_apply wp_init_hash_basic; auto.
    }
    - iIntros (v vs) "(%Hvs & %Hlen & Hg)".
      wp_pures.
      wp_apply (wp_array_init (λ _ v, ⌜ v = #false ⌝%I)).
      + real_solver.
      + iApply big_sepL_intro.
        iModIntro.
        iIntros (??) "?".
        wp_pures.
        done.
      + iIntros (a arr) "(%HlenA & Ha & %Harr)".
        wp_pures.
        wp_alloc l as "Hl".
        wp_pures.
        iModIntro.
        iApply "HΦ".
        rewrite /is_bloom_filter.
        iExists v, vs, (repeat ∅ num_hash), a, arr, ∅.
        rewrite size_empty.
        iFrame.
        iSplit.
        {
          iPureIntro.
          set_solver.
        }
        iSplit; [done |].
        iSplit.
        {
          iApply big_sepL2_alt.
          iRevert "Hg".
          iInduction num_hash as [|nh] "IH" forall (v vs Hvs Hlen); iIntros "Hg".
          - destruct vs; auto.
          - simpl.
            destruct vs as [|v' vs']; auto.
            iSplitR; auto.
            + iPureIntro.
              rewrite repeat_length //.
            + simpl.
              iDestruct "Hg" as "[? Hg]".
              iFrame.
              destruct Hvs as [v'' [? ?]].
              iPoseProof ("IH" $! v'' vs' _ _ with "[Hg]") as "[? ?]"; auto.
              Unshelve. all:auto.
        }
        iPureIntro.
        repeat split.
        * set_solver.
        * revert v vs Hvs Hlen.
          induction num_hash; intros v vs Hvs Hlen.
          ** simpl.
             by apply Forall_nil.
          ** simpl.
             destruct vs; [inversion Hlen | ].
             destruct Hvs as [? [? ?]].
             apply Forall_cons; split; auto.
             eapply IHn; eauto.
        * set_solver.
        * set_solver.
        * set_solver.
        * intros i H ?.
          apply Nat2Z.inj' in HlenA.
          rewrite <- HlenA in H.
          pose proof (lookup_lt_is_Some_2 arr i H) as [x Hx].
          specialize (Harr i x Hx).
          rewrite Hx Harr //.
  Qed.


  Lemma bloom_filter_insert_spec (l : loc) (s : gset nat) (x rem : nat) :
    {{{ is_bloom_filter l s (S rem) ∗ ⌜ x ∉ s ⌝
    }}}
      insert_bloom_filter #l #x
      {{{ RET #() ; is_bloom_filter l (s ∪ {[x]}) rem
      }}}.
  Proof.
    iIntros (Φ) "(Hbf & %Hx ) HΦ".
    rewrite /insert_bloom_filter /is_bloom_filter.
    wp_pures.
    iDestruct "Hbf" as (hfuns hs ms a arr idxs) "(Herr & Hl & %Hfuns & Hrest)".
    wp_load.
    wp_pures.
    iAssert (is_bloom_filter_partial l x s rem [] hs a ) with "[Hl Herr Hrest]" as "Hbfp".
    {
      iExists hfuns, [] , ms , arr, idxs.
      simpl.
      iDestruct "Hrest" as "(<- & ? & -> & ? & % & % & % & % & %)".
      iFrame.
      iPureIntro.
      repeat split; auto.
    }
    wp_apply (wp_list_iter_invariant_HO
                (λ l1 l2, is_bloom_filter_partial l x s rem l1 l2 a )%I
               with "[][$Hbfp][HΦ]"); auto.
    - iIntros (lpre w lsuf Ψ).
      iModIntro.
      iIntros "Hbfp HK".
      wp_pures.
      iDestruct "Hbfp" as (hfuns' ms_new ms_old arr' idxs')
             "(Hl & Herr & %Hhfuns & %Hlenhs & Hhs_new & Hhs_old & %HlenA & Ha & %Hms_old & %Hms_new & %Hidxs_old & %Hidxs_new & %Htrue & %Hbd & %Hfalse)".
      destruct ms_old as [| mcur ms_old_tl]; [set_solver|].
      simpl.
      iDestruct "Hhs_old" as "(Hhs_cur & Hhs_rest)".
      apply Forall_cons_1 in Hms_old as [??].
      wp_apply (wp_insert_avoid_set_adv filter_size _ _ mcur _ idxs'
         (mknonnegreal (fp_error rem (S (length lsuf)) (size idxs'))
            (fp_error_nonneg rem (S (length lsuf)) (size idxs')))
         (mknonnegreal (fp_error rem (length lsuf) (size idxs'))
            (fp_error_nonneg rem (length lsuf) (size idxs')))
         (mknonnegreal (fp_error rem (length lsuf) (S (size idxs')))
            (fp_error_nonneg rem (length lsuf) (S (size idxs')))) with "[$]").
      + apply not_elem_of_dom_1.
        set_solver.
      + auto.
      + simpl.
        rewrite fp_error_m_S /=.
        lra.
      + simpl.
        iIntros (v) "(% & ? & [(% & ?) | (% &? )])".
        * wp_pures.
          wp_apply (wp_store_offset with "[$Ha]").
          {
            apply lookup_lt_is_Some_2.
            rewrite HlenA //.
          }
          iIntros "Ha".
          iApply "HK".
          rewrite /is_bloom_filter_partial.
          iExists hfuns', (ms_new ++ [(<[x:=v]> mcur)]), ms_old_tl, (<[v:=#true]> arr'),
            ({[v]} ∪ idxs').
          rewrite size_union; [|set_solver].
          rewrite size_singleton.
          simpl.
          iFrame.
          simpl.
          iPureIntro.
          repeat split.
          ** rewrite -app_assoc //.
          ** rewrite -app_assoc //.
          ** rewrite insert_length //.
          ** auto.
          ** apply Forall_app_2; auto.
             apply Forall_singleton.
             set_solver.
          ** intros e He.
             specialize (Hidxs_old e He).
             apply Forall_cons in Hidxs_old.
             destruct Hidxs_old as [? Hidxs_old_tl].
             apply (Forall_impl _ _ _ Hidxs_old_tl).
             set_solver.
          ** intros e He.
             apply Forall_app; split.
             *** specialize (Hidxs_new e He).
                 apply (Forall_impl _ _ _ Hidxs_new).
                 set_solver.
             *** apply Forall_singleton.
                 apply elem_of_union in He as [He|He].
                 **** apply elem_of_singleton in He as ->.
                      rewrite lookup_total_insert.
                      set_solver.
                 **** rewrite lookup_total_insert_ne; [|set_solver].
                      specialize (Hidxs_old e He).
                      apply Forall_cons in Hidxs_old.
                      destruct Hidxs_old as [? ?].
                      set_solver.
          ** intros i Hi.
             apply elem_of_union in Hi as [Hi|Hi].
             *** apply elem_of_singleton in Hi as ->.
                 rewrite list_lookup_insert //.
                 real_solver.
             *** rewrite list_lookup_insert_ne; auto.
                 set_solver.
          ** intros i Hi.
             apply elem_of_union in Hi as [Hi|Hi]; auto.
             apply elem_of_singleton in Hi as ->; done.
          ** intros i Hleq Hi.
             apply not_elem_of_union in Hi as [Hi1 Hi2].
             apply not_elem_of_singleton in Hi1.
             rewrite list_lookup_insert_ne; auto.

        * wp_pures.
          wp_apply (wp_store_offset with "[$Ha]").
          {
            apply lookup_lt_is_Some_2.
            rewrite HlenA //.
          }
          iIntros "Ha".
          iApply "HK".
          rewrite /is_bloom_filter_partial.
          iExists hfuns', (ms_new ++ [(<[x:=v]> mcur)]), ms_old_tl, (<[v:=#true]> arr'),
            (idxs').
          simpl.
          iFrame.
          simpl.
          iPureIntro.
          repeat split.
          ** rewrite -app_assoc //.
          ** rewrite -app_assoc //.
          ** rewrite insert_length //.
          ** auto.
          ** apply Forall_app_2; auto.
             apply Forall_singleton.
             set_solver.
          ** intros e He.
             specialize (Hidxs_old e He).
             apply Forall_cons in Hidxs_old.
             destruct Hidxs_old as [? Hidxs_old_tl].
             apply (Forall_impl _ _ _ Hidxs_old_tl).
             set_solver.
          ** intros e He.
             apply Forall_app; split.
             *** specialize (Hidxs_new e He).
                 apply (Forall_impl _ _ _ Hidxs_new).
                 set_solver.
             *** apply Forall_singleton.
                 apply elem_of_union in He as [He|He].
                 **** apply elem_of_singleton in He as ->.
                      rewrite lookup_total_insert.
                      set_solver.
                 **** rewrite lookup_total_insert_ne; [|set_solver].
                      specialize (Hidxs_old e He).
                      apply Forall_cons in Hidxs_old.
                      destruct Hidxs_old as [? ?].
                      set_solver.
          ** intros i Hi.
             destruct (decide (v = i)) as [-> | ?].
             *** rewrite list_lookup_insert //.
                 real_solver.
             *** rewrite list_lookup_insert_ne //; auto.
          ** intros i Hi; auto.
          ** intros i Hleq Hi.
             destruct (decide (v = i)) as [-> | ?].
             *** rewrite list_lookup_insert //.
             *** rewrite list_lookup_insert_ne //; auto.
   - iModIntro.
     iIntros "Hbf".
     iApply "HΦ".
     iPoseProof (bloom_filter_from_partial with "Hbf") as "Hbf".
     replace ({[x]} ∪ s) with (s ∪ {[x]}) by set_solver.
     iFrame.
  Qed.


  Lemma bloom_filter_lookup_spec (l : loc) (s : gset nat) (x rem : nat) :
    {{{ is_bloom_filter l s (S rem) ∗ ⌜ x ∉ s ⌝
    }}}
      lookup_bloom_filter #l #x
      {{{ v, RET v ; ⌜v = #false⌝ }}}.
  Proof.
    iIntros (Φ) "(Hbf & %Hx ) HΦ".
    rewrite /lookup_bloom_filter /is_bloom_filter.
    wp_pures.
    iDestruct "Hbf" as (hfuns hs ms a arr idxs) "(Herr & Hl & %Hhfuns & %Hlenhs & Hhs & %HlenA & Ha & %Hms & %Hidxs & %Htrue & %Hbd & %Hfalse)".
    wp_load.
    wp_pures.
    wp_alloc res as "Hres".
    wp_pures.
    iPoseProof (ec_weaken _ (fp_error 0 0 (size idxs)) with "Herr") as "Herr".
    {
      split.
      - apply fp_error_nonneg.
      - apply fp_error_weaken.
    }
    simpl.
    wp_apply (wp_list_iter_invariant_HO
             (λ l1 l2,
               (∃ ms_old,
                   ⌜ Forall (λ m : gmap nat nat, s = dom m) ms_old ⌝ ∗
                   [∗ list] h;m ∈ l2;ms_old, hashfun filter_size h m) ∗
               a ↦∗ arr ∗
               ⌜ is_list_HO (l1 ++ l2) hfuns ⌝∗
               ( res ↦ #false ∨
                   (res ↦ #true ∗
                    ↯ ((size idxs / (filter_size + 1)) ^ (length l2))%R)))%I
           with "[][Ha Hhs Herr Hres]"); auto.
    - iIntros (lpre w lsuf).
      iIntros (Ψ).
      iModIntro.
      iIntros "((%ms_old & %Hms_old_dom & Hms_old_hf) & Ha & %Hhfuns' & [ Hr | (Hr & Herr)])".
      + iIntros "HΨ".
        wp_pures.
        destruct ms_old as [| m ms_tail]; auto.
        simpl.
        iDestruct "Hms_old_hf" as "[Hmcur Hms_tail]".
        wp_bind (w _).
        wp_apply (wp_insert_basic _ _ _ m x with "Hmcur").
        * apply not_elem_of_dom_1.
          apply Forall_cons in Hms_old_dom as [-> ?].
          done.
        * iIntros (v) "(%Hv & Hhfw)".
          wp_pures.
          (destruct (decide (v ∈ idxs))).
          ** wp_apply (wp_load_offset with "Ha"); [apply Htrue; auto|].
             iIntros "Ha".
             wp_pures.
             iApply "HΨ".
             iModIntro.
             iFrame.
             iPureIntro.
             apply Forall_cons in Hms_old_dom as [??].
             split; auto.
             rewrite -app_assoc //.
          ** wp_apply (wp_load_offset _ _ _ _ _ #false with "Ha"); [apply Hfalse; auto|].
             iIntros "Ha".
             wp_pures.
             wp_store.
             iApply "HΨ".
             iModIntro.
             iFrame.
             iPureIntro.
             apply Forall_cons in Hms_old_dom as [??].
             split; auto.
             rewrite -app_assoc //.
      + iIntros "HΨ".
        wp_pures.
        destruct ms_old as [| m ms_tail]; auto.
        iDestruct "Hms_old_hf" as "[Hmcur Hms_tail]".
        wp_bind (w _).
        assert
          (forall z, (0 <= (size idxs / (filter_size + 1))^z)%R) as Haux.
        {
          intro z.
          apply pow_le.
          apply Rcomplements.Rdiv_le_0_compat; real_solver.
        }
        wp_apply (wp_insert_avoid_set_adv filter_size _ _ m _ idxs
                    (mknonnegreal _ (Haux (length (w :: lsuf) )))
                    (mknonnegreal _ (Haux (length lsuf )))
                    0%NNR
                        with "[$Herr $Hmcur]"); auto.
        * apply Forall_cons in Hms_old_dom as [??].
          apply not_elem_of_dom_1.
          set_solver.
        * simpl. lra.
        * iIntros (v) "(%Hv & Hhfw & Herr)".
          simpl.
          iDestruct "Herr" as "[(%Hvout & Herr) | (%Hvin & Herr)]"; wp_pures.

          ** wp_apply (wp_load_offset _ _ _ _ _ #false with "Ha"); [apply Hfalse; auto|].
             iIntros "Ha".
             wp_pures.
             wp_store.
             iApply "HΨ".
             iModIntro.
             iFrame.
             iPureIntro.
             apply Forall_cons in Hms_old_dom as [??].
             split; auto.
             rewrite -app_assoc //.

          ** wp_apply (wp_load_offset with "Ha"); [apply Htrue; auto|].
             iIntros "Ha".
             wp_pures.
             iApply "HΨ".
             iModIntro.
             iFrame.
             repeat iSplit.
             *** iPureIntro.
                 apply Forall_cons in Hms_old_dom as [??]; auto.
             *** iPureIntro.
                 rewrite -app_assoc //.
             *** iRight.
                 iFrame.

    - iFrame.
      iSplit; auto.
      iSplit; auto.
      iSplit; auto.
      iRight.
      rewrite Hlenhs.
      iFrame.
    - iIntros "(?&?&?&[?|(?&Herr)])".
      + wp_pures.
        wp_load.
        by iApply "HΦ".
      + simpl.
        iPoseProof (ec_contradict with "Herr") as "?"; done.
 Qed.

End bloom_filter.
