From Coquelicot Require Import Hierarchy.
From stdpp Require Import namespaces finite fin_sets namespaces.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl_auth numbers gset_bij.
From clutch.prelude Require Import stdpp_ext.
From clutch.coneris Require Import coneris con_hash_interface2 con_hash_interface3.

Set Default Proof Using "Type*".

Section con_hash_impl3.
  
  Variable val_size:nat.
  Variable max_hash_size:nat.
  Hypothesis Hpos: (0<max_hash_size)%nat.
  Context `{Hc: conerisGS Σ, 
              hash2: !con_hash2 val_size,
                 Htoken:inG Σ (authR natR)
    }.

  (** * Code *)

  Definition init_hash:=init_hash2.
  Definition compute_hash:=compute_hash2.
  Definition allocate_tape:=allocate_tape2.

  
  Definition hash_set_frag v γ_set γ_set' := (hash_set_frag2 v γ_set γ_set')%I.
  Definition hash_set n γ γ' γ_token:=
    (∃ ε,
        hash_set2 n γ γ' ∗
        own γ_token (● max_hash_size) ∗
        own γ_token (◯ n) ∗
        ⌜ (ε.(nonneg) = (((max_hash_size-1) * n)/2 - sum_n_m (λ x, INR x) 0%nat (n-1)) / (val_size + 1))%R⌝ ∗
      ↯ ε
    )%I.
  
  Definition hash_auth :=
    (hash_auth2 )%I.
  Definition hash_tape := hash_tape2.

  Definition hash_frag := hash_frag2.

  Definition hash_token n γ := own γ (◯ n%nat).
  
  Definition con_hash_inv N f l hm  R {HR: ∀ m, Timeless (R m)} γ1 γ2 γ_tape γ4 γ5 γ_token γ_lock:=
    (con_hash_inv2 (N.@"rand") f l hm R γ1 γ2 γ_tape γ4 γ5 γ_lock ∗
    inv (N.@"err") (∃ n, hash_set n γ2 γ5 γ_token))%I
  .

  Local Lemma err_pos (s:nat): (0 <= s / (val_size + 1))%R.
  Proof.
    apply Rcomplements.Rdiv_le_0_compat.
    - apply pos_INR.
    - pose proof (pos_INR val_size). lra.
  Qed.

  Local Lemma amortized_inequality (k : nat):
    (k <= max_hash_size)%nat ->
   ( 0 <= ((max_hash_size-1)%R * k / 2 - sum_n_m (λ x : nat, INR x) 0 (k - 1)) / (val_size + 1))%R.
  Proof.
    intros H.
    pose proof (pos_INR max_hash_size) as H1.
    pose proof (pos_INR val_size) as H2.
    pose proof (pos_INR k) as H3.
    apply Rcomplements.Rdiv_le_0_compat; last lra.
    assert (sum_n_m (λ x : nat, INR x) 0 (k - 1) = (k-1)*k/2)%R as ->.
    - clear.
      induction k.
      + simpl. rewrite sum_n_n.
        rewrite Rmult_0_r. by assert (0/2 = 0)%R as -> by lra.
      + clear. induction k.
        * simpl. rewrite sum_n_n.
          replace (_-_)%R with 0%R by lra.
          rewrite Rmult_0_l. by assert (0/2 = 0)%R as -> by lra.
        * assert (S (S k) - 1 = S (S k - 1))%nat as -> by lia.
          rewrite sum_n_Sm; last lia.
          rewrite IHk.
          replace (plus _ _) with (((S k - 1) * S k / 2) + (S (S k - 1))) by done.
          assert (∀ k, (INR (S k) - 1) = (INR k))%R as H'.
          { intros. simpl. case_match; first replace (1 - 1)%R with 0%R by lra.
            - done.
            - by replace (_+1-1)%R with (INR (S n)) by lra.
          }
          rewrite !H'.
          replace (S k - 1)%nat with (k)%nat by lia.
          replace (Hierarchy.plus _ _) with ((k * S k / 2)%R + (S k))%R by done.
          assert (k * (S k) + S k + S k = S k * S (S k))%R; last lra.
          assert (k * S k + S k + S k = S k * (k+1+1))%R as ->; try lra.
          assert (k+1+1 = S (S k))%R.
          -- rewrite !S_INR. lra.
          -- by rewrite H.
    - rewrite -!Rmult_minus_distr_r.
      apply Rcomplements.Rdiv_le_0_compat; try lra.
      apply Rmult_le_pos; try lra.
      assert (INR k <= INR max_hash_size)%R; try lra.
      by apply le_INR.
  Qed.

  Lemma hash_tape_presample  N f l hm R {HR: ∀ m, Timeless (R m )} γ_hv γ_set γ_hv' γ_token γ γ_set' γ_lock α ns  E:
  ↑(N)⊆E ->
  con_hash_inv N f l hm R γ_hv γ_set γ γ_hv' γ_set' γ_token γ_lock -∗
  hash_tape α ns γ_set γ-∗
  ↯ (amortized_error val_size max_hash_size Hpos) -∗
  hash_token 1 γ_token-∗
    (* hash_set3 s γ_set γ_set' γ6-∗ *)
    state_update E E (∃ (n:fin(S val_size)), 
          (* ( hash_set3 (s+1)%nat γ_set γ_set' γ6 )∗ *)
          hash_tape α (ns++[fin_to_nat n]) γ_set γ ∗ hash_set_frag (fin_to_nat n) γ_set γ_set'
      ).
  Proof.
    rewrite /hash_tape/hash_token/hash_set.
    iIntros (Hsubset ) "#[Hinv Hinv'] Ht Herr Htoken ".
    iInv ("Hinv'") as ">(%s&(%&?&Hauth&Htokens&%H&?))" "Hclose". 
    iDestruct (ec_combine with "[$]") as "Herr".
    rewrite /amortized_error/=H.
    
    iAssert (⌜s+1 <=max_hash_size⌝)%I as "%Hineq'".
    { iCombine "Htoken Htokens" as "H".
      iCombine "Hauth H" gives "H0".
      rewrite auth_both_validI.
      iDestruct "H0" as "[[% %H']_]". simpl in *.
      rewrite nat_op in H'. iPureIntro. lia.
    }
    
    iAssert (↯ (s/(val_size+1)+(((max_hash_size-1) * (s+1))/2 - sum_n_m (λ x, INR x) 0%nat (s))%R / (val_size + 1))%R )%I with "[Herr]" as "Herr".
    { iApply ec_eq; last done.
      remember (val_size + 1)%R as v.
      remember (max_hash_size) as h.
      assert (∀ x y, x/y = x*/y)%R as Hdiv.
      { intros. lra. }
      destruct s.
      + simpl. rewrite sum_n_n. rewrite Rdiv_0_l Rmult_0_r.
        replace (INR 0%nat) with 0%R; last done.
        rewrite !Rminus_0_r.
        replace (0/_/_)%R with 0%R; last lra.
        rewrite !Rplus_0_l.
        rewrite Rmult_1_r.
        rewrite !Hdiv.
        rewrite Rinv_mult.
        lra.
      + assert (forall k, S k - 1 = k)%nat as H' by lia.
        rewrite !H'.
        clear H'.
        rewrite sum_n_Sm; last lia.
        replace (Hierarchy.plus _ (INR (S s)))%R with ((sum_n_m (λ x : nat, INR x) 0 s) + (S s))%R by done.
        rewrite !Hdiv.
        rewrite !Rmult_minus_distr_r.
        rewrite (Rmult_plus_distr_r (sum_n_m _ _ _)).
        rewrite -!Rplus_assoc.
        rewrite Ropp_plus_distr.
        rewrite -!Rplus_assoc.
        assert (((h - 1) * S s * / 2 * / v  + (h-1) * / (2 * v) )%R =
                (S s * / v + (h -1)* (S s + 1) * / 2 * / v   + - (S s * / v))%R)%R; try lra.
        assert ( (h-1) * S s * / 2 * / v + (h-1) * / (2 * v) = (h-1) * (S s+1) * / 2 * / v)%R; try lra.
        replace (_*_*_*_)%R with ((h-1) * (S s) * /(2*v))%R; last first.
        { rewrite Rinv_mult. lra. }
        replace (_*_*_*_)%R with ((h-1) * (S(S s)) * /(2*v))%R; last first.
        { rewrite Rinv_mult. rewrite S_INR. lra. }
        rewrite -Rdiv_plus_distr.
        rewrite Hdiv.
        f_equal.
        rewrite -{2}(Rmult_1_r (h-1)).
        rewrite -Rmult_plus_distr_l.
        f_equal. }
    iDestruct (ec_split with "[$]") as "[Herr Herr']".
    { apply err_pos. }
    { pose proof  amortized_inequality (s+1) as K.
      apply K in Hineq'.
      replace (_+_-_) with s in Hineq'; last lia.
      rewrite plus_INR in Hineq'. simpl in *. done. }
    iMod (con_hash_interface2.hash_tape_presample _ _ _ _ _ _ _ _ _ _ _ _ _ _ (mknonnegreal _ _) 0%NNR with "[//][$][Herr][$]") as "(%&[Hs _]&Ht&Hsf)"; [| |iApply ec_eq; last done; simpl; done|].
    - apply subseteq_difference_r.
      + by apply ndot_ne_disjoint.
      + by apply nclose_subseteq'.
    - simpl. rewrite Rmult_0_l Rplus_0_r.
      rewrite -Rmult_div_swap.
      rewrite Rmult_div_l; first done.
      pose proof pos_INR val_size. lra.
    - iCombine "Htoken Htokens" as "Htokens".
      iFrame.
      iMod ("Hclose" with "[$Hauth $Htokens Hs Herr']")as "_".
      { replace (s+1)%nat with (1+s)%nat by lia. iFrame.
        replace (1+s-1)%nat with s by lia.
        rewrite plus_INR.
        simpl.
        replace (1+s)%R with (s+1)%R by lra.
        iDestruct (ec_valid with "[$]") as "%H'".
        unshelve iExists (mknonnegreal _ _); last  iFrame; try done. naive_solver.
      }
      iModIntro. iFrame.
      Unshelve.
      + apply err_pos. 
  Qed.


  Lemma con_hash_init N R {HR: ∀ m, Timeless (R m)}:
    {{{ R ∅}}}
      init_hash #()
      {{{ (f:val), RET f; ∃ l hm γ1 γ2 γ3 γ4 γ5 γ_token γ_lock, con_hash_inv N f l hm R γ1 γ2 γ3 γ4 γ5 γ_token γ_lock ∗  hash_token max_hash_size γ_token
      }}}.
  Proof.
    iIntros (Φ)"HP HΦ".
    iApply fupd_pgl_wp.
    iMod (own_alloc (● max_hash_size ⋅ ◯ (0+max_hash_size)%nat)) as (γ_token) "[H● [H0 H◯]]"; first (simpl; by apply auth_both_valid_2).
    iModIntro.
    iApply pgl_wp_fupd.
    rewrite /init_hash.
    iApply (con_hash_init2 with "HP").
    iNext.
    iIntros (?)"(%&%&%&%&%&%&%&%&#Hinv&Hs)".
    rewrite /con_hash_inv.
    iMod (ec_zero) as "H0err".
    iMod (inv_alloc _ _ (∃ n : nat, hash_set n _ _ γ_token)%I with "[$H0 $H● $Hs H0err]").
    { iExists nnreal_zero. iFrame.
      iPureIntro. simpl. rewrite sum_n_n. simpl. lra.  }
    iApply "HΦ". iFrame.
    by iFrame "Hinv".
  Qed.

  Lemma con_hash_alloc_tape N f l hm R {HR: ∀ m, Timeless (R m)} γ1 γ2 γ3 γ4 γ5 γ_token γ_lock:
  {{{ con_hash_inv N f l hm R γ1 γ2 γ3 γ4 γ5 γ_token γ_lock 
  }}}
      allocate_tape #()
      {{{ (α: val), RET α; hash_tape α [] γ2 γ3  }}}.
  Proof.
    iIntros (Φ) "#[H1 H2] HΦ".
    rewrite /allocate_tape.
    by wp_apply (con_hash_alloc_tape2 with "[$H1]"). 
  Qed.

  Lemma con_hash_spec N f l hm R {HR: ∀ m, Timeless (R m )} γ1 γ2 γ3 γ4 γ5 γ_token γ_lock Q1 Q2 α (v:nat):
  {{{ con_hash_inv N f l hm R γ1 γ2 γ3 γ4 γ5 γ_token γ_lock ∗ 
      ( ∀ m, R m -∗ hash_auth m γ1 γ2 γ4 γ5-∗ state_update (⊤) (⊤)
             match m!!v with
             | Some res => R m ∗ hash_auth m γ1 γ2 γ4 γ5∗ Q1 res
             | None => ∃ n ns, hash_tape α (n::ns) γ2 γ3 ∗ 
                              (hash_tape α (ns) γ2 γ3
                                      ={⊤}=∗ R (<[v:=n]> m) ∗
                                      hash_auth (<[v:=n]> m) γ1 γ2 γ4 γ5∗ Q2 n ns)
             end                                        
      )
  }}}
      f #v α
      {{{ (res:nat), RET (#res);  (Q1 res ∨
                                 ∃ ns, Q2 res ns
                                )
      }}}
.
  Proof.
    iIntros (Φ) "(#[H1 H2] & Hvs) HΦ".
    iApply (con_hash_spec2 with "[$H1 Hvs]"); last done.
    iApply "Hvs".
  Qed.
    
    
  
  Program Definition con_hash_impl3 : con_hash3 val_size max_hash_size Hpos :=
    {| init_hash3:=init_hash;
      allocate_tape3:=allocate_tape;
      compute_hash3:=compute_hash;
      
      con_hash_inv3 := con_hash_inv;
      hash_tape3:=hash_tape;
      hash_frag3:=hash_frag;
      hash_auth3:=hash_auth;
      hash_set3:=hash_set;
      hash_set_frag3:=hash_set_frag;
      hash_token3 := hash_token;
      con_hash_interface3.hash_tape_presample := hash_tape_presample;
      con_hash_init3 := con_hash_init;
      con_hash_alloc_tape3 := con_hash_alloc_tape;
      con_hash_spec3:=con_hash_spec
    |}.
  Next Obligation.
    iIntros (??????) "??".
    iApply (con_hash_interface2.hash_auth_exclusive with "[$][$]").
  Qed.
  Next Obligation.
    iIntros.
    iApply (con_hash_interface2.hash_auth_frag_agree with "[$][$]").
  Qed.
  Next Obligation.
    iIntros.
    by iApply (con_hash_interface2.hash_auth_duplicate with "[$]").
  Qed.
  Next Obligation.
    iIntros.
    iApply (con_hash_interface2.hash_auth_coll_free with "[$]").
  Qed.
  Next Obligation.
    iIntros (???????) "H1 H2".
    by iDestruct (con_hash_interface2.hash_frag_frag_agree with "[$H1][$H2]") as "?".
  Qed.
  Next Obligation.
    iIntros.
    by iApply (con_hash_interface2.hash_auth_insert with "[$][$]").
  Qed.
  Next Obligation.
    iIntros.
    iApply (con_hash_interface2.hash_tape_valid with "[$]").
  Qed.
  Next Obligation.
    iIntros.
    iApply (con_hash_interface2.hash_tape_exclusive with "[$][$]").
  Qed.
  Next Obligation.
    iIntros.
    rewrite -own_op. rewrite nat_is_op. rewrite /hash_token.
    rewrite auth_frag_op.
    iSplit; by iIntros.
  Qed.
  
  (* Qed. *)
  (* Next Obligation. *)
  (*   iIntros (???????)"[??][??]". *)
  (*   iApply (hv_auth_frag_agree with "[$]"). *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   iIntros (????????) "[?[??]]". *)
  (*   iDestruct (hv_auth_duplicate_frag with "[$]") as "[? $]"; first done. *)
  (*   by iApply (con_hash_interface1.hash_auth_duplicate). *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   iIntros (?????) "[??]". *)
  (*   by iApply hv_auth_coll_free. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   rewrite /hash_frag. *)
  (*   iIntros (???????) "[??][??]". *)
  (*   iDestruct (hv_frag_frag_agree with "[$][$]") as "%". iPureIntro. naive_solver. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   iIntros (????????) "[H1 H2][H3[H4 H5]]". *)
  (*   rewrite /hash_set_frag. *)
  (*   rewrite big_sepM_sep. *)
  (*   iDestruct "H5" as "[#H5 H6]". *)
  (*   rewrite /hash_auth. *)
  (*   iMod (con_hash_interface1.hash_auth_insert with "[$][$]") as "K"; first done. *)
  (*   iDestruct (con_hash_interface1.hash_auth_duplicate with "[$]") as "#?"; first apply lookup_insert. *)
  (*   iAssert (⌜v∉(map_to_list m).*2⌝)%I as "%H0". *)
  (*   { iIntros (H'). *)
  (*     apply elem_of_list_fmap_2 in H'. *)
  (*     destruct H' as ([??]&?&H1). simplify_eq. *)
  (*     rewrite elem_of_map_to_list in H1. *)
  (*     iDestruct (big_sepM_lookup with "[$]") as "H4"; first done. *)
  (*     simpl. *)
  (*     iCombine "H2 H4" gives "%H0". *)
  (*     cbv in H0. naive_solver. *)
  (*   }  *)
  (*   iMod (hv_auth_insert with "[$]") as "[$?]"; first done. *)
  (*   { rewrite Forall_forall. *)
  (*     intros x Hx. *)
  (*     intros ->. *)
  (*     by apply H0. } *)
  (*   rewrite big_sepM_insert; last done. *)
  (*   iFrame. *)
  (*   iDestruct (hash_frag_in_hash_set with "[$]") as "$". *)
  (*   rewrite /hash_set_frag. *)
  (*   iModIntro. rewrite big_sepM_sep. *)
  (*   by iFrame. *)
  (* Qed. *)
  
  (* Next Obligation. *)
  (*   iIntros (????) "?". *)
  (*   by iApply con_hash_interface1.hash_tape_valid. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   iIntros (?????) "??". *)
  (*   iApply (con_hash_interface1.hash_tape_exclusive with "[$][$]"). *)
  (* Qed. *)

  
End con_hash_impl3.
