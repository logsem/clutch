(** * Hocap rand that generates a exclusive token as well
      In most examples, the exclusive token is not needed since the data structure need not need to create 
      an auth view of all the tapes. 
      Useful for building more complex data structures when we need to know all the tapes generated
      We also fix the tape bound
 *)
From iris.algebra Require Import excl_auth gmap.
From clutch.coneris Require Import coneris abstract_tape.

Set Default Proof Using "Type*".

Class rand_spec' (tb:nat) `{!conerisGS Σ} := RandSpec'
{
  (** * Operations *)
  rand_allocate_tape : val;
  rand_tape : val;
  (** * Ghost state *)

  rand_tape_name: Type;
  
  (** * Predicates *)
  is_rand (N:namespace)
    (γ1: rand_tape_name) : iProp Σ; 
  rand_tapes (* (γ: rand_tape_name) *) (α:val) (ns: (list nat)) (γ1: rand_tape_name): iProp Σ;
  rand_token (α: val) (γ:rand_tape_name) : iProp Σ;
  (** * General properties of the predicates *)
  #[global] is_rand_persistent N γ1 ::
    Persistent (is_rand N γ1);
  #[global] rand_tapes_timeless α ns γ::
    Timeless (rand_tapes α ns γ);  
  #[global] rand_token_timeless α γ::
    Timeless (rand_token α γ);  
  rand_tapes_exclusive α ns ns' γ:
  rand_tapes α ns γ-∗ rand_tapes α ns' γ-∗ False;
  rand_token_exclusive α γ:
  rand_token α γ -∗ rand_token α γ -∗ False; 
  rand_tapes_valid α ns γ:
    rand_tapes α ns γ -∗ ⌜Forall (λ n, n<=tb)%nat ns⌝ ; 
  rand_tapes_presample N E α ns ε (ε2 : fin (S tb) -> R) γ:
  ↑N⊆E -> 
  (∀ x, 0<=ε2 x)%R ->
  (SeriesC (λ n, 1 / (S tb) * ε2 n)%R <= ε)%R ->
  is_rand N γ -∗
  rand_tapes α ns γ-∗
  ↯ ε  -∗
  state_update E E (∃ n, ↯ (ε2 n) ∗ rand_tapes α (ns ++ [fin_to_nat n]) γ); 
    

  (** * Program specs *)
  rand_inv_create_spec N E:
  ↑N ⊆ E -> ⊢ |={E}=> (∃ γ1, is_rand N γ1);
  
  rand_allocate_tape_spec N γ E :
  ↑N ⊆ E ->
    {{{ is_rand N γ }}}
      rand_allocate_tape #() @ E
      {{{ (v:val), RET v;
          rand_token v γ∗
           rand_tapes v [] γ
      }}}; 
  
  rand_tape_spec_some N γ E α n ns:
  ↑N ⊆ E ->
    {{{ is_rand N γ ∗ rand_tapes α (n::ns) γ }}}
      rand_tape α @ E
                       {{{ RET #n; rand_tapes α (ns) γ }}}; 
}.

Section checks.
  Context `{H: conerisGS Σ, r1:!rand_spec' tb}.
  
  Lemma wp_rand_tape_1 N n ns α γ:
    {{{ is_rand N γ ∗ ▷ rand_tapes α (n :: ns) γ }}}
      rand_tape α 
                       {{{ RET #(LitInt n); rand_tapes α (ns) γ ∗ ⌜n <= tb⌝ }}}.
  Proof.
    iIntros (Φ) "[#Hinv >Hfrag] HΦ".
    iDestruct (rand_tapes_valid with "[$]") as "%H'". 
    wp_apply (rand_tape_spec_some with "[$Hfrag //]"); first exact.
    iIntros.
    iApply "HΦ".
    iFrame.
    iPureIntro.
    rewrite Forall_cons in H'. naive_solver.
  Qed.

  Local Opaque enum_uniform_fin_list.

              
  Lemma wp_presample_adv_comp_rand_tape N E α ns (ε1 : R) (ε2 : fin (S tb) -> R) γ:
    ↑N ⊆ E ->
    (∀ n, 0<=ε2 n)%R ->
    (SeriesC (λ n, (1 / (S tb)) * ε2 n)%R <= ε1)%R →
    is_rand N γ -∗
    ▷ rand_tapes α (ns) γ -∗
    ↯ ε1 -∗
    wp_update E (∃ n, ↯ (ε2 n) ∗ rand_tapes α (ns ++[fin_to_nat n]) γ)%I.
  Proof.
    iIntros (Hsubset Hpos Hineq) "#Hinv >Htape Herr".
    iDestruct (ec_valid with "[$]") as "%Hpos'".
    destruct Hpos' as [Hpos' ?].
    iApply wp_update_state_update.
    by iApply (rand_tapes_presample with "[$][$]").
  Qed.
      

End checks.

Section impl1.
  Context `{!conerisGS Σ, Hs : !ghost_mapG Σ val (), Hm : !abstract_tapesGS Σ }.
  Variable tb:nat.
  Local Opaque INR.
  (* (** Instantiate rand *) *)
  Local Definition rand_inv_pred1  (γ:gname*gname) : iProp Σ:=
    (∃ (m:gmap val (list nat)),
        (ghost_map_auth γ.1 1 ((λ _, ())<$>m)) ∗
        ● ((λ x, (tb, x))<$>m)@ γ.2 ∗
        [∗ map] α ↦ns∈m, (∃ α', ⌜α = #lbl:α'⌝ ∗ (α' ↪N (tb; ns) ))
    )%I.

  Definition is_rand1 N γ:=
    inv N (rand_inv_pred1 γ).

  Definition rand_tapes1 α ns (γ:gname*gname):=
    (α◯↪N (tb; ns) @γ.2 ∗ ⌜Forall (λ x, x<=tb)%nat ns⌝)%I.

  Definition rand_token1 α (γ:gname*gname) :=
    (α ↪[γ.1] ())%I.
  
  #[local] Program Definition rand_spec1 : rand_spec' tb :=
    {| rand_allocate_tape:= (λ: "_", alloc #tb);
      rand_tape:= (λ: "α", rand("α") #tb); 
      is_rand  := is_rand1;
      rand_tapes := rand_tapes1;
      rand_token := rand_token1;
    |}.
  Next Obligation.
    simpl.
    iIntros (????) "[H1 %] [H2 %]".
    iApply (abstract_tapes_frag_exclusive with "[$][$]").
  Qed.
  Next Obligation.
    simpl.
    iIntros (??) "H1 H2".
    iCombine "H1 H2" gives "%H".
    cbv in H. naive_solver.
  Qed.
  Next Obligation.
    simpl.
    iIntros (???) "(?&$)". 
  Qed.
  Next Obligation.
    simpl.
    iIntros (??????????) "#Hinv [H1 %] Herr".
    iInv "Hinv" as ">(%&Hs&Hm&Ht)" "Hclose".
    iDestruct (abstract_tapes_agree with "[$][$]") as "%Hsome".
    rewrite lookup_fmap_Some in Hsome.
    destruct Hsome as (?&?&Hsome). simplify_eq.
    iDestruct (big_sepM_insert_acc with "[$]") as "[(%&%Heq&Ht) Hclose']"; first done.
    simplify_eq.
    iMod (state_update_presample_exp with "[$][$]") as "(%n&Ht&Herr)"; [done..|].
    iMod (abstract_tapes_presample with "[$][$]") as "[Hm H1]".
    iDestruct ("Hclose'" with "[$Ht]") as "Ht"; first done.
    iMod ("Hclose" with "[Hs Hm $Ht]"); last iFrame.
    - rewrite !fmap_insert (insert_id _ _ ()); first iFrame.
      rewrite lookup_fmap. by rewrite Hsome.
    - iPureIntro. apply Forall_app; split; first done.
      apply Forall_singleton. pose proof fin_to_nat_lt n. lia.
  Qed.
  Next Obligation.
    iIntros (???).
    rewrite /is_rand1/rand_inv_pred1.
    iMod (abstract_tapes_alloc ∅) as "(%&H1&_)".
    iMod (ghost_map_alloc_empty) as "(%&H2)".
    iMod (inv_alloc with "[H1 H2]"); last first.
    - iExists (_,_). by iFrame.
    - iNext. iExists ∅.
      rewrite !fmap_empty. by iFrame.
  Qed.
  Next Obligation.
    simpl.
    iIntros (?[??]?? Φ) "#Hinv HΦ".
    wp_pures.
    iInv "Hinv" as ">(%&Hs&Hm&Hts)" "Hclose".
    wp_apply (wp_alloc_tape); first done.
    iIntros (α) "Ht".
    iAssert (⌜m!!#lbl:α=None⌝)%I as "%Hnone".
    { destruct (_!!_) eqn:?; last done.
      iDestruct (big_sepM_insert_acc with "[$]") as "[(%&%&?) Hclose']"; first done.
      simplify_eq.
      by iDestruct (tapeN_tapeN_contradict with "[$][$]") as "%".
    }
    iMod (ghost_map_insert with "[$]") as "[Hs Htoken]"; first by erewrite lookup_fmap, Hnone.
    iMod (abstract_tapes_new with "[$]") as "[Hm ?]"; first by erewrite lookup_fmap, Hnone.
    iMod ("Hclose" with "[Hts Ht Hs Hm]").
    { iNext. iExists (<[_:=_]>_). rewrite !fmap_insert.
      iFrame.
      rewrite big_sepM_insert; last done.
      by iFrame.
    }
    iApply "HΦ". by iFrame.
  Qed.
  Next Obligation.
    iIntros (?[??]???? Hsubset Φ) "[#Hinv [Htfrag %]] HΦ".
    iApply fupd_pgl_wp.
    iInv "Hinv" as ">(%&Hs&Hm&Hts)" "Hclose".
    iDestruct (abstract_tapes_agree with "[$][$]") as "%Hsome".
    rewrite lookup_fmap_Some in Hsome.
    destruct Hsome as (?&?&?). simplify_eq.
    iDestruct (big_sepM_lookup_acc with "[$]") as "[(%&%&?) Hclose']"; first done.
    simplify_eq.
    iMod ("Hclose" with "[-Htfrag HΦ]") as "_"; iFrame.
    { iDestruct ("Hclose'" with "[-]") as "$". by iFrame. }
    iModIntro. wp_pures.
    iInv "Hinv" as ">(%&Hs&Hm&Hts)" "Hclose".
    iDestruct (abstract_tapes_agree with "[$][$]") as "%Hsome".
    rewrite lookup_fmap_Some in Hsome.
    destruct Hsome as (?&?&Hsome). simplify_eq.
    iDestruct (big_sepM_insert_acc with "[$]") as "[(%&%&?) Hclose']"; first done.
    simplify_eq.
    wp_apply (wp_rand_tape with "[$]") as "[Htape %]".
    iMod (abstract_tapes_pop with "[$][$]") as "[Hm Htfrag]".
    iDestruct ("Hclose'" with "[$Htape]") as "Htapes"; first done.
    iMod ("Hclose" with "[-HΦ Htfrag]").
    { iFrame. rewrite !fmap_insert. iFrame.
      rewrite (insert_id _ _ ()); first iFrame.
      rewrite lookup_fmap. by rewrite Hsome. }
    iApply "HΦ". iFrame.
    iPureIntro. by eapply Forall_inv_tail.
  Qed.
End impl1.

Section impl2.
  Context `{!conerisGS Σ, Hs : !ghost_mapG Σ val (), Hm : !abstract_tapesGS Σ }.
  Local Opaque INR.
  
  (** simulating a rand 3 with two flips *)
  Local Definition rand_inv_pred2  (γ:gname*gname) : iProp Σ:=
    (∃ (m:gmap val (list nat)),
        (ghost_map_auth γ.1 1 ((λ _, ())<$>m)) ∗
        ● ((λ x, (1, x))<$>m)@ γ.2 ∗
        [∗ map] α ↦ns∈m, (∃ α', ⌜α = #lbl:α'⌝ ∗ (α' ↪N (1; ns) ))
    )%I.

  Definition is_rand2 N γ:=
    inv N (rand_inv_pred2 γ).

  Local Definition expander (l:list nat):=
    l ≫= (λ x, [x/2; x `mod` 2]).
  Definition rand_tapes2 (α:val) ns (γ:gname*gname):=
    (α◯↪N (1; expander ns) @γ.2 ∗ ⌜Forall (λ x, x<=3)%nat ns⌝)%I.

  Definition rand_token2 α (γ:gname*gname) :=
    (α ↪[γ.1] ())%I.
  
  #[local] Program Definition rand_spec2 : rand_spec' 3 :=
    {| rand_allocate_tape:= (λ: "_", alloc #1);
      rand_tape:= (λ: "α", (rand("α") #1) + (#2*rand("α") #1)); 
      is_rand  := is_rand2;
      rand_tapes := rand_tapes2;
      rand_token := rand_token2;
    |}.
  Next Obligation.
    simpl.
    iIntros (????) "[H1 %] [H2 %]".
    iApply (abstract_tapes_frag_exclusive with "[$][$]").
  Qed.
  Next Obligation.
    simpl.
    iIntros (??) "H1 H2".
    iCombine "H1 H2" gives "%H".
    cbv in H. naive_solver.
  Qed.
  Next Obligation.
    simpl.
    iIntros (???) "(?&$)". 
  Qed.
  Next Obligation.
    simpl.
    iIntros (??????????) "#Hinv [H1 %] Herr".
    iInv "Hinv" as ">(%&Hs&Hm&Ht)" "Hclose".
    iDestruct (abstract_tapes_agree with "[$][$]") as "%Hsome".
    rewrite lookup_fmap_Some in Hsome.
    destruct Hsome as (?&?&Hsome). simplify_eq.
    iDestruct (big_sepM_insert_acc with "[$]") as "[(%&%Heq&Ht) Hclose']"; first done.
    simplify_eq.
    iMod (state_update_presample_exp _ _ _ _ _ (λ x, 1/2* if bool_decide (fin_to_nat x=1)%nat then ε2 2%fin + ε2 3%fin else ε2 0%fin + ε2 1%fin)%R with "[$][$]") as "(%n1&Ht&Herr)".
    { intros. case_bool_decide; apply Rmult_le_pos; try lra;
        apply Rplus_le_le_0_compat; naive_solver.
    }
    { rewrite !SeriesC_finite_foldr /= in H1 *. etrans; last exact.
      replace (INR 2) with 2%R by done.
      replace (INR 4) with 4%R; first lra.
      rewrite !S_INR INR_0. lra.
    }
    case_bool_decide as K1.
    - (* sampled a 1*)
      iMod (state_update_presample_exp _ _ _ _ _ (λ x, if bool_decide (fin_to_nat x=1)%nat then ε2 3%fin else ε2 2%fin)%R with "[$][$]") as "(%n2&Ht&Herr)".
      { intros. case_bool_decide; naive_solver. }
      { rewrite SeriesC_finite_foldr/=. replace (INR 2) with 2%R by done.
        lra.
      }
      do 2 iMod (abstract_tapes_presample with "[$][$]") as "[Hm H1]".
      iDestruct ("Hclose'" with "[$Ht]") as "Ht"; first done.
      iMod ("Hclose" with "[Hs Hm $Ht]"); last iFrame.
      + rewrite !fmap_insert (insert_id _ _ ()); first iFrame.
        * by rewrite insert_insert.
        * rewrite lookup_fmap. by rewrite Hsome.
      + case_bool_decide as K2; iFrame; rewrite /rand_tapes2 /expander bind_app.
        * rewrite K1 K2/= -app_assoc. iFrame.
          iPureIntro. apply Forall_app. split; first done.
          apply Forall_singleton. done.
        * rewrite K1. assert (fin_to_nat n2 = 0) as ->.
          { repeat (inv_fin n2; first done; try intros n2 ?); inv_fin n2.
          }
          rewrite -app_assoc. iFrame.
          iPureIntro. apply Forall_app. split; first done.
          apply Forall_singleton. simpl. lia.
    - (* sampled a 0*)
      iMod (state_update_presample_exp _ _ _ _ _ (λ x, if bool_decide (fin_to_nat x=1)%nat then ε2 1%fin else ε2 0%fin)%R with "[$][$]") as "(%n2&Ht&Herr)".
      { intros. case_bool_decide; naive_solver. }
      { rewrite SeriesC_finite_foldr/=. replace (INR 2) with 2%R by done.
        lra.
      }
      do 2 iMod (abstract_tapes_presample with "[$][$]") as "[Hm H1]".
      iDestruct ("Hclose'" with "[$Ht]") as "Ht"; first done.
      iMod ("Hclose" with "[Hs Hm $Ht]"); last iFrame.
      + rewrite !fmap_insert (insert_id _ _ ()); first iFrame.
        * by rewrite insert_insert.
        * rewrite lookup_fmap. by rewrite Hsome.
      + case_bool_decide as K2; iFrame; rewrite /rand_tapes2 /expander bind_app.
        * assert (fin_to_nat n1 = 0) as ->.
          { repeat (inv_fin n1; first done; try intros n1 ?); inv_fin n1.
          }
          rewrite K2/= -app_assoc. iFrame.
          iPureIntro. apply Forall_app. split; first done.
          apply Forall_singleton. lia. 
        * assert (fin_to_nat n1 = 0) as ->.
          { repeat (inv_fin n1; first done; try intros n1 ?); inv_fin n1.
          }
          assert (fin_to_nat n2 = 0) as ->.
          { repeat (inv_fin n2; first done; try intros n2 ?); inv_fin n2.
          }
          rewrite -app_assoc. iFrame.
          iPureIntro. apply Forall_app. split; first done.
          apply Forall_singleton. simpl. lia.   
  Qed.
  Next Obligation.
    iIntros (???).
    rewrite /is_rand2/rand_inv_pred2.
    iMod (abstract_tapes_alloc ∅) as "(%&H1&_)".
    iMod (ghost_map_alloc_empty) as "(%&H2)".
    iMod (inv_alloc with "[H1 H2]"); last first.
    - iExists (_,_). by iFrame.
    - iNext. iExists ∅.
      rewrite !fmap_empty. by iFrame.
  Qed.
  Next Obligation.
    simpl.
    iIntros (?[??]?? Φ) "#Hinv HΦ".
    wp_pures.
    iInv "Hinv" as ">(%&Hs&Hm&Hts)" "Hclose".
    wp_apply (wp_alloc_tape); first done.
    iIntros (α) "Ht".
    iAssert (⌜m!!#lbl:α=None⌝)%I as "%Hnone".
    { destruct (_!!_) eqn:?; last done.
      iDestruct (big_sepM_insert_acc with "[$]") as "[(%&%&?) Hclose']"; first done.
      simplify_eq.
      by iDestruct (tapeN_tapeN_contradict with "[$][$]") as "%".
    }
    iMod (ghost_map_insert with "[$]") as "[Hs Htoken]"; first by erewrite lookup_fmap, Hnone.
    iMod (abstract_tapes_new with "[$]") as "[Hm ?]"; first by erewrite lookup_fmap, Hnone.
    iMod ("Hclose" with "[Hts Ht Hs Hm]").
    { iNext. iExists (<[_:=_]>_). rewrite !fmap_insert.
      iFrame.
      rewrite big_sepM_insert; last done.
      by iFrame.
    }
    iApply "HΦ". by iFrame.
  Qed.
  Next Obligation.
    iIntros (?[??]???? Hsubset Φ) "[#Hinv [Htfrag %H]] HΦ".
    rewrite /expander bind_cons.
    iApply fupd_pgl_wp.
    iInv "Hinv" as ">(%&Hs&Hm&Hts)" "Hclose".
    iDestruct (abstract_tapes_agree with "[$][$]") as "%Hsome".
    rewrite lookup_fmap_Some in Hsome.
    destruct Hsome as (?&?&?). simplify_eq.
    iDestruct (big_sepM_lookup_acc with "[$]") as "[(%&%&?) Hclose']"; first done.
    simplify_eq.
    iMod ("Hclose" with "[-Htfrag HΦ]") as "_"; iFrame.
    { iDestruct ("Hclose'" with "[-]") as "$". by iFrame. }
    iModIntro. wp_pures.
    wp_bind (rand(_) _)%E.
    iInv "Hinv" as ">(%&Hs&Hm&Hts)" "Hclose".
    iDestruct (abstract_tapes_agree with "[$][$]") as "%Hsome".
    rewrite lookup_fmap_Some in Hsome.
    destruct Hsome as (?&?&Hsome). simplify_eq.
    iDestruct (big_sepM_insert_acc with "[$]") as "[(%&%&?) Hclose']"; first done.
    simplify_eq.
    wp_apply (wp_rand_tape with "[$]") as "[Htape %]".
    iMod (abstract_tapes_pop with "[$][$]") as "[Hm Htfrag]".
    iDestruct ("Hclose'" with "[$Htape]") as "Htapes"; first done.
    iMod ("Hclose" with "[-HΦ Htfrag]").
    { iFrame. rewrite !fmap_insert. iFrame.
      rewrite (insert_id _ _ ()); first iFrame.
      rewrite lookup_fmap. by rewrite Hsome. }
    iModIntro. wp_pures.
    wp_bind (rand(_) _)%E.
    iInv "Hinv" as ">(%&Hs&Hm&Hts)" "Hclose".
    iDestruct (abstract_tapes_agree with "[$][$]") as "%Hsome'".
    rewrite lookup_fmap_Some in Hsome'.
    destruct Hsome' as (?&?&Hsome'). simplify_eq.
    iDestruct (big_sepM_insert_acc with "[$]") as "[(%&%&?) Hclose']"; first done.
    simplify_eq.
    wp_apply (wp_rand_tape with "[$]") as "[Htape %]".
    iMod (abstract_tapes_pop with "[$][$]") as "[Hm Htfrag]".
    iDestruct ("Hclose'" with "[$Htape]") as "Htapes"; first done.
    iMod ("Hclose" with "[-HΦ Htfrag]").
    { iFrame. rewrite !fmap_insert. iFrame.
      rewrite (insert_id _ _ ()); first iFrame.
      rewrite lookup_fmap. by rewrite Hsome'. }
    iModIntro.
    wp_pures.
    simpl.
    replace (_+2*_)%Z with (Z.of_nat n).
    - iApply "HΦ". iFrame.
      iPureIntro. by eapply Forall_inv_tail.
    - apply Forall_cons in H as [??]. destruct n as [|[|[|[|]]]]; simpl; lia.
  Qed.
End impl2.


Section impl3.
  Context `{!conerisGS Σ, Hs : !ghost_mapG Σ val (), Hm : !abstract_tapesGS Σ }.
  Variable tb:nat.
  Local Opaque INR.
  (* (** Instantiate rand *) *)
  Local Definition rand_inv_pred3  (γ:gname*gname) : iProp Σ:=
    (∃ (m:gmap val (list nat)),
        (ghost_map_auth γ.1 1 ((λ _, ())<$>m)) ∗
        ● ((λ x, (S tb, x))<$>m)@ γ.2 ∗
        [∗ map] α ↦ns∈m, (∃ α', ⌜α = #lbl:α'⌝ ∗ (α' ↪N (S tb; ns) ))
    )%I.

  Definition is_rand3 N γ:=
    inv N (rand_inv_pred3 γ).

  Definition rand_tapes3 α ns (γ:gname*gname):=
    ((∃ ns', ⌜filter (λ x, x<=tb)%nat ns' = ns⌝ ∗ α◯↪N (S tb; ns') @γ.2) ∗
     ⌜Forall (λ x, x<=tb)%nat ns⌝)%I.

  Definition rand_token3 α (γ:gname*gname) :=
    (α ↪[γ.1] ())%I.
  
  #[local] Program Definition rand_spec3 : rand_spec' tb :=
    {| rand_allocate_tape:= (λ: "_", alloc #(S tb));
      rand_tape:= (rec: "f" "α":=
                     let: "res" := rand("α") #(S tb) in
                     if: "res" ≤ #tb then "res" else "f" "α"
                  ); 
      is_rand  := is_rand3;
      rand_tapes := rand_tapes3;
      rand_token := rand_token3;
    |}.
  Next Obligation.
    simpl.
    iIntros (????) "[(%&%&H1) %] [(%&%&H2) %]".
    iApply (abstract_tapes_frag_exclusive with "[$][$]").
  Qed.
  Next Obligation.
    simpl.
    iIntros (??) "H1 H2".
    iCombine "H1 H2" gives "%H".
    cbv in H. naive_solver.
  Qed.
  Next Obligation.
    simpl.
    iIntros (???) "(?&$)". 
  Qed.
  Next Obligation.
    simpl.
    iIntros (??????????) "#Hinv [H1 %] Herr".
    iMod (state_update_epsilon_err) as "(%ep & %Heps & Heps)".
    iRevert "H1 Herr".
    iApply (ec_ind_amp _ (S (S tb))%R with "[][$]"); try lra.
    { 
      pose proof (pos_INR_S (tb)). rewrite S_INR. lra.
    }
    clear ep Heps.
    iModIntro.
    iIntros (eps Heps) "#IH Heps (%ls & <- & Hfrag) Herr".
    iInv "Hinv" as ">(%&Hs&Hm&Ht)" "Hclose".
    iDestruct (abstract_tapes_agree with "[$][$]") as "%Hsome".
    rewrite lookup_fmap_Some in Hsome.
    destruct Hsome as (?&?&Hsome). simplify_eq.
    iDestruct (big_sepM_insert_acc with "[$]") as "[(%&%Heq&Ht) Hclose']"; first done.
    simplify_eq.
    iDestruct (ec_valid with "Herr") as "%".
    iCombine " Herr Heps" as "Herr'".
    iMod (state_update_presample_exp _ _ _ _ _
            (λ x, match decide (fin_to_nat x < S tb)%nat with
                  | left p => ε2 (nat_to_fin p)
                  | _ => ε + S (S tb)*eps
                                  end
            )%R with "[$][$]") as "(%n&Ht&Herr)".
    { intros. case_match; first done.
      apply Rplus_le_le_0_compat; first naive_solver.
      apply Rmult_le_pos; last lra.
      apply pos_INR.
    }
    {
      rewrite !SeriesC_scal_l in H1 *.
      assert (forall (x y z:R), x>0->1/x*y<=z <-> y<=z*x)%R as Hrewrite.
      { intros. rewrite -Rcomplements.Rle_div_l; last done.
        lra. 
      }
      rewrite !Hrewrite in H1 *; [|pose proof pos_INR_S (S tb); lra|pose proof pos_INR_S (tb); lra].
      rewrite !SeriesC_fin_sum in H1 *.
      rewrite -!SeriesC_nat_bounded in H1 *.
      rewrite (SeriesC_split_elem _ (S tb)%fin); last first.
      - apply ex_seriesC_nat_bounded.
      - intros. rewrite /extend_fin_to_R. repeat case_match; try lra.
        + naive_solver.
        + apply Rplus_le_le_0_compat; first lra.
          apply Rmult_le_pos; last lra. apply pos_INR.
      - rewrite SeriesC_singleton_dependent.
        rewrite bool_decide_eq_true_2; last done.
        rewrite /extend_fin_to_R.
        case_match; first lia.
        rewrite fin_to_nat_to_fin. case_match; first lia.
        trans (ε + S (S tb) * eps + ε * S tb)%R; last (rewrite !S_INR; lra).
        assert (SeriesC
                  (λ a : nat,
                     if bool_decide (a ≠ S tb)
                     then
                       if bool_decide (a ≤ S tb)
                       then
                         match le_lt_dec (S (S tb)) a with
                         | left _ => 0
                         | right h =>
                             match decide (nat_to_fin h < S tb)%nat with
                             | left p => ε2 (nat_to_fin p)
                             | right _ => ε + S (S tb) * eps
                             end
                         end
                       else 0
                     else 0) <=ε* S tb)%R; last lra.
        etrans; last exact.
        right.
        apply SeriesC_ext.
        rewrite /extend_fin_to_R.
        intros.
        case_bool_decide as K1; try case_bool_decide as K2; try case_match eqn : K3;
          try rewrite fin_to_nat_to_fin;
          try case_bool_decide as K4; try case_match eqn:K5; try case_match; try (done||lia).
        f_equal.
        apply fin_to_nat_inj.
        by rewrite !fin_to_nat_to_fin.  
    }
    iMod (abstract_tapes_presample with "[$][$]") as "[Hm H1]".
    iDestruct ("Hclose'" with "[$Ht]") as "Ht"; first done.
    iMod ("Hclose" with "[Hs Hm $Ht]").
    - rewrite !fmap_insert (insert_id _ _ ()); first iFrame.
      rewrite lookup_fmap. by rewrite Hsome.
    - case_match eqn:Hineq.
      + iFrame. iPureIntro. split.
        * rewrite filter_app. f_equal. rewrite filter_cons. case_match; try lia.
          by rewrite fin_to_nat_to_fin.
        * apply Forall_app; split; first done.
          apply Forall_singleton. pose proof fin_to_nat_lt n. rewrite fin_to_nat_to_fin. lia.
      + iDestruct (ec_split with "[$]") as "[Hε Heps]"; first lra.
        { apply Rmult_le_pos; last lra.
        apply pos_INR.
        } 
        iApply ("IH" with "[$][-Hε][$]").
        iFrame. iPureIntro.
        rewrite filter_app.
        rewrite filter_cons. case_match.
        * simpl in *. lia.
        * by rewrite filter_nil app_nil_r.
  Qed.
  Next Obligation.
    iIntros (???).
    rewrite /is_rand1/rand_inv_pred1.
    iMod (abstract_tapes_alloc ∅) as "(%&H1&_)".
    iMod (ghost_map_alloc_empty) as "(%&H2)".
    iMod (inv_alloc with "[H1 H2]"); last first.
    - iExists (_,_). by iFrame.
    - iNext. iExists ∅.
      rewrite !fmap_empty. by iFrame.
  Qed.
  Next Obligation.
    simpl.
    iIntros (?[??]?? Φ) "#Hinv HΦ".
    wp_pures.
    iInv "Hinv" as ">(%&Hs&Hm&Hts)" "Hclose".
    wp_apply (wp_alloc_tape); first done.
    iIntros (α) "Ht".
    iAssert (⌜m!!#lbl:α=None⌝)%I as "%Hnone".
    { destruct (_!!_) eqn:?; last done.
      iDestruct (big_sepM_insert_acc with "[$]") as "[(%&%&?) Hclose']"; first done.
      simplify_eq.
      by iDestruct (tapeN_tapeN_contradict with "[$][$]") as "%".
    }
    iMod (ghost_map_insert with "[$]") as "[Hs Htoken]"; first by erewrite lookup_fmap, Hnone.
    iMod (abstract_tapes_new with "[$]") as "[Hm ?]"; first by erewrite lookup_fmap, Hnone.
    iMod ("Hclose" with "[Hts Ht Hs Hm]").
    { iNext. iExists (<[_:=_]>_). rewrite !fmap_insert.
      iFrame.
      rewrite big_sepM_insert; last done.
      by iFrame.
    }
    iApply "HΦ". by iFrame.
  Qed.
  Next Obligation.
    iIntros (?[??]???? Hsubset Φ) "[#Hinv [(%ns'&%Hfilter&Htfrag) %Hforall]] HΦ".
    iApply fupd_pgl_wp.
    iInv "Hinv" as ">(%m&Hs&Hm&Hts)" "Hclose".
    iDestruct (abstract_tapes_agree with "[$][$]") as "%Hsome".
    rewrite lookup_fmap_Some in Hsome.
    destruct Hsome as (?&?&Hsome). simplify_eq.
    iDestruct (big_sepM_lookup_acc with "[$]") as "[(%&%&?) Hclose']"; first done.
    simplify_eq.
    iMod ("Hclose" with "[-Htfrag HΦ]") as "_"; iFrame.
    { iDestruct ("Hclose'" with "[-]") as "$". by iFrame. }
    iModIntro.
    simpl.
    clear m Hsome.
    iLöb as "IH" forall (ns' n ns Hfilter Hforall) "Htfrag HΦ".
    wp_pures.
    wp_bind (rand(_)_)%E.
    iInv "Hinv" as ">(%&Hs&Hm&Hts)" "Hclose".
    iDestruct (abstract_tapes_agree with "[$][$]") as "%Hsome".
    rewrite lookup_fmap_Some in Hsome.
    destruct Hsome as (?&?&Hsome). simplify_eq.
    iDestruct (big_sepM_insert_acc with "[$]") as "[(%&%&?) Hclose']"; first done.
    simplify_eq.
    destruct ns'.
    { rewrite filter_nil in Hfilter. simplify_eq. }
    wp_apply (wp_rand_tape with "[$]") as "[Htape %]".
    iMod (abstract_tapes_pop with "[$][$]") as "[Hm Htfrag]".
    iDestruct ("Hclose'" with "[$Htape]") as "Htapes"; first done.
    iMod ("Hclose" with "[-HΦ Htfrag]").
    { iFrame. rewrite !fmap_insert. iFrame.
      rewrite (insert_id _ _ ()); first iFrame.
      rewrite lookup_fmap. by rewrite Hsome. }
    iModIntro. wp_pures.
    case_bool_decide.
    - wp_pures. rewrite filter_cons in Hfilter.
      case_match; last lia. simplify_eq. iApply "HΦ". iFrame.
      iPureIntro. split; first done. by eapply Forall_inv_tail.
    - wp_pure. iApply ("IH" with "[][][$]").
      + rewrite filter_cons in Hfilter. case_match; [lia|done].
      + done.
      + done.
  Qed.
End impl3.
