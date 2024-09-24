(** * Hocap rand specs *)
From clutch.coneris Require Import coneris hocap.

Set Default Proof Using "Type*".


Class rand_spec `{!conerisGS Σ} := RandSpec
{
  (** * Operations *)
  rand_allocate_tape : val;
  rand_tape : val;
  (** * Ghost state *)
  (** The assumptions about [Σ] *)
  randG : gFunctors → Type;
  
  rand_error_name : Type;
  rand_tape_name: Type;
  (** * Predicates *)
  is_rand {L : randG Σ} (N:namespace)
    (γ1: rand_error_name) (γ2: rand_tape_name): iProp Σ;
  rand_error_auth {L : randG Σ} (γ: rand_error_name) (x:R): iProp Σ;
  rand_error_frag {L : randG Σ} (γ: rand_error_name) (x:R): iProp Σ;
  rand_tapes_auth {L : randG Σ} (γ: rand_tape_name) (m:gmap loc (nat * list nat)): iProp Σ;
  rand_tapes_frag {L : randG Σ} (γ: rand_tape_name) (α:loc) (ns: (nat * list nat)): iProp Σ;
  (** * General properties of the predicates *)
  #[global] is_rand_persistent {L : randG Σ} N γ1 γ2 ::
    Persistent (is_rand (L:=L) N γ1 γ2);
  #[global] rand_error_auth_timeless {L : randG Σ} γ x ::
    Timeless (rand_error_auth (L:=L) γ x);
  #[global] rand_error_frag_timeless {L : randG Σ} γ x ::
    Timeless (rand_error_frag (L:=L) γ x);
  #[global] rand_tapes_auth_timeless {L : randG Σ} γ m ::
    Timeless (rand_tapes_auth (L:=L) γ m);
  #[global] rand_tapes_frag_timeless {L : randG Σ} γ α ns ::
    Timeless (rand_tapes_frag (L:=L) γ α ns);
  #[global] rand_error_name_inhabited::
    Inhabited rand_error_name;
  #[global] rand_tape_name_inhabited::
    Inhabited rand_tape_name;

  rand_error_auth_exclusive {L : randG Σ} γ x1 x2:
    rand_error_auth (L:=L) γ x1 -∗ rand_error_auth (L:=L) γ x2 -∗ False;
  rand_error_frag_split {L : randG Σ} γ (x1 x2:nonnegreal):
  rand_error_frag (L:=L) γ x1 ∗ rand_error_frag (L:=L) γ x2 ⊣⊢
  rand_error_frag (L:=L) γ (x1+x2)%R ;
  rand_error_auth_valid {L : randG Σ} γ x:
    rand_error_auth (L:=L) γ x -∗ ⌜(0<=x<1)%R⌝;
  rand_error_frag_valid {L : randG Σ} γ x:
    rand_error_frag (L:=L) γ x -∗ ⌜(0<=x<1)%R⌝;
  rand_error_ineq {L : randG Σ} γ x1 x2:
    rand_error_auth (L:=L) γ x1 -∗ rand_error_frag (L:=L) γ x2 -∗ ⌜(x2 <= x1)%R ⌝;
  rand_error_decrease {L : randG Σ} γ (x1 x2:R):
     rand_error_auth (L:=L) γ x1 -∗ rand_error_frag (L:=L) γ x2 ==∗ rand_error_auth (L:=L) γ (x1-x2)%R;
  rand_error_increase {L : randG Σ} γ (x1:R) (x2:nonnegreal):
    (x1+x2<1)%R -> ⊢ rand_error_auth (L:=L) γ x1 ==∗
    rand_error_auth (L:=L) γ (x1+x2) ∗ rand_error_frag (L:=L) γ x2;

  rand_tapes_auth_exclusive {L : randG Σ} γ m m':
  rand_tapes_auth (L:=L) γ m -∗ rand_tapes_auth (L:=L) γ m' -∗ False;
  rand_tapes_frag_exclusive {L : randG Σ} γ α ns ns':
  rand_tapes_frag (L:=L) γ α ns -∗ rand_tapes_frag (L:=L) γ α ns' -∗ False;
  rand_tapes_agree {L : randG Σ} γ α m ns:
  rand_tapes_auth (L:=L) γ m -∗ rand_tapes_frag (L:=L) γ α ns -∗ ⌜ m!! α = Some (ns) ⌝;
  rand_tapes_valid {L : randG Σ} γ2 α tb ns:
    rand_tapes_frag (L:=L) γ2 α (tb, ns) -∗
    ⌜Forall (λ n, n<=tb)%nat ns⌝;
      rand_tapes_update {L : randG Σ} γ α m ns ns':
      Forall (λ n, n<=ns'.1)%nat ns'.2 ->
    rand_tapes_auth (L:=L) γ m -∗ rand_tapes_frag (L:=L) γ α ns ==∗
    rand_tapes_auth (L:=L) γ (<[α := ns']> m) ∗ rand_tapes_frag (L:=L) γ α ns';

  (** * Program specs *)
  rand_inv_create_spec {L : randG Σ} N E:
  ⊢ wp_update E (∃ γ1 γ2, is_rand (L:=L) N γ1 γ2);
  rand_err_convert_spec1 {L : randG Σ} N E ε γ1 γ2:
  ↑N ⊆ E->
  is_rand (L:=L) N γ1 γ2 -∗
  ↯ ε -∗
  wp_update E (rand_error_frag (L:=L) γ1 ε);
  rand_err_convert_spec2 {L : randG Σ} N E ε γ1 γ2:
  ↑N ⊆ E->
  is_rand (L:=L) N γ1 γ2 -∗
  rand_error_frag (L:=L) γ1 ε -∗
  wp_update E (↯ ε);
  rand_allocate_tape_spec {L: randG Σ} N E (tb:nat) γ1 γ2:
    ↑N ⊆ E->
    {{{ is_rand (L:=L) N γ1 γ2 }}}
      rand_allocate_tape #tb @ E
      {{{ (v:val), RET v;
          ∃ (α:loc), ⌜v=#lbl:α⌝ ∗ rand_tapes_frag (L:=L) γ2 α (tb, [])
      }}};
  rand_tape_spec_some {L: randG Σ} N E γ1 γ2 (P: iProp Σ) (Q:iProp Σ) (α:loc) (n:nat) (tb:nat) ns:
    ↑N⊆E ->
    {{{ is_rand (L:=L) N γ1 γ2 ∗
        □ (∀ (m:gmap loc (nat * list nat)), P ∗
           rand_tapes_auth (L:=L) γ2 m
            ={E∖↑N}=∗ ⌜m!!α=Some (tb, n::ns)⌝ ∗ Q ∗ rand_tapes_auth (L:=L) γ2 (<[α:=(tb, ns)]> m)) ∗
        ▷P
    }}}
      rand_tape #lbl:α #tb @ E
                       {{{ RET #n; Q }}}; 
  rand_presample_spec {L: randG Σ} N E ns α (tb:nat)
     (ε2 : list (fin (S tb)) -> R)
    (P : iProp Σ) num T γ1 γ2 ε :
    ↑N ⊆ E ->
    (∀ l, length l = num ->  0<= ε2 l)%R ->
    (SeriesC (λ l, if bool_decide (l ∈ enum_uniform_fin_list tb num) then ε2 l else 0) /((S tb)^num) <= ε)%R->
    is_rand (L:=L) N γ1 γ2 -∗
    □(∀ (ε': R) m, P ∗rand_error_auth (L:=L) γ1 (ε')%R ∗ rand_tapes_auth (L:=L) γ2 m ={E∖↑N}=∗
                   ⌜(ε<=ε')%R⌝ ∗ ⌜(m!!α = Some (tb, ns))⌝ ∗
                   P ∗rand_error_auth (L:=L) γ1 (ε')%R ∗ rand_tapes_auth (L:=L) γ2 m 
      ) -∗
    (□∀ (ε':R) ns' m, (P ∗ rand_error_auth (L:=L) γ1 (ε')%R ∗ ⌜length ns' = num⌝ ∗
                     rand_tapes_auth (L:=L) γ2 m
                    ) ={E∖↑N}=∗
                             (⌜(1<=ε2 ns' + (ε'-ε))%R⌝ ∨ (rand_error_auth (L:=L) γ1 (ε2 ns' + (ε'-ε))%R ∗
                                                       rand_tapes_auth (L:=L) γ2 (<[α:= (tb, ns++(fin_to_nat <$> ns'))]> m) ∗ T ns')))
        -∗
    P -∗ 
        wp_update E (∃ n, T n)
}.

Section impl.
  Local Opaque INR.
  (* (** Instantiate rand *) *)
  Class randG1 Σ := RandG1 { flipG1_error::hocap_errorGS Σ;
                             flipG1_tapes:: hocap_tapesGS Σ;
                      }.
  Local Definition rand_inv_pred1 `{!conerisGS Σ, !hocap_errorGS Σ, !hocap_tapesGS Σ} γ1 γ2:=
    (∃ (ε:R) (m:gmap loc (nat * list nat)) ,
        ↯ ε ∗ ●↯ ε @ γ1  ∗
        ([∗ map] α ↦ t ∈ m, α ↪N ( t.1 ; t.2 )) ∗
        ●m@γ2
    )%I.

  #[local] Program Definition rand_spec1 `{!conerisGS Σ}: rand_spec :=
    {| rand_allocate_tape:= (λ: "N", alloc "N");
      rand_tape:= (λ: "α" "N", rand("α") "N"); 
      randG := randG1;
      rand_error_name := gname;
      rand_tape_name := gname;
      is_rand _ N γ1 γ2 := inv N (rand_inv_pred1 γ1 γ2);
      rand_error_auth _ γ x := ●↯ x @ γ;
      rand_error_frag _ γ x := ◯↯ x @ γ;
      rand_tapes_auth _ γ m := (●m@γ)%I;
      rand_tapes_frag _ γ α ns := ((α ◯↪N (ns.1; ns.2) @ γ) ∗ ⌜Forall (λ x, x<=ns.1) ns.2⌝)%I;
    |}.
  Next Obligation.
    simpl.
    iIntros.
    iApply (hocap_error_auth_exclusive with "[$][$]").
  Qed.
  Next Obligation.
    simpl.
    iIntros.
    iApply (hocap_error_frag_split).
  Qed.
  Next Obligation.
    simpl.
    iIntros (?????) "H".
    iApply (hocap_error_auth_valid with "[$]").
  Qed.
  Next Obligation.
    simpl.
    iIntros (?????) "H".
    iApply (hocap_error_frag_valid with "[$]").
  Qed.
  Next Obligation.
    simpl.
    iIntros (??????) "H1 H2".
    iApply (hocap_error_ineq with "[$][$]").
  Qed.
  Next Obligation.
    iIntros.
    iApply (hocap_error_decrease with "[$][$]"). 
  Qed.
  Next Obligation.
    iIntros.
    by iApply (hocap_error_increase with "[$]").
  Qed.
  Next Obligation.
    simpl.
    iIntros (??????) "H1 H2".
    by iDestruct (ghost_map_auth_valid_2 with "[$][$]") as "[%H _]".
  Qed.
  Next Obligation.
    simpl.
    iIntros (???????) "[H1 %] [H2 %]".
    iDestruct (ghost_map_elem_frac_ne with "[$][$]") as "%"; last done.
    rewrite dfrac_op_own dfrac_valid_own. by intro.
  Qed.
  Next Obligation.
    simpl.
    iIntros (??????[]) "? [??]".
    by iDestruct (hocap_tapes_agree with "[$][$]") as "%H".
  Qed.
  Next Obligation.
    simpl.
    by iIntros (???????) "[? $]". 
  Qed.
  Next Obligation.
    iIntros (??????[??][??]?) "?[? %]".
    iMod (hocap_tapes_update with "[$][$]") as "[??]".
    by iFrame.
  Qed.
  Next Obligation.
    simpl.
    iIntros (?????).
    iApply fupd_wp_update_ret.
    unshelve iMod (hocap_error_alloc (nnreal_zero)) as "(%γ1 & ? & ?)"; simpl; [rewrite INR_0; lra|].
    iMod ec_zero as "?".
    iMod (hocap_tapes_alloc ∅) as "(%γ2 & H4 & H5)".
    iMod (inv_alloc _ _ (rand_inv_pred1 γ1 γ2) with "[-]").
    { iFrame. by iNext. }
    by iFrame.
  Qed.
  Next Obligation.
    simpl.
    iIntros (????? ε ???) "#Hinv Herr".
    iApply fupd_wp_update_ret.
    iInv "Hinv" as ">(%ε'&%&H1&?&?&?)" "Hclose".
    iDestruct (ec_valid with "[$Herr]") as "%".
    iCombine "Herr H1" as "?".
    iDestruct (ec_valid with "[$]") as "[% %]".
    simpl in *.
    unshelve iMod (hocap_error_increase _ _ (mknonnegreal ε _) with "[$]") as "[? Hfrag]"; [naive_solver|simpl;lra|].
    simpl.
    iMod ("Hclose" with "[-Hfrag]") as "_"; last done.
    iFrame. iApply (ec_eq with "[$]"). lra.
  Qed.
  Next Obligation. 
    simpl.
    iIntros (????? ε ???) "#Hinv Herr".
    iApply fupd_wp_update_ret.
    iInv "Hinv" as ">(%ε'&%&H1&?&?&?)" "Hclose".
    iDestruct (hocap_error_frag_valid with "[$]") as "%".
    iDestruct (ec_valid with "[$]") as "%".
    iDestruct (hocap_error_ineq with "[$][$]") as "%".
    unshelve iMod (hocap_error_decrease with "[$][$]") as "?".
    iDestruct (ec_eq with "[$]") as "?"; last first.
    { iDestruct (ec_split with "[$]") as "[? H]"; last first.
      - iMod ("Hclose" with "[-H]") as "_"; last done.
        iFrame.
      - naive_solver.
      - lra.
    }
    lra.
  Qed.
  Next Obligation.
    simpl.
    iIntros (????????? Φ) "#Hinv HΦ".
    wp_pures.
    iInv "Hinv" as "(%&%&?&?&?&?)" "Hclose".
    wp_apply (wp_alloc_tape); first done.
    iIntros (α) "Hα".
    iDestruct (hocap_tapes_notin with "[$][$]") as "%".
    iMod (hocap_tapes_new _ _ α tb [] with "[$]") as "[?H]"; first done.
    iMod ("Hclose" with "[-H HΦ]").
    { iModIntro. iFrame.
      rewrite big_sepM_insert; [iFrame|done].
    }
    iApply "HΦ".
    by iFrame.
  Qed.
  Next Obligation.
  simpl.
  iIntros (?????????????? Φ) "(#Hinv & #Hvs & HP) HΦ".
  wp_pures.
  wp_bind (rand(_) _)%E.
  iInv "Hinv" as ">(%&%&H1&H2&H3&H4)" "Hclose".
  iMod ("Hvs" with "[$]") as "(%&HQ&Hauth)".
  iDestruct (big_sepM_insert_acc with "[$]") as "[Htape H3]"; first done.
  simpl.
  wp_apply (wp_rand_tape with "[$]") as "[Htape %]".
  iMod ("Hclose" with "[- HΦ HQ]") as "_".
  { iExists _, (<[α:=_]> m).
    iFrame.
    iApply "H3". by iNext.
  }
  by iApply "HΦ".
Qed.
Next Obligation.
  simpl.
  iIntros (??????????????? Hsubset Hpos Hineq) "#Hinv #Hchange #Hvs HP".
  iApply wp_update_state_step_coupl.
  iIntros (σ1 ε_supply) "((Hheap&Htapes)&Hε)".
  iMod (inv_acc with "Hinv") as "[>(%ε' & % & H1 & H2 & H3 & H4 ) Hclose]"; [done|].
  iMod ("Hchange" with "[$]") as "(%&%&HP & H2 &H4)". 
  (* iDestruct (hocap_tapes_agree with "[$][$]") as "%K". *)
  iDestruct (big_sepM_insert_acc with "[$]") as "[Htape H3]"; first done.
  simpl.
  iDestruct (tapeN_lookup with "[$][$]") as "(%&%&%Heq)".
  iDestruct (ec_supply_bound with "[$][$]") as "%".
  iMod (ec_supply_decrease with "[$][$]") as (ε'' ε_rem -> Hε') "Hε_supply". subst.
  iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
  iApply (state_step_coupl_iterM_state_adv_comp_con_prob_lang num α); first done.
  unshelve iExists (λ x, mknonnegreal (if length x =? num then ε2 x + (ε''-ε) else 1)%R _).
  { case_match; last (simpl;lra).
    apply Rplus_le_le_0_compat; last (simpl in *; lra).
    apply Hpos. by apply Nat.eqb_eq.
  } 
  iSplit.
  { iPureIntro.
    simpl.
    rewrite (SeriesC_subset (λ x, (x∈enum_uniform_fin_list tb num))); last first.
    - intros a. intros K.
      rewrite elem_of_enum_uniform_fin_list in K.
      case_match eqn :H4; last done.
      by rewrite Nat.eqb_eq in H4.
    - erewrite (SeriesC_ext _ (λ a, 1/S tb ^ num * (if bool_decide (a ∈ enum_uniform_fin_list tb num) then ε2 a else 0) + (if bool_decide (a ∈ enum_uniform_fin_list tb num) then 1/S tb ^ num * (ε''-ε) else 0)))%R; last first.
      + intros n.
        case_bool_decide; last lra.
        replace (_ =? _) with true; last first.
        * symmetry. rewrite Nat.eqb_eq. by rewrite -elem_of_enum_uniform_fin_list.
        * simpl. lra.
      + rewrite SeriesC_plus; [|apply ex_seriesC_scal_l, ex_seriesC_list|apply ex_seriesC_list..].
        rewrite SeriesC_list_2; last apply NoDup_enum_uniform_fin_list.
        rewrite SeriesC_scal_l enum_uniform_fin_list_length pow_INR.
        replace (1/_*_*_)%R with (ε''-ε)%R; first (simpl; lra).
        rewrite Rmult_comm -Rmult_assoc Rdiv_1_l Rmult_inv_r; first lra.
        apply pow_nonzero.
        pose proof pos_INR_S tb; lra.
  }
  iIntros (sample) "<-".
  destruct (Rlt_decision (nonneg ε_rem + (ε2 sample + (ε''-ε))%R) 1%R) as [Hdec|Hdec]; last first.
  { apply Rnot_lt_ge, Rge_le in Hdec.
    iApply state_step_coupl_ret_err_ge_1.
    simpl. simpl in *. rewrite Nat.eqb_refl. lra.
  }
  iApply state_step_coupl_ret.
  unshelve iMod (ec_supply_increase _ (mknonnegreal (ε2 sample + (ε''-ε))%R _) with "Hε_supply") as "[Hε_supply Hε]".
  { apply Rplus_le_le_0_compat; simpl in *; [naive_solver|lra]. }
  { simpl. done. }
  simpl.
  iMod (tapeN_update_append' _ _ _ _ sample with "[$][$]") as "[Htapes Htape]".
  (* iMod (hocap_tapes_update _ _ _ _ _ _ ((fin_to_nat <$> ns')++(fin_to_nat <$> sample)) with "[$][$]") as "[H4 Hfrag]". *)
  iMod "Hclose'" as "_".
  iMod ("Hvs" $! ε'' sample  with "[$HP $H2 $H4]") as "[%|(Hauth & H2 & HT)]"; first done.
  { iExFalso. iApply (ec_contradict with "[$]"). exact. }
  iMod ("Hclose" with "[$Hε $Hauth Htape H3 $H2]") as "_".
  { iNext.
    by iApply "H3".
  }
  iApply fupd_mask_intro_subseteq; first set_solver.
  iFrame. 
  erewrite (nnreal_ext _ _); first done.
  simpl. by rewrite Nat.eqb_refl.
Qed.

End impl.


(** * EXPERIMENT *)

Class rand_spec' `{!conerisGS Σ} := RandSpec'
{
  (** * Operations *)
  rand_allocate_tape' : val;
  rand_tape' : val;
  (** * Ghost state *)
  (** The assumptions about [Σ] *)
  randG' : gFunctors → Type;
  
  rand_tape_name': Type;
  (** * Predicates *)
  is_rand' {L : randG' Σ} (N:namespace)
    (γ1: rand_tape_name') : iProp Σ;
  rand_tapes_auth' {L : randG' Σ} (γ: rand_tape_name') (m:gmap loc (nat * list nat)): iProp Σ;
  rand_tapes_frag' {L : randG' Σ} (γ: rand_tape_name') (α:loc) (ns: (nat * list nat)): iProp Σ;
  (** * General properties of the predicates *)
  #[global] is_rand_persistent' {L : randG' Σ} N γ1 ::
    Persistent (is_rand' (L:=L) N γ1);
  #[global] rand_tapes_auth_timeless' {L : randG' Σ} γ m ::
    Timeless (rand_tapes_auth' (L:=L) γ m);
  #[global] rand_tapes_frag_timeless' {L : randG' Σ} γ α ns ::
    Timeless (rand_tapes_frag' (L:=L) γ α ns);
  #[global] rand_tape_name_inhabited' ::
    Inhabited rand_tape_name';

  rand_tapes_auth_exclusive' {L : randG' Σ} γ m m':
  rand_tapes_auth' (L:=L) γ m -∗ rand_tapes_auth' (L:=L) γ m' -∗ False;
  rand_tapes_frag_exclusive' {L : randG' Σ} γ α ns ns':
  rand_tapes_frag' (L:=L) γ α ns -∗ rand_tapes_frag' (L:=L) γ α ns' -∗ False;
  rand_tapes_agree' {L : randG' Σ} γ α m ns:
  rand_tapes_auth' (L:=L) γ m -∗ rand_tapes_frag' (L:=L) γ α ns -∗ ⌜ m!! α = Some (ns) ⌝;
  rand_tapes_valid' {L : randG' Σ} γ2 α tb ns:
    rand_tapes_frag' (L:=L) γ2 α (tb, ns) -∗
    ⌜Forall (λ n, n<=tb)%nat ns⌝ ;
  rand_tapes_update' {L : randG' Σ} γ α m ns ns':
  Forall (λ x, x<=ns'.1) ns'.2 ->
    rand_tapes_auth' (L:=L) γ m -∗ rand_tapes_frag' (L:=L) γ α ns ==∗
    rand_tapes_auth' (L:=L) γ (<[α := ns']> m) ∗ rand_tapes_frag' (L:=L) γ α ns';

  (** * Program specs *)
  rand_inv_create_spec' {L : randG' Σ} N E:
  ⊢ wp_update E (∃ γ1, is_rand' (L:=L) N γ1);
  rand_allocate_tape_spec' {L: randG' Σ} N E (tb:nat) γ2:
    ↑N ⊆ E->
    {{{ is_rand' (L:=L) N γ2 }}}
      rand_allocate_tape' #tb @ E
      {{{ (v:val), RET v;
          ∃ (α:loc), ⌜v=#lbl:α⌝ ∗ rand_tapes_frag' (L:=L) γ2 α (tb, [])
      }}};
  rand_tape_spec_some' {L: randG' Σ} N E γ2 (P: iProp Σ) (Q:iProp Σ) (α:loc) (n:nat) (tb:nat) ns:
    ↑N⊆E ->
    {{{ is_rand' (L:=L) N γ2 ∗
        □ (∀ (m:gmap loc (nat * list nat)), P ∗
           rand_tapes_auth' (L:=L) γ2 m
            ={E∖↑N}=∗ ⌜m!!α=Some (tb, n::ns)⌝ ∗ Q ∗ rand_tapes_auth' (L:=L) γ2 (<[α:=(tb, ns)]> m)) ∗
      ▷ P
    }}}
      rand_tape' #lbl:α #tb @ E
                       {{{ RET #n; Q }}};
  rand_presample_spec' {L: randG' Σ} N E ns α (tb:nat)
     (ε2 : list (fin (S tb)) -> R)
    (P : iProp Σ) num T γ2 (ε:nonnegreal) :
    ↑N ⊆ E ->
    (∀ l, length l = num ->  0<= ε2 l)%R ->
    (SeriesC (λ l, if bool_decide (l ∈ enum_uniform_fin_list tb num) then ε2 l else 0) /((S tb)^num) <= ε)%R->
    is_rand' (L:=L) N γ2 -∗
    □(∀ (ε': nonnegreal) m, P ∗ err_interp ε' ∗ rand_tapes_auth' (L:=L) γ2 m ={E∖↑N}=∗
                   ⌜(ε<=ε')%R⌝ ∗ ⌜(m!!α = Some (tb, ns))⌝ ∗
                   P ∗err_interp ε' ∗ rand_tapes_auth' (L:=L) γ2 m
      ) -∗
    (□∀ (ε': nonnegreal) ns' m, (P ∗ err_interp ε' ∗ ⌜length ns' = num⌝ ∗
                     rand_tapes_auth' (L:=L) γ2 m
                    ) ={E∖↑N}=∗
                                (⌜(1<=ε2 ns' + (ε'-ε))%R⌝ ∨ ∃ (ε_final:nonnegreal),
                                    ⌜(nonneg ε_final = ε2 ns' + (ε'-ε))%R ⌝ ∗
                                    (err_interp ε_final ∗
                                                       rand_tapes_auth' (L:=L) γ2 (<[α:= (tb, ns++(fin_to_nat <$> ns'))]> m) ∗ T ns')))
        -∗
    P -∗
        wp_update E (∃ n, T n)
}.

Section impl'.
  Local Opaque INR.
  (* (** Instantiate rand *) *)
  Class randG1' Σ := RandG1' { 
                             flipG1_tapes':: hocap_tapesGS Σ;
                      }.
  Local Definition rand_inv_pred1' `{!conerisGS Σ, !hocap_tapesGS Σ} γ2:=
    (∃ (m:gmap loc (nat * list nat)) ,
        ([∗ map] α ↦ t ∈ m, α ↪N ( t.1 ; t.2 )) ∗
        ●m@γ2
    )%I.

  #[local] Program Definition rand_spec1' `{!conerisGS Σ}: rand_spec' :=
    {| rand_allocate_tape':= (λ: "N", alloc "N");
      rand_tape':= (λ: "α" "N", rand("α") "N"); 
      randG' := randG1';
      rand_tape_name' := gname;
      is_rand' _ N γ2 := inv N (rand_inv_pred1' γ2);
      rand_tapes_auth' _ γ m := (●m@γ)%I;
      rand_tapes_frag' _ γ α ns := (α ◯↪N (ns.1; ns.2) @ γ ∗ ⌜Forall (λ x, x<=ns.1) ns.2⌝)%I;
    |}.
  Next Obligation.
    simpl.
    iIntros (??????) "H1 H2".
    by iDestruct (ghost_map_auth_valid_2 with "[$][$]") as "[%H _]".
  Qed.
  Next Obligation.
    simpl.
    iIntros (???????) "[H1 %] [H2 %]".
    iDestruct (ghost_map_elem_frac_ne with "[$][$]") as "%"; last done.
    rewrite dfrac_op_own dfrac_valid_own. by intro.
  Qed.
  Next Obligation.
    simpl.
    iIntros (??????[]) "?[? %]".
    by iDestruct (hocap_tapes_agree with "[$][$]") as "%".
  Qed.
  Next Obligation.
    simpl.
    by iIntros (???????) "[? $]".
  Qed.
  Next Obligation.
    iIntros (??????[][]?) "?[? %]".
    iMod (hocap_tapes_update with "[$][$]") as "[??]".
    by iFrame.
  Qed.
  Next Obligation.
    simpl.
    iIntros (?????).
    iApply fupd_wp_update_ret.
    iMod (hocap_tapes_alloc ∅) as "(%γ2 & H4 & H5)".
    iMod (inv_alloc _ _ (rand_inv_pred1' γ2) with "[-]").
    { iFrame. by iNext. }
    by iFrame.
  Qed.
  Next Obligation.
    simpl.
    iIntros (???????? Φ) "#Hinv HΦ".
    wp_pures.
    iInv "Hinv" as "(%&?&?)" "Hclose".
    wp_apply (wp_alloc_tape); first done.
    iIntros (α) "Hα".
    iDestruct (hocap_tapes_notin with "[$][$]") as "%".
    iMod (hocap_tapes_new _ _ α tb [] with "[$]") as "[?H]"; first done.
    iMod ("Hclose" with "[-H HΦ]").
    { iModIntro. iFrame.
      rewrite big_sepM_insert; [iFrame|done].
    }
    iApply "HΦ".
    by iFrame.
  Qed.
  Next Obligation.
  simpl.
  iIntros (????????????? Φ) "(#Hinv & #Hvs & HP) HΦ".
  wp_pures.
  wp_bind (rand(_) _)%E.
  iInv "Hinv" as ">(%&H3&H4)" "Hclose".
  iMod ("Hvs" with "[$]") as "(%&HQ&Hauth)".
  iDestruct (big_sepM_insert_acc with "[$]") as "[Htape H3]"; first done.
  simpl.
  wp_apply (wp_rand_tape with "[$]") as "[Htape %]".
  iMod ("Hclose" with "[- HΦ HQ]") as "_".
  { iExists (<[α:=_]> m).
    iFrame.
    iApply "H3". by iNext.
  }
  by iApply "HΦ".
Qed.
Next Obligation.
  simpl.
  iIntros (?????????????? Hsubset Hpos Hineq) "#Hinv #Hcheck #Hvs HP ".
  iApply wp_update_state_step_coupl.
  iIntros (σ1 ε_supply) "((Hheap&Htapes)&Hε)".
  iMod (inv_acc with "Hinv") as "[>(% & H3 & H4 ) Hclose]"; [done|].
  iMod ("Hcheck" with "[$]") as "(%&%&HP&Hε& H4)".
  iDestruct (big_sepM_insert_acc with "[$]") as "[Htape H3]"; first done.
  simpl.
  iDestruct (tapeN_lookup with "[$][$]") as "(%&%&%Heq)".
  (* iDestruct (ec_supply_bound with "[$][$]") as "%". *)
  (* iMod (ec_supply_decrease with "[$][$]") as (ε'' ε_rem -> Hε') "Hε_supply". subst. *)
  iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
  unshelve epose (ε_rem := mknonnegreal (ε_supply-ε) _).
  { simpl in *. lra. }
  replace (ε_supply) with (ε_rem + ε)%NNR; last first.
  { rewrite /ε_rem. apply nnreal_ext. simpl. lra. }
  iApply (state_step_coupl_iterM_state_adv_comp_con_prob_lang num α); first done.
  unshelve iExists (λ x, mknonnegreal (if length x =? num then ε2 x else 1)%R _).
  { case_match; last (simpl;lra). apply Hpos. by rewrite -Nat.eqb_eq. }
  iSplit.
  { iPureIntro.
    simpl. etrans; last exact.
    rewrite (Rdiv_def (SeriesC _)(S tb ^num)%R) -SeriesC_scal_r.
    apply SeriesC_le; last apply ex_seriesC_scal_r, ex_seriesC_list.
    intros. rewrite elem_of_enum_uniform_fin_list'.
    case_match; last lra.
    split; last lra.
    apply Rmult_le_pos; last (apply Hpos; by rewrite -Nat.eqb_eq).
    rewrite -pow_INR. apply Rdiv_INR_ge_0.
  }
  iIntros (sample) "<-".
  destruct (Rlt_decision (nonneg ε_rem + (ε2 sample)%R) 1%R) as [Hdec|Hdec]; last first.
  { apply Rnot_lt_ge, Rge_le in Hdec.
    iApply state_step_coupl_ret_err_ge_1.
    simpl. simpl in *. rewrite Nat.eqb_refl. lra.
  }
  iApply state_step_coupl_ret.
  simpl.
  rewrite -Heq.
  iMod (tapeN_update_append' _ _ _ _ sample with "[$][$]") as "[Htapes Htape]".
  iMod "Hclose'" as "_".
  iMod ("Hvs" $! _ sample  with "[$HP $H4 $Hε]") as "Hor"; first done.  
  iDestruct "Hor" as "[%|(%ε_final & %Heq' & Hε & Hauth & HT)]".
  { exfalso. simpl in *. lra. }
  iMod ("Hclose" with "[$Hauth Htape H3 ]") as "_".
  { iNext.
    by iApply "H3".
  }
  iApply fupd_mask_intro_subseteq; first set_solver.
  iFrame. 
  erewrite (nnreal_ext (_+_)%NNR _); first done.
  simpl. rewrite Nat.eqb_refl. simpl in *. lra.
Qed.
  
End impl'.

Section checks.
  Context `{H: conerisGS Σ, r1:@rand_spec Σ H, r2:@rand_spec' Σ H, L:randG Σ, L': randG' Σ}.

  Lemma wp_rand_alloc_tape NS (N:nat) E γ1 γ2 :
    ↑NS ⊆ E ->
    {{{ is_rand (L:=L) NS γ1 γ2 }}} rand_allocate_tape #N @ E {{{ α, RET #lbl:α; rand_tapes_frag (L:=L) γ2 α (N,[]) }}}.
  Proof.
    iIntros (Hsubset Φ) "#Hinv HΦ".
    wp_apply (rand_allocate_tape_spec with "[//]"); first exact.
    iIntros (?) "(%&->&?)".
    by iApply "HΦ".
  Qed.

  Lemma wp_rand_alloc_tape' NS (N:nat) E γ2:
    ↑NS ⊆ E ->
    {{{ is_rand' (L:=L') NS γ2 }}} rand_allocate_tape' #N @ E {{{ α, RET #lbl:α; rand_tapes_frag' (L:=L') γ2 α (N,[]) }}}.
  Proof.
    iIntros (Hsubset Φ) "#Hinv HΦ".
    wp_apply (rand_allocate_tape_spec' with "[//]"); first exact.
    iIntros (?) "(%&->&?)".
    by iApply "HΦ".
  Qed.

  Lemma wp_rand_tape_1 NS (N:nat) E γ1 γ2 n ns α:
    ↑NS ⊆ E ->
    {{{ is_rand (L:=L) NS γ1 γ2 ∗ ▷ rand_tapes_frag (L:=L) γ2 α (N, n :: ns) }}}
      rand_tape #lbl:α #N@ E
                       {{{ RET #(LitInt n); rand_tapes_frag (L:=L) γ2 α (N, ns) ∗ ⌜n <= N⌝ }}}.
  Proof.
    iIntros (Hsubset Φ) "(#Hinv & Hfrag) HΦ".
    wp_apply (rand_tape_spec_some _ _ _ _ _ (⌜n<=N⌝ ∗ rand_tapes_frag _ _ _)%I with "[Hfrag]"); first exact.
    - iSplit; first done. iSplit; last iApply "Hfrag".
      iModIntro.
      iIntros (?) "[Hfrag Hauth]".
      iDestruct (rand_tapes_agree with "[$][$]") as "%".
      iDestruct (rand_tapes_valid with "[$Hfrag]") as "%K".
      inversion K; subst. 
      iMod (rand_tapes_update _ _ _ _  (N, ns) with "[$][$]") as "[Hauth Hfrag]"; first done.
      iFrame "Hauth". iModIntro.
      iFrame.
      by iPureIntro.
    - iIntros "[??]". iApply "HΦ".
      iFrame.
  Qed.

  Lemma wp_rand_tape_2 NS (N:nat) E γ2 n ns α:
    ↑NS ⊆ E ->
    {{{ is_rand' (L:=L') NS γ2 ∗ ▷ rand_tapes_frag' (L:=L') γ2 α (N, n :: ns) }}}
      rand_tape' #lbl:α #N@ E
                       {{{ RET #(LitInt n); rand_tapes_frag' (L:=L') γ2 α (N, ns) ∗ ⌜n <= N⌝ }}}.
  Proof.
    iIntros (Hsubset Φ) "(#Hinv &>Hfrag) HΦ".
    wp_apply (rand_tape_spec_some' _ _ _ _ (⌜n<=N⌝ ∗ rand_tapes_frag' _ _ _)%I with "[Hfrag]"); first exact.
    - iSplit; first done. iSplit; last iApply "Hfrag".
      iModIntro.
      iIntros (?) "[Hfrag Hauth]".
      iDestruct (rand_tapes_agree' with "[$][$]") as "%".
      iDestruct (rand_tapes_valid' with "[$Hfrag]") as "%K".
      inversion K; subst. 
      iMod (rand_tapes_update' _ _ _ _  (N, ns) with "[$][$]") as "[Hauth Hfrag]"; first done.
      iFrame "Hauth". iModIntro.
      iFrame.
      by iPureIntro.
    - iIntros "[??]". iApply "HΦ".
      iFrame.
  Qed.

  Lemma wp_presample_adv_comp_rand_tape (N : nat) NS E α ns (ε1 : R) (ε2 : fin (S N) -> R) γ1 γ2:
    ↑NS ⊆ E ->
    (∀ n, 0<=ε2 n)%R ->
    (SeriesC (λ n, (1 / (S N)) * ε2 n)%R <= ε1)%R →
    is_rand (L:=L) NS γ1 γ2 -∗
    ▷ rand_tapes_frag (L:=L) γ2 α (N, ns) -∗
    rand_error_frag (L:=L) γ1 ε1 -∗
    wp_update E (∃ n, rand_error_frag (L:=L) γ1 (ε2 n) ∗ rand_tapes_frag (L:=L) γ2 α (N, ns ++[fin_to_nat n]))%I.
  Proof.
    iIntros (Hsubset Hpos Hineq) "#Hinv >Htape Herr".
    iMod (rand_presample_spec _ _ _ _ _ (λ l, match l with
                                              | [x] => ε2 x
                                              | _ => 1%R
                                              end
            ) 
            (rand_tapes_frag (L:=L) γ2 α (N, ns) ∗rand_error_frag (L:=L) γ1 ε1) 1%nat
            (λ ls, ∃ n, ⌜ls=[n]⌝ ∗ rand_error_frag γ1 (ε2 n) ∗ rand_tapes_frag γ2 α (N, ns ++ [fin_to_nat n]))%I
           with "[//][][][$Htape $Herr]") as "(%l&%sample & -> & Herr &Htape)".
    - done.
    - by intros [|?[|]].
    - etrans; last exact.
      etrans; last eapply (SeriesC_le_inj _ (λ l, match l with |[x] => Some x | _ => None end)).
      + rewrite Rdiv_def -SeriesC_scal_r. apply Req_le_sym.
        apply SeriesC_ext.
        intros. case_match; subst.
        * rewrite bool_decide_eq_false_2; first (simpl;lra).
          by rewrite elem_of_enum_uniform_fin_list.
        * case_match; last first.
          { rewrite bool_decide_eq_false_2; first (simpl;lra).
            by rewrite elem_of_enum_uniform_fin_list. }
          rewrite bool_decide_eq_true_2; last by apply elem_of_enum_uniform_fin_list.
          simpl.
          rewrite Rdiv_def Rmult_1_r; lra.
      + intros. apply Rmult_le_pos; last done.
        apply Rdiv_INR_ge_0.
      + intros. repeat case_match; by simplify_eq.
      + apply ex_seriesC_finite.
    - iModIntro.
      iIntros (??) "([??]&?&?)".
      iDestruct (rand_error_ineq with "[$][$]") as "%".
      iDestruct (rand_tapes_agree with "[$][$]") as "%".
      iModIntro. iFrame.
      by iPureIntro.
    - iModIntro.
      iIntros (?[|sample[|]]?) "([??]&?&%&?)"; try done.
      destruct (Rlt_decision (ε2 sample + (ε' - ε1))%R 1%R).
      + iRight.
        iMod (rand_error_decrease with "[$][$]") as "?".
        unshelve iMod (rand_error_increase _ _ (mknonnegreal (ε2 sample) _) with "[$]") as "[? ?]"; first done.
        * simpl. lra.
        * simpl. iFrame.
          iDestruct (rand_tapes_valid with "[$]") as "%".
          iMod (rand_tapes_update with "[$][$]") as "[$?]".
          -- rewrite Forall_app; split; first done.
             rewrite Forall_singleton.
             pose proof fin_to_nat_lt sample; simpl. lia.
          -- iFrame.
             iModIntro. iSplit; last done.
             replace (_-_+_)%R with (ε2 sample + (ε' - ε1))%R; first done.
             lra.
      + iLeft.
        iPureIntro. lra.
    - iModIntro. iFrame.
  Qed.

  Lemma wp_presample_adv_comp_rand_tape' (N : nat) NS E α ns (ε1 : R) (ε2 : fin (S N) -> R) γ2:
    ↑NS ⊆ E ->
    (∀ n, 0<=ε2 n)%R ->
    (SeriesC (λ n, (1 / (S N)) * ε2 n)%R <= ε1)%R →
    is_rand' (L:=L') NS γ2 -∗
    ▷ rand_tapes_frag' (L:=L') γ2 α (N, ns) -∗
    ↯ ε1 -∗
    wp_update E (∃ n, ↯ (ε2 n) ∗ rand_tapes_frag' (L:=L') γ2 α (N, ns ++[fin_to_nat n]))%I.
  Proof.
    iIntros (Hsubset Hpos Hineq) "#Hinv >Htape Herr".
    iDestruct (ec_valid with "[$]") as "%Hpos'".
    destruct Hpos' as [Hpos' ?].
    iMod (rand_presample_spec' _ _ _ _ _ (λ l, match l with
                                              | [x] => ε2 x
                                              | _ => 1%R
                                              end
            ) 
            (rand_tapes_frag' (L:=L') γ2 α (N, ns) ∗ ↯ ε1) 1%nat
            (λ ls, ∃ n, ⌜ls=[n]⌝ ∗ ↯ (ε2 n) ∗ rand_tapes_frag' γ2 α (N, ns ++ [fin_to_nat n]))%I
            _ (mknonnegreal ε1 Hpos')
           with "[//][][][$Htape $Herr]") as "(%l&%sample & -> & Herr &Htape)".
    - done.
    - by intros [|?[|]].
    - etrans; last eapply Hineq.
      etrans; last eapply (SeriesC_le_inj _ (λ l, match l with |[x] => Some x | _ => None end)).
      + rewrite Rdiv_def -SeriesC_scal_r. apply Req_le_sym.
        apply SeriesC_ext.
        intros. case_match; subst.
        * rewrite bool_decide_eq_false_2; first (simpl;lra).
          by rewrite elem_of_enum_uniform_fin_list.
        * case_match; last first.
          { rewrite bool_decide_eq_false_2; first (simpl;lra).
            by rewrite elem_of_enum_uniform_fin_list. }
          rewrite bool_decide_eq_true_2; last by apply elem_of_enum_uniform_fin_list.
          simpl.
          rewrite Rdiv_def Rmult_1_r; lra.
      + intros. apply Rmult_le_pos; last done.
        apply Rdiv_INR_ge_0.
      + intros. repeat case_match; by simplify_eq.
      + apply ex_seriesC_finite.
    - iModIntro.
      iIntros (??) "([??]&?&?)".
      iDestruct (ec_supply_bound with "[$][$]") as "%".
      iDestruct (rand_tapes_agree' with "[$][$]") as "%".
      iModIntro. iFrame.
      by iPureIntro.
    - iModIntro.
      iIntros (?[|sample[|]]?) "([??]&?&%&?)"; try done.
      destruct (Rlt_decision (ε2 sample + (ε' - ε1))%R 1%R).
      + iRight.
        iMod (ec_supply_decrease with "[$][$]") as "(%&%&->&<-&?)".
        unshelve iMod (ec_supply_increase _ (mknonnegreal (ε2 sample) _) with "[$]") as "[? ?]"; first done.
        * simpl. simpl in *. lra.
        * simpl. iFrame.
          iDestruct (rand_tapes_valid' with "[$]") as "%".
          iMod (rand_tapes_update' with "[$][$]") as "[$?]".
          -- rewrite Forall_app; split; first done.
             rewrite Forall_singleton.
             pose proof fin_to_nat_lt sample; simpl. lia.
          -- iFrame.
             iModIntro. iSplit; last done.
             simpl.
             iPureIntro. lra.
      + iLeft.
        iPureIntro. simpl; simpl in *. lra.
    - iModIntro. iFrame.
  Qed.
    
End checks.
