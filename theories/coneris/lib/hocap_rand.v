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
  
  rand_tape_name: Type;
  (** * Predicates *)
  is_rand {L : randG Σ} (N:namespace)
    (γ1: rand_tape_name) : iProp Σ;
  rand_tapes_auth {L : randG Σ} (γ: rand_tape_name) (m:gmap loc (nat * list nat)): iProp Σ;
  rand_tapes_frag {L : randG Σ} (γ: rand_tape_name) (α:loc) (ns: (nat * list nat)): iProp Σ;
  (** * General properties of the predicates *)
  #[global] is_rand_persistent {L : randG Σ} N γ1 ::
    Persistent (is_rand (L:=L) N γ1);
  #[global] rand_tapes_auth_timeless {L : randG Σ} γ m ::
    Timeless (rand_tapes_auth (L:=L) γ m);
  #[global] rand_tapes_frag_timeless {L : randG Σ} γ α ns ::
    Timeless (rand_tapes_frag (L:=L) γ α ns);
  #[global] rand_tape_name_inhabited ::
    Inhabited rand_tape_name;

  rand_tapes_auth_exclusive {L : randG Σ} γ m m':
  rand_tapes_auth (L:=L) γ m -∗ rand_tapes_auth (L:=L) γ m' -∗ False;
  rand_tapes_frag_exclusive {L : randG Σ} γ α ns ns':
  rand_tapes_frag (L:=L) γ α ns -∗ rand_tapes_frag (L:=L) γ α ns' -∗ False;
  rand_tapes_agree {L : randG Σ} γ α m ns:
  rand_tapes_auth (L:=L) γ m -∗ rand_tapes_frag (L:=L) γ α ns -∗ ⌜ m!! α = Some (ns) ⌝;
  rand_tapes_valid {L : randG Σ} γ2 α tb ns:
    rand_tapes_frag (L:=L) γ2 α (tb, ns) -∗ ⌜Forall (λ n, n<=tb)%nat ns⌝ ;
  rand_tapes_update {L : randG Σ} γ α m ns ns':
  Forall (λ x, x<=ns'.1) ns'.2 ->
    rand_tapes_auth (L:=L) γ m -∗ rand_tapes_frag (L:=L) γ α ns ==∗
    rand_tapes_auth (L:=L) γ (<[α := ns']> m) ∗ rand_tapes_frag (L:=L) γ α ns';

  (** * Program specs *)
  rand_inv_create_spec {L : randG Σ} N E:
  ⊢ wp_update E (∃ γ1, is_rand (L:=L) N γ1);
  rand_allocate_tape_spec {L: randG Σ} N E (tb:nat) γ2:
    ↑N ⊆ E->
    {{{ is_rand (L:=L) N γ2 }}}
      rand_allocate_tape #tb @ E
      {{{ (v:val), RET v;
          ∃ (α:loc), ⌜v=#lbl:α⌝ ∗ rand_tapes_frag (L:=L) γ2 α (tb, [])
      }}}; 
  rand_tape_spec_some {L: randG Σ} N E γ2 (α:loc) (tb:nat) n ns:
    ↑N⊆E ->
    {{{ is_rand (L:=L) N γ2 ∗
        rand_tapes_frag (L:=L) γ2 α (tb, n::ns) 
    }}}
      rand_tape #lbl:α #tb @ E
                       {{{ RET #n; rand_tapes_frag (L:=L) γ2 α (tb, ns) }}}; 
  rand_presample_spec {L: randG Σ} N E γ2 α (tb:nat) ns T:
    ↑N ⊆ E ->
    is_rand (L:=L) N γ2 -∗
    rand_tapes_frag (L:=L) γ2 α (tb, ns) -∗
    (|={E∖↑N, ∅}=>
        ∃ ε num (ε2 : list (fin (S tb)) -> R),
            ↯ ε ∗
            ⌜(∀ l, length l = num ->  0<= ε2 l)%R⌝ ∗
            ⌜(SeriesC (λ l, if bool_decide (l ∈ enum_uniform_fin_list tb num) then ε2 l else 0) /((S tb)^num) <= ε)%R⌝ ∗
        (∀ (ns':list (fin (S tb))), ↯ (ε2 ns') ={∅, E∖↑N}=∗ T ε num ε2 ns')) -∗
    wp_update E (∃ ε num ε2 ns', rand_tapes_frag (L:=L) γ2 α (tb, ns ++ (fin_to_nat <$> ns')) ∗
                                 T ε num ε2 ns')
}.

Section impl.
  Local Opaque INR.
  (* (** Instantiate rand *) *)
  Class randG1 Σ := RandG1 { 
                             flipG1_tapes:: hocap_tapesGS Σ;
                      }.
  Local Definition rand_inv_pred1 `{!conerisGS Σ, !hocap_tapesGS Σ} γ2:=
    (∃ (m:gmap loc (nat * list nat)) ,
        ([∗ map] α ↦ t ∈ m, α ↪N ( t.1 ; t.2 )) ∗
        ●m@γ2
    )%I.

  #[local] Program Definition rand_spec1 `{!conerisGS Σ}: rand_spec :=
    {| rand_allocate_tape:= (λ: "N", alloc "N");
      rand_tape:= (λ: "α" "N", rand("α") "N"); 
      randG := randG1;
      rand_tape_name := gname;
      is_rand _ N γ2 := inv N (rand_inv_pred1 γ2);
      rand_tapes_auth _ γ m := (●m@γ)%I;
      rand_tapes_frag _ γ α ns := (α ◯↪N (ns.1; ns.2) @ γ ∗ ⌜Forall (λ x, x<=ns.1) ns.2⌝)%I;
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
    iMod (inv_alloc _ _ (rand_inv_pred1 γ2) with "[-]").
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
    iIntros (??????????? Φ) "(#Hinv & [Hvs %]) HΦ".
    wp_pures.
    iInv "Hinv" as ">(%&H3&H4)" "Hclose".
    iDestruct (hocap_tapes_agree with "[$][$]") as "%".
    iDestruct (big_sepM_insert_acc with "[$]") as "[Htape H3]"; first done.
    simpl.
    wp_apply (wp_rand_tape with "[$]") as "[Htape %]".
    iMod (hocap_tapes_update with "[$][$]") as "[? Hfrag]".
    iMod ("Hclose" with "[- Hfrag HΦ]") as "_".
    { iExists (<[α:=_]> m).
      iFrame.
      iApply "H3". by iNext.
    }
    iApply "HΦ". iFrame.
    iPureIntro. by eapply Forall_inv_tail.
  Qed.
  Next Obligation.
    simpl.
    iIntros (???????????) "#Hinv [Hfrag %] Hvs".
    iApply wp_update_state_step_coupl.
    iIntros (σ1 ε_supply) "((Hheap&Htapes)&Hε)".
    iMod (inv_acc with "Hinv") as "[>(% & H3 & H4 ) Hclose]"; [done|].
    iMod "Hvs" as "(%err & %num & %ε2 & Herr & %Hpos & %Hineq & Hrest)".
    iDestruct (hocap_tapes_agree with "[$][$]") as "%".
    iDestruct (big_sepM_insert_acc with "[$]") as "[Htape H3]"; first done.
    iDestruct (tapeN_lookup with "[$][$]") as "(%&%&%Heq)".
    iDestruct (ec_supply_bound with "[$][$]") as "%".
    iMod (ec_supply_decrease with "[$][$]") as (ε'' ε_rem -> Heq') "Hε_supply".
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    (* unshelve epose (ε_rem := mknonnegreal (ε_supply-ε) _). *)
    (* { simpl in *. lra. } *)
    (* replace (ε_supply) with (ε_rem + ε)%NNR; last first. *)
    (* { rewrite /ε_rem. apply nnreal_ext. simpl. lra. } *)
    iApply (state_step_coupl_iterM_state_adv_comp_con_prob_lang num α); first done.
    unshelve iExists (λ x, mknonnegreal (if length x =? num then ε2 x else 1)%R _).
    { case_match; last (simpl;lra). apply Hpos. by rewrite -Nat.eqb_eq. }
    iSplit.
    { iPureIntro.
      simpl. rewrite Heq'. etrans; last exact.
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
    simpl. simpl in *.
    rewrite -Heq.
    iMod (tapeN_update_append' _ _ _ _ sample with "[$][$]") as "[Htapes Htape]".
    iMod "Hclose'" as "_".
    unshelve iMod (ec_supply_increase _ (mknonnegreal (ε2 sample) _) with "[$]") as "[Hsupply Herr]".
    { naive_solver. }
    { simpl; lra. }
    iMod (hocap_tapes_update with "[$][$]") as "[Hauth Hfrag]".
    iMod ("Hrest" $! sample  with "[$Herr]") as "HT".
    iFrame.
    iMod ("Hclose" with "[-Hsupply]") as "_".
    { iNext. iFrame. by iApply "H3". }
    iApply fupd_mask_intro_subseteq; first set_solver.
    iSplit.
    - iApply ec_supply_eq; last done.
      simpl. rewrite Nat.eqb_refl. lra.
    - iPureIntro.
      rewrite Forall_app; split; subst; first done.
      eapply Forall_impl; first apply fin.fin_forall_leq.
      simpl; intros; lia.
  Qed.
  
End impl.

Section checks.
  Context `{H: conerisGS Σ, r1:@rand_spec Σ H, L:randG Σ}.
  
  Lemma wp_rand_tape_1 NS (N:nat) E γ1 n ns α:
    ↑NS ⊆ E ->
    {{{ is_rand (L:=L) NS γ1 ∗ ▷ rand_tapes_frag (L:=L) γ1 α (N, n :: ns) }}}
      rand_tape #lbl:α #N@ E
                       {{{ RET #(LitInt n); rand_tapes_frag (L:=L) γ1 α (N, ns) ∗ ⌜n <= N⌝ }}}.
  Proof.
    iIntros (Hsubset Φ) "(#Hinv &>Hfrag) HΦ".
    iDestruct (rand_tapes_valid with "[$]") as "%H'". 
    wp_apply (rand_tape_spec_some with "[Hfrag]"); first exact.
    - by iFrame.
    - iIntros.
      iApply "HΦ".
      iFrame.
      iPureIntro.
      rewrite Forall_cons in H'. naive_solver.
  Qed.

  Local Opaque enum_uniform_fin_list.

  Lemma rand_presample_single_spec N E γ2 α (tb:nat) ns T:
    ↑N ⊆ E ->
    is_rand (L:=L) N γ2 -∗
    rand_tapes_frag (L:=L) γ2 α (tb, ns) -∗
    (|={E∖↑N, ∅}=>
        ∃ ε (ε2 : fin (S tb) -> R),
            ↯ ε ∗
            ⌜(∀ x, 0<= ε2 x)%R⌝ ∗
            ⌜(SeriesC ε2 /((S tb)) <= ε)%R⌝ ∗
        (∀ x, ↯ (ε2 x) ={∅, E∖↑N}=∗ T ε ε2 x)) -∗
    wp_update E (∃ ε ε2 x, rand_tapes_frag (L:=L) γ2 α (tb, ns ++ [fin_to_nat x]) ∗
                           T ε ε2 x).
  Proof.
    iIntros (Hsubset) "#Hinv Hfrag Hvs".
    iMod (rand_presample_spec _ _ _ _ _ _ (λ ε' num ε2' ns2,
                                             ∃ x, ⌜ns2 = [x]⌝ ∗ T ε' (λ x, ε2' ([x])) x
            ) with "[//][$][-]")%I as "H"; first done; last first.
    - iDestruct "H" as "(%&%&%&%&Hfrag &%&%&HT)".
      subst.
      by iFrame.
    - iMod "Hvs" as "(%&%ε2&$&%Hpos & %Hineq & Hrest)".
      iModIntro.
      iExists 1, (λ ls, match ls with |[x] => ε2 x | _ => 1 end)%R.
      repeat iSplit.
      + iPureIntro. by intros [|?[|]].
      + iPureIntro.  etrans; last eapply Hineq.
        rewrite !Rdiv_def pow_1.
        apply Rmult_le_compat_r.
        { rewrite -Rdiv_1_l.
          apply Rdiv_INR_ge_0. }
        etrans; last eapply (SeriesC_le_inj _ (λ l, match l with |[x] => Some x | _ => None end)).
        * apply Req_le_sym.
          apply SeriesC_ext.
          intros. case_match; subst.
          -- rewrite bool_decide_eq_false_2; first (simpl;lra).
             by rewrite elem_of_enum_uniform_fin_list.
          -- case_match; last first.
             { rewrite bool_decide_eq_false_2; first (simpl;lra).
               subst.
               by rewrite elem_of_enum_uniform_fin_list.
             }
             rewrite bool_decide_eq_true_2; last by apply elem_of_enum_uniform_fin_list.
             done.
        * done.
        * intros. repeat case_match; by simplify_eq.
        * apply ex_seriesC_finite.
      + iIntros ([|?[|]]) "?"; [by iDestruct (ec_contradict with "[$]") as "%"| |by iDestruct (ec_contradict with "[$]") as "%"].
        iFrame.
        iMod ("Hrest" with "[$]").
        by iFrame.
  Qed.  

              
  Lemma wp_presample_adv_comp_rand_tape (N : nat) NS E α ns (ε1 : R) (ε2 : fin (S N) -> R) γ1:
    ↑NS ⊆ E ->
    (∀ n, 0<=ε2 n)%R ->
    (SeriesC (λ n, (1 / (S N)) * ε2 n)%R <= ε1)%R →
    is_rand (L:=L) NS γ1 -∗
    ▷ rand_tapes_frag (L:=L) γ1 α (N, ns) -∗
    ↯ ε1 -∗
    wp_update E (∃ n, ↯ (ε2 n) ∗ rand_tapes_frag (L:=L) γ1 α (N, ns ++[fin_to_nat n]))%I.
  Proof.
    iIntros (Hsubset Hpos Hineq) "#Hinv >Htape Herr".
    iDestruct (ec_valid with "[$]") as "%Hpos'".
    destruct Hpos' as [Hpos' ?].
    iMod (rand_presample_single_spec _ _ _ _ _ _ (λ ε' ε2' n, ↯ (ε2 n)) with "[//][$][-]") as "(%&%&%&?&?)"; first done; last by iFrame.
    iFrame.
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose".
    iExists ε2.
    repeat iSplit.
    - done.
    - iPureIntro. etrans; last apply Hineq.
      rewrite SeriesC_scal_l.
      lra.
    - iIntros. iFrame.
  Qed.
End checks.
