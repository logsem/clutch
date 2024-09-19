From clutch.coneris Require Import coneris.
From clutch.coneris Require Import flip hocap.

Set Default Proof Using "Type*".

Class flip_spec `{!conerisGS Σ} := FlipSpec
{
  (** * Operations *)
  flip_allocate_tape : val;
  flip_tape : val;
  (** * Ghost state *)
  (** The assumptions about [Σ] *)
  flipG : gFunctors → Type;
  (** [name] is used to associate [locked] with [is_lock] *)
  flip_error_name : Type;
  flip_tape_name: Type;
  (** * Predicates *)
  is_flip {L : flipG Σ} (N:namespace) 
    (γ1: flip_error_name) (γ2: flip_tape_name): iProp Σ;
  flip_error_auth {L : flipG Σ} (γ: flip_error_name) (x:R): iProp Σ;
  flip_error_frag {L : flipG Σ} (γ: flip_error_name) (x:R): iProp Σ;
  flip_tapes_auth {L : flipG Σ} (γ: flip_tape_name) (m:gmap loc (list bool)): iProp Σ;
  flip_tapes_frag {L : flipG Σ} (γ: flip_tape_name) (α:loc) (ns:list bool): iProp Σ;
  (** * General properties of the predicates *)
  #[global] is_flip_persistent {L : flipG Σ} N γ1 γ2 ::
    Persistent (is_flip (L:=L) N γ1 γ2);
  #[global] flip_error_auth_timeless {L : flipG Σ} γ x ::
    Timeless (flip_error_auth (L:=L) γ x);
  #[global] flip_error_frag_timeless {L : flipG Σ} γ x ::
    Timeless (flip_error_frag (L:=L) γ x);
  #[global] flip_tapes_auth_timeless {L : flipG Σ} γ m ::
    Timeless (flip_tapes_auth (L:=L) γ m);
  #[global] flip_tapes_frag_timeless {L : flipG Σ} γ α ns ::
    Timeless (flip_tapes_frag (L:=L) γ α ns);
  #[global] flip_error_name_inhabited::
    Inhabited flip_error_name;
  #[global] flip_tape_name_inhabited::
    Inhabited flip_tape_name;

  flip_error_auth_exclusive {L : flipG Σ} γ x1 x2:
    flip_error_auth (L:=L) γ x1 -∗ flip_error_auth (L:=L) γ x2 -∗ False;
  flip_error_frag_exclusive {L : flipG Σ} γ x1 x2:
  flip_error_frag (L:=L) γ x1 -∗ flip_error_frag (L:=L) γ x2 -∗ False;
  flip_error_auth_pos {L : flipG Σ} γ x:
    flip_error_auth (L:=L) γ x -∗ ⌜(0<=x)%R⌝;
  flip_error_auth_frag {L : flipG Σ} γ x:
    flip_error_frag (L:=L) γ x -∗ ⌜(0<=x)%R⌝;
  flip_error_agree {L : flipG Σ} γ x1 x2:
    flip_error_auth (L:=L) γ x1 -∗ flip_error_frag (L:=L) γ x2 -∗ ⌜x1 = x2 ⌝;
  flip_error_update {L : flipG Σ} γ x1 x2 (x3:nonnegreal):
    flip_error_auth (L:=L) γ x1 -∗ flip_error_frag (L:=L) γ x2 ==∗
    flip_error_auth (L:=L) γ x3 ∗ flip_error_frag (L:=L) γ x3;

  flip_tapes_auth_exclusive {L : flipG Σ} γ m m':
  flip_tapes_auth (L:=L) γ m -∗ flip_tapes_auth (L:=L) γ m' -∗ False;
  flip_tapes_frag_exclusive {L : flipG Σ} γ α ns ns':
  flip_tapes_frag (L:=L) γ α ns -∗ flip_tapes_frag (L:=L) γ α ns' -∗ False;
  flip_tapes_agree {L : flipG Σ} γ α m ns:
    flip_tapes_auth (L:=L) γ m -∗ flip_tapes_frag (L:=L) γ α ns -∗ ⌜ m!! α = Some (ns) ⌝;
  flip_tapes_update {L : flipG Σ} γ α m ns n:
    flip_tapes_auth (L:=L) γ m -∗ flip_tapes_frag (L:=L) γ α ns ==∗
    flip_tapes_auth (L:=L) γ (<[α := (ns ++[n])]> m) ∗ flip_tapes_frag (L:=L) γ α (ns ++ [n]);

  (** * Program specs *)
  flip_inv_create_spec {L : flipG Σ} N E ε:
  ↯ ε -∗
  wp_update E (∃ γ1 γ2, is_flip (L:=L) N γ1 γ2 ∗
                        flip_error_frag (L:=L) γ1 ε);
  
  flip_allocate_tape_spec {L: flipG Σ} N E γ1 γ2:
    ↑N ⊆ E->
    {{{ is_flip (L:=L) N γ1 γ2 }}}
      flip_allocate_tape #() @ E
      {{{ (v:val), RET v;
          ∃ (α:loc), ⌜v=#lbl:α⌝ ∗ flip_tapes_frag (L:=L) γ2 α []
      }}};
  flip_tape_spec_some {L: flipG Σ} N E γ1 γ2 (P: iProp Σ) (Q:iProp Σ) (α:loc) (n:bool) ns:
    ↑N⊆E -> 
    {{{ is_flip (L:=L) N γ1 γ2 ∗
        □ (∀ m, P ∗
           flip_tapes_auth (L:=L) γ2 m 
            ={E∖↑N}=∗ ⌜m!!α=Some (n::ns)⌝ ∗ Q ∗ flip_tapes_auth (L:=L) γ2 (<[α:=ns]> m)) ∗
        P 
    }}}
      flip_tape #lbl:α @ E
                       {{{ RET #n; Q }}};
  flip_presample_spec {L: flipG Σ} NS E ns α
     (ε2 : R -> bool -> R)
    (P : iProp Σ) T γ1 γ2:
    ↑NS ⊆ E ->
    (∀ ε n, 0<= ε -> 0<=ε2 ε n)%R ->
    (∀ (ε:R), 0<= ε -> (ε2 ε true + ε2 ε false)/2 <= ε)%R->
    is_flip (L:=L) NS γ1 γ2 -∗
    (□∀ (ε:R) n, (P ∗ flip_error_auth (L:=L) γ1 ε) ={E∖↑NS}=∗
        (⌜(1<=ε2 ε n)%R⌝ ∨ (flip_error_auth (L:=L) γ1 (ε2 ε n)  ∗ T (n)))) 
        -∗
    P -∗ flip_tapes_frag (L:=L) γ2 α ns-∗
        wp_update E (∃ n, T (n) ∗ flip_tapes_frag (L:=L) γ2 α (ns++[n]))
}.


(** Instantiate flip *)
Class flipG1 Σ := FlipG1 { flipG1_error::hocap_errorGS Σ;
                                    flipG1_tapes:: hocap_tapesGS Σ;
                    }.
Local Definition flip_inv_pred1 `{!conerisGS Σ, !hocap_errorGS Σ, !hocap_tapesGS Σ} γ1 γ2:=
    (∃ (ε:R) (m:gmap loc (list bool)) ,
        ↯ ε ∗ ●↯ ε @ γ1  ∗
        ([∗ map] α ↦ t ∈ ((λ (ns:list bool), (1%nat, bool_to_nat<$>ns))<$>m), α ↪N ( t.1 ; t.2 )) ∗
        ●(((λ (ns:list bool), (1, bool_to_nat<$>ns))<$>m):gmap _ _)@γ2
    )%I.

#[local] Program Definition flip_spec1 `{!conerisGS Σ}: flip_spec :=
  {| flip_allocate_tape:= (λ: <>, allocB);
     flip_tape:= flipL;
     flipG := flipG1;
    flip_error_name := gname;
    flip_tape_name := gname;
    is_flip _ N γ1 γ2 := inv N (flip_inv_pred1 γ1 γ2);
    flip_error_auth _ γ x := ●↯ x @ γ;
    flip_error_frag _ γ x := ◯↯ x @ γ;
    flip_tapes_auth _ γ m := (●((λ ns, (1, bool_to_nat<$>ns))<$>m)@γ)%I;
    flip_tapes_frag _ γ α ns := (α◯↪N (1%nat;bool_to_nat<$> ns) @ γ)%I;
  |}.

Next Obligation.
  simpl.
  iIntros (??????) "(%&<-&H1)(%&<-&H2)".
  iCombine "H1 H2" gives "%H". by rewrite excl_auth.excl_auth_auth_op_valid in H.
Qed.
Next Obligation.
  simpl.
  iIntros (??????) "(%&<-&H1)(%&<-&H2)".
  iCombine "H1 H2" gives "%H". by rewrite excl_auth.excl_auth_frag_op_valid in H.
Qed.
Next Obligation.
  simpl.
  iIntros (?????) "H".
  iApply (hocap_error_auth_pos with "[$]").
Qed.
Next Obligation.
  simpl.
  iIntros (?????) "H".
  iApply (hocap_error_frag_pos with "[$]").
Qed.
Next Obligation.
  simpl.
  iIntros (??????) "H1 H2".
  iApply (hocap_error_agree with "[$][$]").
Qed.
Next Obligation.
  simpl. iIntros (???????) "??".
  iApply (hocap_error_update with "[$][$]").
Qed.
Next Obligation.
  simpl.
  iIntros (??????) "H1 H2".
  by iDestruct (ghost_map_auth_valid_2 with "[$][$]") as "[%H _]".
Qed.
Next Obligation.
  simpl. 
  iIntros (???????) "H1 H2".
  iDestruct (ghost_map_elem_frac_ne with "[$][$]") as "%"; last done.
  rewrite dfrac_op_own dfrac_valid_own. by intro.
Qed.
Next Obligation.
  simpl.
  iIntros.
  iDestruct (hocap_tapes_agree with "[$][$]") as "%H".
  iPureIntro.
  rewrite lookup_fmap_Some in H. destruct H as (?&?&K).
  simplify_eq.
  rewrite K.
  f_equal.
  eapply fmap_inj; last done.
  intros [][]?; by simplify_eq.
Qed.
Next Obligation.
  iIntros.
  iMod (hocap_tapes_presample with "[$][$]") as "[??]".
  iModIntro. iFrame.
  rewrite fmap_insert.
  rewrite fmap_app; iFrame.
Qed.
Next Obligation.
  simpl.
  iIntros (????? ε) "H1".
  iApply fupd_wp_update.
  iApply wp_update_ret.
  iDestruct (ec_valid with "[$]") as "%".
  unshelve iMod (hocap_error_alloc (mknonnegreal ε _)) as "(%γ1 & H2 & H3)"; first naive_solver.
  simpl.
  iMod (hocap_tapes_alloc ∅) as "(%γ2 & H4 & H5)".
  iMod (inv_alloc _ _ (flip_inv_pred1 γ1 γ2) with "[H1 H2 H4]").
  { iFrame. iNext. iExists ∅.
    iFrame.
    by rewrite fmap_empty.
  }
  by iFrame.
Qed.
Next Obligation.
  simpl.
  iIntros (???????? Φ) "#Hinv HΦ".
  wp_pures.
  rewrite /allocB.
  iInv "Hinv" as "(%&%&?&?&?&?)" "Hclose".
  wp_apply (wp_alloc_tape); first done.
  iIntros (α) "Hα".
  iDestruct (hocap_tapes_notin with "[$][$]") as "%".
  iMod (hocap_tapes_new _ _ α 1%nat [] with "[$]") as "[?H]"; first done.
  iMod ("Hclose" with "[-H HΦ]").
  { iModIntro.
    iExists _, (<[α:=([])]> m).
    iFrame.
    rewrite fmap_insert.
    rewrite big_sepM_insert; [iFrame|done].
  }
  iApply "HΦ".
  by iFrame.
Qed.
Next Obligation.
  simpl.
  iIntros (????????????? Φ) "(#Hinv & #Hvs & HP) HΦ".
  rewrite /flipL.
  wp_pures.
  wp_bind (rand(_) _)%E.
  iInv "Hinv" as ">(%&%&?&?&H3&?)" "Hclose".
  iMod ("Hvs" with "[$]") as "(%&HQ&Hauth)".
  erewrite <-(insert_delete m) at 1; last done.
  rewrite fmap_insert.
  rewrite big_sepM_insert; last first.
  { rewrite fmap_delete. apply lookup_delete. }
  iDestruct "H3" as "[Htape H3]".
  simpl.
  wp_apply (wp_rand_tape with "[$]") as "[Htape %]".
  iMod ("Hclose" with "[- HΦ HQ]") as "_".
  { iExists _, (<[α:=ns]> m).
    iFrame.
    rewrite <-(insert_delete m) at 2; last done.
    rewrite insert_insert fmap_insert.
    rewrite big_sepM_insert; first iFrame.
    rewrite fmap_delete.
    apply lookup_delete.
  }
  iModIntro.
  wp_apply conversion.wp_int_to_bool as "_"; first done.
  replace (Z_to_bool _) with n.
  - iApply "HΦ"; iFrame.
  - destruct n; simpl.
    + rewrite Z_to_bool_neq_0; [done|lia].
    + by rewrite Z_to_bool_eq_0.
Qed.
Next Obligation.
  simpl.
  iIntros (???????????? Hsubset Hpos Hineq) "#Hinv #Hvs HP Hfrag".
  iApply wp_update_state_step_coupl.
  iIntros (σ ε) "((Hheap&Htapes)&Hε)".
  iMod (inv_acc with "Hinv") as "[>(% & % & H1 & H2 & H3 & H4 ) Hclose]"; [done|].
  iDestruct (hocap_tapes_agree with "[$][$]") as "%K".
  rewrite lookup_fmap_Some in K. destruct K as (?&M&?).
  simplify_eq.
  unshelve epose proof fmap_inj _ _ _ _ M as ->.
  { intros [][]?; by simplify_eq. }
  erewrite <-(insert_delete m) at 1; last done.
  rewrite fmap_insert.
  rewrite big_sepM_insert; last first.
  { rewrite fmap_delete. apply lookup_delete. }
  simpl.
  iDestruct "H3" as "[Htape H3]".
  iDestruct (tapeN_lookup with "[$][$]") as "(%&%&%Heq)".
  iDestruct (ec_supply_bound with "[$][$]") as "%".
  iMod (ec_supply_decrease with "[$][$]") as (ε1' ε_rem -> Hε1') "Hε_supply". subst.
  iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
  iApply state_step_coupl_state_adv_comp_con_prob_lang; first done.
  unshelve iExists (λ x, mknonnegreal (ε2 ε1' (nat_to_bool (fin_to_nat x))) _).
  { apply Hpos. apply cond_nonneg. }
  iSplit.
  { iPureIntro.
    simpl.
    unshelve epose proof (Hineq ε1' _) as H'; first apply cond_nonneg.
    rewrite SeriesC_finite_foldr/=.
    rewrite nat_to_bool_eq_0 nat_to_bool_neq_0; last lia.
    simpl in *. lra.
  }
  iIntros (sample).
  destruct (Rlt_decision (nonneg ε_rem + (ε2 ε1' (nat_to_bool (fin_to_nat sample))))%R 1%R) as [Hdec|Hdec]; last first.
  { apply Rnot_lt_ge, Rge_le in Hdec.
    iApply state_step_coupl_ret_err_ge_1.
    simpl. simpl in *. lra.
  }
  iApply state_step_coupl_ret.
  unshelve iMod (ec_supply_increase _ (mknonnegreal (ε2 ε1' (nat_to_bool (fin_to_nat sample))) _) with "Hε_supply") as "[Hε_supply Hε]".
  { apply Hpos. apply cond_nonneg. }
  { simpl. done. }
  simpl.
  iMod (tapeN_update_append _ _ _ _ sample with "[$][Htape]") as "[Htapes Htape]".
  { by erewrite Heq. }
  iMod (hocap_tapes_presample _ _ _ _ _ (fin_to_nat sample) with "[$][$]") as "[H4 Hfrag]".
  iMod "Hclose'" as "_".
  iMod ("Hvs" with "[$]") as "[%|[H2 HT]]".
  { iExFalso. iApply (ec_contradict with "[$]"). exact. }
  iMod ("Hclose" with "[$Hε $H2 Htape H3 H4]") as "_".
  { iNext.
    iExists (<[α:=(ns ++ [nat_to_bool sample])]>m).
    rewrite fmap_insert.
    rewrite big_sepM_insert_delete Heq/=.
    rewrite fmap_delete. iFrame.
    rewrite fmap_app/= nat_to_bool_to_nat; first iFrame.
    pose proof fin_to_nat_lt sample. lia.
  }
  iApply fupd_mask_intro_subseteq; first set_solver.
  iFrame.
  rewrite fmap_app/= nat_to_bool_to_nat; first done.
  pose proof fin_to_nat_lt sample. lia.
Qed.
