From iris.algebra Require Import frac_auth.
From iris.base_logic.lib Require Import invariants.
From clutch.coneris Require Import coneris hocap.

Set Default Proof Using "Type*".

(* Class lock `{!conerisGS Σ} := Lock *)
(* { *)
(*   (** * Operations *) *)
(*   new_counter : val; *)
(*   incr_counter : val; *)
(*   allocate_tape : val; *)
(*   incr_counter_tape : val; *)
(*   (** * Ghost state *) *)
(*   (** The assumptions about [Σ] *) *)
(*   counterG : gFunctors → Type; *)
(*   (** [name] is used to associate [locked] with [is_lock] *) *)
(*   error_name : Type; *)
(*   tape_name: Type; *)
(*   counter_name: Type; *)
(*   (** * Predicates *) *)
(*   is_counter {L : counterG Σ} (N:namespace) (counter: val) *)
(*     (γ1: error_name) (γ2: tape_name) (γ3: counter_name): iProp Σ; *)
(*   counter_error_auth {L : counterG Σ} (γ: error_name) (x:R): iProp Σ; *)
(*   counter_error_frag {L : counterG Σ} (γ: error_name) (x:R): iProp Σ; *)
(*   counter_tapes_auth {L : counterG Σ} (γ: tape_name) (m:gmap loc (nat*list nat)): iProp Σ; *)
(*   counter_tapes_frag {L : counterG Σ} (γ: tape_name) (α:loc) (N:nat) (ns:list nat): iProp Σ; *)
(*   counter_content_auth {L : counterG Σ} (γ: counter_name) (z:Z): iProp Σ; *)
(*   counter_content_frag {L : counterG Σ} (γ: counter_name) (f:frac) (z:Z): iProp Σ; *)
(*   (** * General properties of the predicates *) *)
(*   #[global] is_counter_persistent {L : counterG Σ} N c γ1 γ2 γ3 :: *)
(*     Persistent (is_counter (L:=L) N c γ1 γ2 γ3); *)
(*   #[global] counter_error_auth_timeless {L : counterG Σ} γ x :: *)
(*     Timeless (counter_error_auth (L:=L) γ x); *)
(*   #[global] counter_error_frag_timeless {L : counterG Σ} γ x :: *)
(*     Timeless (counter_error_frag (L:=L) γ x); *)
(*   #[global] counter_tapes_auth_timeless {L : counterG Σ} γ m :: *)
(*     Timeless (counter_tapes_auth (L:=L) γ m); *)
(*   #[global] counter_tapes_frag_timeless {L : counterG Σ} γ α N ns :: *)
(*     Timeless (counter_tapes_frag (L:=L) γ α N ns); *)
(*   #[global] counter_content_auth_timeless {L : counterG Σ} γ z :: *)
(*     Timeless (counter_content_auth (L:=L) γ z); *)
(*   #[global] counter_content_frag_timeless {L : counterG Σ} γ f z :: *)
(*     Timeless (counter_content_frag (L:=L) γ f z); *)

(*   counter_error_auth_exclusive {L : counterG Σ} γ x1 x2: *)
(*     counter_error_auth (L:=L) γ x1 -∗ counter_error_auth (L:=L) γ x2 -∗ False;  *)
(*   counter_error_frag_exclusive {L : counterG Σ} γ x1 x2: *)
(*   counter_error_frag (L:=L) γ x1 -∗ counter_error_frag (L:=L) γ x2 -∗ False; *)
(*   counter_error_agree {L : counterG Σ} γ x1 x2: *)
(*     counter_error_auth (L:=L) γ x1 -∗ counter_error_frag (L:=L) γ x2 -∗ ⌜x1 = x2 ⌝;  *)
(*   counter_error_update {L : counterG Σ} γ x1 x2 x3: *)
(*     counter_error_auth (L:=L) γ x1 -∗ counter_error_frag (L:=L) γ x2 ==∗ *)
(*     counter_error_auth (L:=L) γ x3 ∗ counter_error_frag (L:=L) γ x3; *)

(*   counter_tapes_auth_exclusive {L : counterG Σ} γ m1 m2: *)
(*     counter_tapes_auth (L:=L) γ m1 -∗ counter_tapes_auth (L:=L) γ m2 -∗ False;  *)
(*   counter_tapes_frag_exclusive {L : counterG Σ} γ α N N' ns ns': *)
(*   counter_tapes_frag (L:=L) γ α N ns -∗ counter_tapes_frag (L:=L) γ α N' ns' -∗ False; *)
(*   counter_tapes_agree {L : counterG Σ} γ α m N ns: *)
(*     counter_tapes_auth (L:=L) γ m -∗ counter_tapes_frag (L:=L) γ α N ns -∗ ⌜ m!! α = Some (N, ns) ⌝;  *)
(*   counter_tapes_update {L : counterG Σ} γ α m N ns n: *)
(*     counter_tapes_auth (L:=L) γ m -∗ counter_tapes_frag (L:=L) γ α N ns ==∗ *)
(*     counter_tapes_auth (L:=L) γ (<[α := (N, ns ++[n])]> m) ∗ counter_tapes_frag (L:=L) γ α N (ns ++ [n]); *)

(*   counter_content_auth_exclusive {L : counterG Σ} γ z1 z2: *)
(*     counter_content_auth (L:=L) γ z1 -∗ counter_content_auth (L:=L) γ z2 -∗ False;  *)
(*   counter_content_less_than {L : counterG Σ} γ z z' f: *)
(*     counter_content_auth (L:=L) γ z -∗ counter_content_frag (L:=L) γ f z' -∗ ⌜(z'<=z)%Z ⌝;  *)
(*   counter_content_agree {L : counterG Σ} γ z z': *)
(*     counter_content_auth (L:=L) γ z -∗ counter_content_frag (L:=L) γ 1%Qp z' -∗ ⌜(z'<=z)%Z ⌝; *)
(*   counter_content_update {L : counterG Σ} γ f z1 z2 z3: *)
(*     counter_content_auth (L:=L) γ z1 -∗ counter_content_frag (L:=L) γ f z2 ==∗ *)
(*     counter_content_auth (L:=L) γ (z1+z3)%Z ∗ counter_content_frag (L:=L) γ f (z2+z3)%Z; *)
  
(*   (** * Program specs *) *)
(*   new_counter_spec {L : counterG Σ} N ε: *)
(*   {{{ ↯ ε }}} new_counter #() *)
(*     {{{ c, RET c; ∃ γ1 γ2 γ3, is_counter (L:=L) N c γ1 γ2 γ3 ∗ *)
(*                               counter_error_frag (L:=L) γ1 ε ∗ *)
(*                               counter_content_frag (L:=L) γ3 1%Qp 0%Z *)
(*     }}}; *)
(*   (* acquire_spec `{!conerisGS Σ} {L : lockG Σ} γ lk R : *) *)
(*   (*   {{{ is_lock (L:=L) γ lk R }}} acquire lk {{{ RET #(); locked (L:=L) γ ∗ R }}}; *) *)
(*   (* release_spec `{!conerisGS Σ} {L : lockG Σ} γ lk R : *) *)
(*   (*   {{{ is_lock (L:=L) γ lk R ∗ locked (L:=L) γ ∗ R }}} release lk {{{ RET #(); True }}} *) *)
(* }. *)


Section impl1.

  Definition new_counter : val:= λ: "_", ref #0.
  Definition incr_counter : val := λ: "l", let: "n" := rand #3 in (FAA "l" "n", "n").
  Definition allocate_tape : val := λ: "_", AllocTape #3.
  Definition incr_counter_tape :val := λ: "l" "α", let: "n" := rand("α") #3 in (FAA "l" "n", "n").
  Definition read_counter : val := λ: "l", !"l".

  Context `{!conerisGS Σ, !hocap_errorGS Σ, !hocap_tapesGS Σ, !inG Σ (frac_authR ZR)}.
  Definition counter_inv_pred (c:val) γ1 γ2 γ3:=
    (∃ (ε:R) m (l:loc) (z:Z),
        ↯ ε ∗ ●↯ ε @ γ1 ∗
        ([∗ map] α ↦ t ∈ m, α ↪N ( t.1 ; t.2 )) ∗ ●m@γ2 ∗  
        ⌜c=#l⌝ ∗ l ↦ #z ∗ own γ3 (●F z)
    )%I.

  Lemma new_counter_spec E ε N:
    {{{ ↯ ε }}}
      new_counter #() @ E
      {{{ (c:val), RET c;
          ∃ γ1 γ2 γ3, inv N (counter_inv_pred c γ1 γ2 γ3) ∗
                      ◯↯ε @ γ1 ∗ own γ3 (◯F 0%Z)
      }}}.
  Proof.
    rewrite /new_counter.
    iIntros (Φ) "Hε HΦ".
    wp_pures.
    wp_alloc l as "Hl".
    iDestruct (ec_valid with "[$]") as "%".
    unshelve iMod (hocap_error_alloc (mknonnegreal ε _)) as "[%γ1 [H1 H2]]".
    { lra. }
    simpl.
    iMod (hocap_tapes_alloc (∅:gmap _ _)) as "[%γ2 [H3 H4]]".
    iMod (own_alloc (●F 0%Z ⋅ ◯F 0%Z)) as "[%γ3[H5 H6]]".
    { by apply frac_auth_valid. }
    iMod (inv_alloc N _ (counter_inv_pred (#l) γ1 γ2 γ3) with "[$Hε $Hl $H1 $H3 $H5]") as "#Hinv".
    { iSplit; last done. by iApply big_sepM_empty. }
    iApply "HΦ".
    iExists _, _, _. by iFrame.
  Qed. 

  Lemma incr_counter_spec E N c γ1 γ2 γ3 (ε2:R -> nat -> R) (P: iProp Σ) (T: nat -> iProp Σ) (Q: Z->nat->iProp Σ):
    ↑N ⊆ E->
    (∀ ε n, 0<= ε -> 0<= ε2 ε n)%R->
    (∀ (ε:R), 0<=ε -> ((ε2 ε 0%nat) + (ε2 ε 1%nat)+ (ε2 ε 2%nat)+ (ε2 ε 3%nat))/4 <= ε)%R →
    {{{ inv N (counter_inv_pred c γ1 γ2 γ3) ∗
        □(∀ (ε:R) (n : nat), P ∗ ●↯ ε @ γ1 ={E∖↑N}=∗ (⌜(1<=ε2 ε n)%R⌝∨●↯ (ε2 ε n) @ γ1 ∗ T n) ) ∗
        □ (∀ (n:nat) (z:Z), T n ∗ own γ3 (●F z) ={E∖↑N}=∗
                          own γ3 (●F(z+n)%Z)∗ Q z n) ∗
        P
    }}}
      incr_counter c @ E
      {{{ (n:nat) (z:Z), RET (#z, #n); Q z n }}}.
  Proof.
    iIntros (Hsubset Hpos Hineq Φ) "(#Hinv & #Hvs1 & #Hvs2 & HP) HΦ".
    rewrite /incr_counter.
    wp_pures.
    wp_bind (rand _)%E.
    iInv N as ">(%ε & %m & %l & %z & H1 & H2 & H3 & H4 & -> & H5 & H6)" "Hclose".
    iDestruct (ec_valid with "[$]") as "[%K1 %K2]".
    wp_apply (wp_couple_rand_adv_comp1' _ _ _ _ (λ x, ε2 ε (fin_to_nat x)) with "[$]").
    { intros. naive_solver. }
    { rewrite SeriesC_finite_foldr; specialize (Hineq ε K1). simpl; lra. }
    iIntros (n) "H1".
    iMod ("Hvs1" with "[$]") as "[%|[H2 HT]]".
    { iExFalso. iApply ec_contradict; last done. done. }
    iMod ("Hclose" with "[$H1 $H2 $H3 $H4 $H5 $H6]") as "_"; first done.
    iModIntro. wp_pures.
    clear -Hsubset.
    wp_bind (FAA _ _).
    iInv N as ">(%ε & %m & % & %z & H1 & H2 & H3 & H4 & -> & H5 & H6)" "Hclose".
    wp_faa.
    iMod ("Hvs2" with "[$]") as "[H6 HQ]".
    iMod ("Hclose" with "[$H1 $H2 $H3 $H4 $H5 $H6]") as "_"; first done.
    iModIntro.
    wp_pures.
    by iApply "HΦ".
  Qed.

  Lemma allocate_tape_spec N E c γ1 γ2 γ3:
    ↑N ⊆ E->
    {{{ inv N (counter_inv_pred c γ1 γ2 γ3) }}}
      allocate_tape #() @ E
      {{{ (v:val), RET v;
          ∃ (α:loc), ⌜v=#lbl:α⌝ ∗ α ◯↪N (3%nat; []) @ γ2
      }}}.
  Proof.
    iIntros (Hsubset Φ) "#Hinv HΦ".
    rewrite /allocate_tape.
    wp_pures.
    wp_alloctape α as "Hα".
    iInv N as ">(%ε & %m & %l & %z & H1 & H2 & H3 & H4 & -> & H5 & H6)" "Hclose".
    iDestruct (hocap_tapes_notin with "[$][$]") as "%".
    iMod (hocap_tapes_new with "[$]") as "[H4 H7]"; first done.
    iMod ("Hclose" with "[$H1 $H2 H3 $H4 $H5 $H6 Hα]") as "_".
    { iNext. iSplitL; last done.
      rewrite big_sepM_insert; [simpl; iFrame|done].
    }
    iApply "HΦ".
    by iFrame.
  Qed.

  Lemma incr_counter_tape_spec_some N E c γ1 γ2 γ3 (ε2:R -> nat -> R) (P: iProp Σ) (Q:Z->iProp Σ) (α:loc) (n:nat) ns:
    ↑N⊆E -> 
    {{{ inv N (counter_inv_pred c γ1 γ2 γ3) ∗
        □ (∀ (z:Z), P ∗ own γ3 (●F z) ={E∖↑N}=∗
                          own γ3 (●F(z+n)%Z)∗ Q z) ∗
        P ∗ α ◯↪N (3%nat; n::ns) @ γ2
    }}}
      incr_counter_tape c #lbl:α @ E
      {{{ (z:Z), RET (#z, #n); Q z ∗ α ◯↪N (3%nat; ns) @ γ2}}}.
  Proof.
    iIntros (Hsubset Φ) "(#Hinv & #Hvs & HP & Hα) HΦ".
    rewrite /incr_counter_tape.
    wp_pures.
    wp_bind (rand(_) _)%E.
    iInv N as ">(%ε & %m & %l & %z & H1 & H2 & H3 & H4 & -> & H5 & H6)" "Hclose".
    iDestruct (hocap_tapes_agree with "[$][$]") as "%".
    erewrite <-(insert_delete m) at 1; last done.
    rewrite big_sepM_insert; last apply lookup_delete.
    simpl.
    iDestruct "H3" as "[Htape H3]".
    wp_apply (wp_rand_tape with "[$]").
    iIntros "[Htape %]".
    iMod (hocap_tapes_pop with "[$][$]") as "[H4 Hα]".
    iMod ("Hclose" with "[$H1 $H2 H3 $H4 $H5 $H6 Htape]") as "_".
    { iSplitL; last done.
      erewrite <-(insert_delete m) at 2; last done.
      iNext.
      rewrite insert_insert.
      rewrite big_sepM_insert; last apply lookup_delete. iFrame.
    }
    iModIntro.
    wp_pures.
    clear -Hsubset.
    wp_bind (FAA _ _).
    iInv N as ">(%ε & %m & % & %z & H1 & H2 & H3 & H4 & -> & H5 & H6)" "Hclose".
    wp_faa.
    iMod ("Hvs" with "[$]") as "[H6 HQ]".
    iMod ("Hclose" with "[$H1 $H2 $H3 $H4 $H5 $H6]") as "_"; first done.
    iModIntro. wp_pures.
    iApply "HΦ".
    by iFrame.
  Qed. 
    
  Lemma incr_counter_tape_spec_none N E c γ1 γ2 γ3 (ε2:R -> nat -> R) (P: iProp Σ) (T: nat -> iProp Σ) (Q: Z -> nat -> iProp Σ)(α:loc) (ns:list nat):
    ↑N ⊆ E->
    (∀ ε n, 0<= ε -> 0<= ε2 ε n)%R->
    (∀ (ε:R), 0<=ε -> ((ε2 ε 0%nat) + (ε2 ε 1%nat)+ (ε2 ε 2%nat)+ (ε2 ε 3%nat))/4 <= ε)%R →
    {{{ inv N (counter_inv_pred c γ1 γ2 γ3) ∗
        □(∀ (ε:R) (n : nat), P ∗ ●↯ ε @ γ1 ={E∖↑N}=∗ (⌜(1<=ε2 ε n)%R⌝∨●↯ (ε2 ε n) @ γ1 ∗ T n) ) ∗
        □ (∀ (n:nat) (z:Z), T n ∗ own γ3 (●F z) ={E∖↑N}=∗
                          own γ3 (●F(z+n)%Z)∗ Q z n) ∗
        P ∗ α ◯↪N (3%nat; []) @ γ2
    }}}
      incr_counter_tape c #lbl:α @ E
      {{{ (z:Z) (n:nat), RET (#z, #n); Q z n ∗ α ◯↪N (3%nat; []) @ γ2 }}}.
  Proof.
    iIntros (Hsubset Hpos Hineq Φ) "(#Hinv & #Hvs1 & #Hvs2 & HP & Hα) HΦ".
    rewrite /incr_counter_tape.
    wp_pures.
    wp_bind (rand(_) _)%E.
    iInv N as ">(%ε & %m & %l & %z & H1 & H2 & H3 & H4 & -> & H5 & H6)" "Hclose".
    iDestruct (hocap_tapes_agree with "[$][$]") as "%".
    rewrite big_sepM_lookup_acc; last done.
    iDestruct (ec_valid with "[$]") as "[%K1 %K2]".
    iDestruct ("H3") as "[H3 H3']". simpl.
    wp_apply (wp_couple_empty_tape_adv_comp _ _ _ _ (λ x, ε2 ε x) with "[$]").
    { intros. naive_solver. }
    { rewrite SeriesC_nat_bounded. simpl. specialize (Hineq ε K1).
      rewrite /Hierarchy.sum_n Hierarchy.sum_n_m_Reals; last lia.
      rewrite /sum_f/sum_f_R0/=. lra. }
    iIntros (n) "[Htape H1]".
    iMod ("Hvs1" with "[$]") as "[%|[H2 HT]]".
    { iExFalso. iApply ec_contradict; last done. done. }
    iDestruct ("H3'" with "[$]") as "H3".
    iMod ("Hclose" with "[$H1 $H2 $H3 $H4 $H5 $H6]") as "_"; first done.
    iModIntro. wp_pures.
    clear -Hsubset.
    wp_bind (FAA _ _).
    iInv N as ">(%ε & %m & % & %z & H1 & H2 & H3 & H4 & -> & H5 & H6)" "Hclose".
    wp_faa.
    iMod ("Hvs2" with "[$]") as "[H6 HQ]".
    iMod ("Hclose" with "[$H1 $H2 $H3 $H4 $H5 $H6]") as "_"; first done.
    iModIntro.
    wp_pures.
    iApply "HΦ". by iFrame.
  Qed.

  
  Lemma counter_presample NS (N : nat)  z E ns α
     (ε2 : R -> nat -> R)
    (P : iProp Σ) (Q : val-> iProp Σ) T γ1 γ2 γ3 c:
    TCEq N (Z.to_nat z) →
    ↑NS ⊆ E ->
    (∀ ε n, 0<= ε -> 0<=ε2 ε n)%R ->
    (∀ (ε:R), 0<= ε ->SeriesC (λ n, if (bool_decide (n≤N)) then 1 / (S N) * ε2 ε n else 0%R)%R <= ε)%R->
    inv NS (counter_inv_pred c γ1 γ2 γ3) -∗
    (□∀ (ε:R) n, (P ∗ ●↯ ε @ γ1) ={E∖↑NS}=∗
        (⌜(1<=ε2 ε n)%R⌝ ∨(●↯ (ε2 ε n) @ γ1 ∗ T (n)))) 
        -∗
    P -∗ α ◯↪N (N; ns) @ γ2 -∗
        wp_update E (∃ n, T (n) ∗ α◯↪N (N; ns++[n]) @ γ2).
  Proof.
    iIntros (-> Hsubset Hpos Hineq) "#Hinv #Hvs HP Hfrag".
    rewrite wp_update_unfold.
    iIntros (?? Hv) "Hcnt".
    rewrite {2}pgl_wp_unfold /pgl_wp_pre /= Hv.
    iIntros (σ ε) "((Hheap&Htapes)&Hε)".
    iMod (inv_acc with "Hinv") as "[>(% & % & % & % & H1 & H2 & H3 & H4 & -> & H5 & H6) Hclose]"; [done|].
    iDestruct (hocap_tapes_agree with "[$][$]") as "%".
    erewrite <-(insert_delete m) at 1; last done.
    rewrite big_sepM_insert; last apply lookup_delete.
    simpl.
    iDestruct "H3" as "[Htape H3]".
    iDestruct (tapeN_lookup with "[$][$]") as "(%&%&%)".
    iDestruct (ec_supply_bound with "[$][$]") as "%".
    iMod (ec_supply_decrease with "[$][$]") as (ε1' ε_rem -> Hε1') "Hε_supply". subst.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iApply glm_state_adv_comp_con_prob_lang; first done.
    unshelve iExists (λ x, mknonnegreal (ε2 ε1' x) _).
    { apply Hpos. apply cond_nonneg. }
    iSplit.
    { iPureIntro. 
      unshelve epose proof (Hineq ε1' _) as H1; first apply cond_nonneg.
      by rewrite SeriesC_nat_bounded_fin in H1. }
    iIntros (sample).
    
    destruct (Rlt_decision (nonneg ε_rem + (ε2 ε1' sample))%R 1%R) as [Hdec|Hdec]; last first.
    { apply Rnot_lt_ge, Rge_le in Hdec.
      iLeft.
      iPureIntro.
      simpl. simpl in *. lra.
    }
    iRight.
    unshelve iMod (ec_supply_increase _ (mknonnegreal (ε2 ε1' sample) _) with "Hε_supply") as "[Hε_supply Hε]".
    { apply Hpos. apply cond_nonneg. }
    { simpl. done. }
    iMod (tapeN_update_append _ _ _ _ sample with "[$][$]") as "[Htapes Htape]".
    iMod (hocap_tapes_presample _ _ _ _ _ (fin_to_nat sample) with "[$][$]") as "[H4 Hfrag]".
    iMod "Hclose'" as "_".
    iMod ("Hvs" with "[$]") as "[%|[H2 HT]]".
    { iExFalso. iApply (ec_contradict with "[$]"). exact. }
    iMod ("Hclose" with "[$Hε $H2 Htape H3 $H4 $H5 $H6]") as "_".
    { iNext. iSplit; last done.
      rewrite big_sepM_insert_delete; iFrame.
    }
    iSpecialize ("Hcnt" with "[$]").
    setoid_rewrite pgl_wp_unfold.
    rewrite /pgl_wp_pre /= Hv.
    iApply ("Hcnt" $! (state_upd_tapes <[α:= (Z.to_nat z; ns' ++[sample]):tape]> σ) with "[$]").
  Qed. 

  Lemma read_counter_spec N E c γ1 γ2 γ3 P Q:
    ↑N ⊆ E ->
    {{{  inv N (counter_inv_pred c γ1 γ2 γ3) ∗
        □ (∀ (z:Z), P ∗ own γ3 (●F z) ={E∖↑N}=∗
                    own γ3 (●F z)∗ Q z)
         ∗ P
    }}}
      read_counter c @ E
      {{{ (n':Z), RET #n'; Q n'
      }}}.
  Proof.
    iIntros (Hsubset Φ) "(#Hinv & #Hvs & HP) HΦ".
    rewrite /read_counter.
    wp_pure.
    iInv N as ">(%ε & %m & %l & %z & H1 & H2 & H3 & H4 & -> & H5 & H6)" "Hclose".
    wp_load.
    iMod ("Hvs" with "[$]") as "[H6 HQ]".
    iMod ("Hclose" with "[$H1 $H2 $H3 $H4 $H5 $H6]"); first done.
    iApply ("HΦ" with "[$]").
  Qed. 
    
  
End impl1.
