From clutch.foxtrot Require Import foxtrot.

(* An abstract spec for a module that samples a number from 0 to N, but unknown distribution *)
Set Default Proof Using "Type*".

Class sample_spec (tb:nat) (sample_without_tape:val)  := SampleSpec
{
  (** * Operations *)
  sample_allocate_tape : val;
  sample_with_tape : val;

  (* For simplicity we dont do any error stuff *)
  (* sample_f: fin (S tb) -> R;  *)
  
  (** * Predicates *)
  sample_tape (α:val) (ns: (list nat)) `{!foxtrotGS Σ}: iProp Σ;
  sample_tape' (α:val) `{!foxtrotGS Σ}: iProp Σ; 
  (** * General properties of the predicates *)
  #[global] sample_tape_timeless  α ns `{!foxtrotGS Σ}::
    Timeless (sample_tape α ns);
  #[global] sample_tape_timeless'  α `{!foxtrotGS Σ}::
    Timeless (sample_tape' α);
  sample_tape_exclusive α ns ns' `{!foxtrotGS Σ}:
  sample_tape α ns -∗ sample_tape α ns' -∗ False;
  sample_tape_exclusive' α `{!foxtrotGS Σ}:
  sample_tape' α  -∗ sample_tape' α -∗ False;
  sample_tape_valid α ns `{!foxtrotGS Σ}:
  sample_tape α ns -∗ ⌜Forall (λ n, n<=tb)%nat ns⌝ ;

  
  sample_tape_presample E α ns `{!foxtrotGS Σ}:
  sample_tape α (ns) -∗
  pupd E E (∃ (n : fin (S tb )), sample_tape α (ns ++ [fin_to_nat n])); 
  
  (* sample_tape_presample E α ns ε (ε2 : fin (S tb) -> R): *)
  (* (∀ x, 0<=ε2 x)%R -> *)
  (* (SeriesC (λ n, sample_f n * ε2 n)%R <= ε)%R -> *)
  (* sample_tape α (ns) -∗ *)
  (* ↯ ε  -∗ *)
  (* pupd E E (∃ n, ↯ (ε2 n) ∗ sample_tape α (ns ++ [fin_to_nat n]));  *)
    

  (** * Program specs *)
  sample_allocate_tape_spec E `{!foxtrotGS Σ}:
    {{{ True }}}
      sample_allocate_tape #() @ E
      {{{ (v:val), RET v;
          sample_tape v ([])
      }}};
  
  sample_allocate_tape_spec' E j K `{!foxtrotGS Σ}:
  j ⤇ fill K (sample_allocate_tape #())  -∗
  pupd E E
    (∃ v, sample_tape' v ∗ j⤇ fill K v);
  
  sample_tape_spec_some E α n ns `{!foxtrotGS Σ}:
    {{{ sample_tape α (n::ns) }}}
      sample_with_tape α  @ E
      {{{ RET #n; sample_tape α (ns) }}};
  
  (* sample_tape_spec_couple E α ns j K `{!foxtrotGS Σ}: *)
  (* sample_tape α ns -∗ *)
  (* j ⤇ fill K (sample_without_tape #()) -∗ *)
  (* pupd E E *)
  (*   (∃ n, sample_tape α (ns++[n]) ∗ j⤇ fill K (#n)); *)
  
  sample_tape_spec_couple' E α  j K `{!foxtrotGS Σ}:
    {{{ sample_tape' α ∗ j ⤇ fill K (sample_with_tape α) }}}
      sample_without_tape #()  @ E
      {{{ (n:fin (S tb)), RET #n; sample_tape' α ∗ j⤇fill K (# n) }}};

  sample_without_tape_spec' E j K `{!foxtrotGS Σ}:
  j⤇ fill K (sample_without_tape #())
  -∗
    pupd E E
         (∃ (n:fin(S tb)), j ⤇ fill K #n)

  (* This next condition necessary? *)
  (* sample_tape_spec_some' E α j K: *)
  (* sample_tape' α -∗ *)
  (* j⤇ fill K (sample_with_tape α) -∗ *)
  (* pupd E E *)
  (*   (∃ (n : fin (S tb)), sample_tape' α ∗ j⤇ fill K #n) *)
  
    
  (* sample_tape_spec_some' E α ε (ε2 : fin (S tb) -> R) j K: *)
  (* (∀ x, 0<=ε2 x)%R -> *)
  (* (SeriesC (λ n, sample_f n * ε2 n)%R <= ε)%R -> *)
  (* sample_tape' α -∗ *)
  (* ↯ ε  -∗ *)
  (* j⤇ fill K (sample_with_tape α) -∗ *)
  (* pupd E E *)
  (*      (∃ n, sample_tape' α ∗ ↯ (ε2 n) ∗ j⤇ fill K #n) *)
}.


Section impl.
  #[local] Program Definition sample_spec1 (tb:nat)  `{!foxtrotGS Σ}: sample_spec tb ((λ: "_", rand #tb)):=
    {| sample_allocate_tape:= (λ: "_", alloc #tb);
      sample_with_tape:= (λ: "α", rand("α") #tb);
      sample_tape α ns _ _ := (∃ α', ⌜α = #lbl:α'⌝ ∗ (α' ↪N (tb; ns) ))%I;
      sample_tape' α _ _:= (∃ α', ⌜α = #lbl:α'⌝ ∗ (α' ↪ₛN (tb; []) ))%I;
    |}.
  Next Obligation.
    simpl.
    iIntros (????????) "(%&%&H1) (%&%&H2)".
    simplify_eq.
    iDestruct (tapeN_tapeN_contradict with "[$][$]") as "[]".
  Qed.
  Next Obligation.
    simpl. 
    iIntros (??????) "(%&%&H1) (%&%&H2)".
    simplify_eq.
    iDestruct (spec_tapeN_tapeN_contradict with "[$][$]") as "[]".
  Qed.
  Next Obligation.
    simpl.
    iIntros (???????) "(%&?&H1)".
    iApply (tapeN_ineq with "[$]").
  Qed.
  Next Obligation.
    simpl.
    iIntros (????????) "(%&->&?)".
    iMod (pupd_presample with "[$]") as "(%&?&%)".
    iModIntro.
    assert (n<S tb)%nat as K by lia.
    iExists (nat_to_fin K), _.
    rewrite fin_to_nat_to_fin. by iFrame.
  Qed.
  Next Obligation.
    simpl.
    iIntros (???????) "_ HΦ".
    wp_pures.
    wp_apply (wp_alloc_tape with "[//]") as (?) "?".
    iApply "HΦ".
    by iFrame.
  Qed.
  Next Obligation.
    simpl.
    iIntros (????????) "Hspec".
    tp_pure j.
    tp_allocnattape j α as "Hα".
    by iFrame.
  Qed. 
  Next Obligation.
    simpl.
    iIntros (??????????) "(%&->&?) HΦ".
    wp_pures.
    wp_randtape.
    iApply "HΦ".
    by iFrame.
  Qed.
  (* Next Obligation. *)
  (*   simpl. *)
  (*   iIntros (??????????) "(%&->&?)Hspec". *)
  (*   tp_pures j. *)
  (*   iMod (pupd_couple_tape_rand with "[$][$]") as "(%&?&?&%)"; first (simpl; lia). *)
  (*   by iFrame. *)
  (* Qed. *)
  Next Obligation.
    simpl.
    iIntros (??????????) "[(%&->&?)Hspec] HΦ".
    wp_pures.
    tp_pures j.
    wp_apply (wp_couple_rand_rand_lbl with "[$]"); first (simpl; lia).
    iIntros (?) "[?[?%]]".
    assert (n< S tb)%nat as K' by lia.
    replace n with (fin_to_nat (nat_to_fin K')); last by rewrite fin_to_nat_to_fin.
    iApply "HΦ".
    by iFrame.
  Qed.
  Next Obligation.
    simpl.
    iIntros (????????) "Hα".
    tp_pures j.
    iMod (pupd_rand with "[$]") as "(%n&Hα&%)".
    assert (n<S tb)%nat as K' by lia.
    replace n with (fin_to_nat (nat_to_fin K')); last by rewrite fin_to_nat_to_fin.
    by iFrame.
  Qed. 
  (* Next Obligation. *)
  (*   simpl. *)
  (*   iIntros (???????) "(%&->&?) Hspec". *)
  (*   tp_pures j. *)
  (*   iMod (pupd_rand_tape_empty with "[$][$]") as "(%&%&?&?)". *)
  (*   iFrame. *)
  (*   assert (n< S tb)%nat as K' by lia. *)
  (*   replace n with (fin_to_nat (nat_to_fin K')); last by rewrite fin_to_nat_to_fin. *)
  (*   by iFrame. *)
  (* Qed. *)


  
  #[local] Program Definition sample_spec2 (tb:nat)  `{!foxtrotGS Σ}: sample_spec tb ((λ: "_", #0)):=
    {| sample_allocate_tape:= (λ: "_", alloc #tb);
      sample_with_tape:= (λ: "α", #0);
      sample_tape α ns _ _:= (∃ α', ⌜α = #lbl:α'⌝ ∗ (α' ↪N (tb; []) ∗ ⌜Forall (λ x, x=0) ns⌝))%I;
      sample_tape' α _ _:= (∃ α', ⌜α = #lbl:α'⌝ ∗ (α' ↪ₛN (tb; []) ))%I;
    |}.
  Next Obligation.
    simpl.
    iIntros (????????) "(%&%&H1&%) (%&%&H2&%)".
    simplify_eq.
    iDestruct (tapeN_tapeN_contradict with "[$][$]") as "[]".
  Qed.
  Next Obligation.
    simpl. 
    iIntros (??????) "(%&%&H1) (%&%&H2)".
    simplify_eq.
    iDestruct (spec_tapeN_tapeN_contradict with "[$][$]") as "[]".
  Qed.
  Next Obligation.
    simpl.
    iIntros (???????) "(%&?&H1&%)".
    iPureIntro.
    eapply Forall_impl; first done.
    simpl. 
    intros. lia. 
  Qed.
  Next Obligation.
    simpl.
    iIntros (????????) "(%&->&?&%)".
    iModIntro.
    assert (0<S tb)%nat as K by lia.
    iExists (nat_to_fin K), _.
    iFrame. iSplit; first done.
    iPureIntro.
    apply Forall_app; split; first done.
    apply Forall_singleton. by rewrite fin_to_nat_to_fin. 
  Qed.
  Next Obligation.
    simpl.
    iIntros (???????) "_ HΦ".
    wp_pures.
    wp_apply (wp_alloc_tape with "[//]") as (?) "?".
    iApply "HΦ".
    by iFrame.
  Qed.
  Next Obligation.
    simpl.
    iIntros (????????) "Hspec".
    tp_pure j.
    tp_allocnattape j α as "Hα".
    by iFrame.
  Qed. 
  Next Obligation.
    simpl.
    iIntros (??????????) "(%&->&?&%H) HΦ".
    wp_pures.
    inversion H. subst.
    iApply "HΦ".
    by iFrame.
  Qed.
  (* Next Obligation. *)
  (*   simpl. *)
  (*   iIntros (??????????) "(%&->&?&%)Hspec". *)
  (*   tp_pures j. *)
  (*   iModIntro. *)
  (*   iExists 0. iFrame. *)
  (*   iPureIntro; split; first done. *)
  (*   apply Forall_app; split; first done. *)
  (*   by apply Forall_singleton. *)
  (* Qed. *)
  Next Obligation.
    simpl.
    iIntros (??????????) "[(%&->&?)Hspec] HΦ".
    tp_pures j.
    wp_pures.
    assert (0< S tb)%nat as K' by lia.
    replace (LitInt 0)%nat with (LitInt $ fin_to_nat (nat_to_fin K')); last by rewrite fin_to_nat_to_fin.
    iApply "HΦ".
    by iFrame.
  Qed.
  Next Obligation.
    simpl.
    iIntros (????????) "Hspec".
    tp_pures j.
    assert (0<S tb)%nat as K' by lia.
    replace (LitInt 0) with (LitInt (fin_to_nat (nat_to_fin K'))); last by rewrite fin_to_nat_to_fin.
    by iFrame.
  Qed. 
  (* Next Obligation. *)
  (*   simpl. *)
  (*   iIntros (???????) "(%&->&?) Hspec". *)
  (*   tp_pures j. *)
  (*   assert (0< S tb)%nat as K' by lia. *)
  (*   replace (LitInt 0)%nat with (LitInt $ fin_to_nat (nat_to_fin K')); last by rewrite fin_to_nat_to_fin. *)
  (*   by iFrame. *)
  (* Qed. *)
    
End impl.
