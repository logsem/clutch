From clutch.coneris Require Import coneris.

Set Default Proof Using "Type*".

Class random_counter `{!conerisGS Σ} := RandCounter
{
  (** * Operations *)
  new_counter : val;
  (* incr_counter : val; *)
  allocate_tape : val;
  incr_counter_tape : val;
  read_counter : val;
  (** * Ghost state *)
  (** The assumptions about [Σ] *)
  counterG : gFunctors → Type;
  (** [name] is used to associate [locked] with [is_lock] *)
  tape_name: Type;
  counter_name: Type;
  (** * Predicates *)
  is_counter {L : counterG Σ} (N:namespace) (counter: val)
    (γ1: tape_name) (γ2: counter_name): iProp Σ;
  counter_tapes_auth {L : counterG Σ} (γ: tape_name) (m:gmap loc (list nat)): iProp Σ;
  counter_tapes_frag {L : counterG Σ} (γ: tape_name) (α:loc) (ns:list nat): iProp Σ;
  counter_content_auth {L : counterG Σ} (γ: counter_name) (z:nat): iProp Σ;
  counter_content_frag {L : counterG Σ} (γ: counter_name) (f:frac) (z:nat): iProp Σ;
  (** * General properties of the predicates *)
  #[global] is_counter_persistent {L : counterG Σ} N c γ1 γ2 ::
    Persistent (is_counter (L:=L) N c γ1 γ2);
  #[global] counter_tapes_auth_timeless {L : counterG Σ} γ m ::
    Timeless (counter_tapes_auth (L:=L) γ m);
  #[global] counter_tapes_frag_timeless {L : counterG Σ} γ α ns ::
    Timeless (counter_tapes_frag (L:=L) γ α ns);
  #[global] counter_content_auth_timeless {L : counterG Σ} γ z ::
    Timeless (counter_content_auth (L:=L) γ z);
  #[global] counter_content_frag_timeless {L : counterG Σ} γ f z ::
    Timeless (counter_content_frag (L:=L) γ f z);
  
  counter_tapes_auth_exclusive {L : counterG Σ} γ m m':
  counter_tapes_auth (L:=L) γ m -∗ counter_tapes_auth (L:=L) γ m' -∗ False;
  counter_tapes_frag_exclusive {L : counterG Σ} γ α ns ns':
  counter_tapes_frag (L:=L) γ α ns -∗ counter_tapes_frag (L:=L) γ α ns' -∗ False;
  counter_tapes_agree {L : counterG Σ} γ α m ns:
  counter_tapes_auth (L:=L) γ m -∗ counter_tapes_frag (L:=L) γ α ns -∗ ⌜ m!! α = Some (ns) ⌝;
  counter_tapes_valid {L : counterG Σ} γ α ns:
    counter_tapes_frag (L:=L) γ α ns -∗ ⌜Forall (λ n, n<=3)%nat ns⌝;
  counter_tapes_update {L : counterG Σ} γ α m ns ns':
    Forall (λ x, x<=3%nat) ns'->
    counter_tapes_auth (L:=L) γ m -∗ counter_tapes_frag (L:=L) γ α ns ==∗
    counter_tapes_auth (L:=L) γ (<[α := ns']> m) ∗ counter_tapes_frag (L:=L) γ α (ns');

  counter_content_auth_exclusive {L : counterG Σ} γ z1 z2:
    counter_content_auth (L:=L) γ z1 -∗ counter_content_auth (L:=L) γ z2 -∗ False;
  counter_content_less_than {L : counterG Σ} γ z z' f:
  counter_content_auth (L:=L) γ z -∗ counter_content_frag (L:=L) γ f z' -∗ ⌜(z'<=z)%nat ⌝;
  counter_content_frag_combine {L:counterG Σ} γ f f' z z':
    (counter_content_frag (L:=L) γ f z ∗ counter_content_frag (L:=L) γ f' z')%I ≡
    counter_content_frag (L:=L) γ (f+f')%Qp (z+z')%nat;
  counter_content_agree {L : counterG Σ} γ z z':
    counter_content_auth (L:=L) γ z -∗ counter_content_frag (L:=L) γ 1%Qp z' -∗ ⌜(z'=z)%nat ⌝;
  counter_content_update {L : counterG Σ} γ f z1 z2 z3:
    counter_content_auth (L:=L) γ z1 -∗ counter_content_frag (L:=L) γ f z2 ==∗
    counter_content_auth (L:=L) γ (z1+z3)%nat ∗ counter_content_frag (L:=L) γ f (z2+z3)%nat;
  
  (** * Program specs *)
  new_counter_spec {L : counterG Σ} E N:
  {{{ True }}} new_counter #() @E
    {{{ c, RET c; ∃ γ1 γ2, is_counter (L:=L) N c γ1 γ2 ∗
                           counter_content_frag (L:=L) γ2 1%Qp 0%nat
    }}};
  allocate_tape_spec {L: counterG Σ} N E c γ1 γ2:
    ↑N ⊆ E->
    {{{ is_counter (L:=L) N c γ1 γ2 }}}
      allocate_tape #() @ E
      {{{ (v:val), RET v;
          ∃ (α:loc), ⌜v=#lbl:α⌝ ∗ counter_tapes_frag (L:=L) γ1 α []
      }}};
  incr_counter_tape_spec_some {L: counterG Σ} N E c γ1 γ2 (Q:nat->nat->list nat->iProp Σ) (α:loc) :
    ↑N⊆E ->
    {{{ is_counter (L:=L) N c γ1 γ2 ∗
        (∀ (z:nat), counter_content_auth (L:=L) γ2 z ={E∖ ↑N, ∅}=∗
                   ∃ n ns, counter_tapes_frag (L:=L) γ1 α (n::ns) ∗
                    (counter_tapes_frag (L:=L) γ1 α ns ={∅, E∖↑N}=∗
                     counter_content_auth (L:=L) γ2 (z+n) ∗ Q z n ns)
          ) 
    }}}
      incr_counter_tape c #lbl:α @ E
                                 {{{ (z n:nat), RET (#z, #n); ∃ ns, Q z n ns}}}; 
  counter_presample_spec {L: counterG Σ} NS E T γ1 γ2 c:
    ↑NS ⊆ E ->
    is_counter (L:=L) NS c γ1 γ2 -∗
    ( |={E∖↑NS,∅}=>
        ∃ ε α ε2 num ns,
        ↯ ε ∗ counter_tapes_frag (L:=L) γ1 α ns ∗
        ⌜(∀ n, 0<=ε2 n)%R⌝ ∗
        ⌜(SeriesC (λ l, if bool_decide (l∈fmap (λ x, fmap (FMap:=list_fmap) fin_to_nat x) (enum_uniform_fin_list 3%nat num)) then ε2 l else 0%R) / (4^num) <= ε)%R⌝ ∗
      (∀ ns', ↯ (ε2 ns') ∗ counter_tapes_frag (L:=L) γ1 α (ns++ns')={∅,E∖↑NS}=∗
              T ε α ε2 num ns ns'
      ))-∗ 
        wp_update E (∃ ε α ε2 num ns ns', T ε α ε2 num ns ns'); 
  read_counter_spec {L: counterG Σ} N E c γ1 γ2 Q:
    ↑N ⊆ E ->
    {{{  is_counter (L:=L) N c γ1 γ2 ∗
         (∀ (z:nat), counter_content_auth (L:=L) γ2 z ={E∖↑N}=∗
                    counter_content_auth (L:=L) γ2 z∗ Q z)
        
    }}}
      read_counter c @ E
      {{{ (n':nat), RET #n'; Q n'
      }}}
}.


Section lemmas.
  Context `{rc:random_counter} {L: counterG Σ}.
  
  Lemma incr_counter_tape_spec_none  N E c γ1 γ2 Q α:
    ↑N ⊆ E->
    {{{ is_counter (L:=L) N c γ1 γ2 ∗
        ( |={E∖↑N, ∅}=>
            ∃ ε ε2,
              ↯ ε ∗ counter_tapes_frag (L:=L) γ1 α [] ∗
              ⌜(∀ n, 0<=ε2 n)%R⌝ ∗
              ⌜(((ε2 0%nat) + (ε2 1%nat)+ (ε2 2%nat)+ (ε2 3%nat))/4 <= ε)%R⌝ ∗
              (∀ n, ↯ (ε2 n) ∗ counter_tapes_frag (L:=L) γ1 α [n] ={∅,E∖↑N}=∗
                    ∀ (z:nat), counter_content_auth (L:=L) γ2 z ={E∖↑N, ∅}=∗
                             counter_tapes_frag (L:=L) γ1 α [n]∗
                           (counter_tapes_frag (L:=L) γ1 α []={∅, E∖↑N}=∗
                    counter_content_auth (L:=L) γ2 (z+n) ∗ Q z n ε ε2
              )
              )
        ) 
    }}}
      incr_counter_tape c #lbl:α @ E
                                 {{{ (z n:nat), RET (#z, #n); ∃ ε ε2, Q z n ε ε2 }}}.
  Proof.
    iIntros (Hsubset Φ) "(#Hinv & Hvs) HΦ".
    iMod (counter_presample_spec _ _
            (λ ε α' ε2 num ns ns',
               ∃ n ε2', 
                 ⌜num=1%nat⌝ ∗ ⌜α'=α⌝ ∗ ⌜ns=[]⌝ ∗ ⌜ns'=[n]⌝ ∗
                 ⌜(ε2' = λ x, ε2 [x])%R⌝ ∗
                 (∀ z : nat,
                    counter_content_auth γ2 z ={E ∖ ↑N,∅}=∗
                    counter_tapes_frag γ1 α [n] ∗
                    (counter_tapes_frag γ1 α [] ={∅,E ∖ ↑N}=∗
                    counter_content_auth γ2 (z + n) ∗ Q z n ε ε2'))
            )%I with "[//][-HΦ]") as "(%ε & % & %ε2 & %num & %ns & %ns' & %n & %ε2' & -> & -> & -> & -> & -> & Hrest)"; try done.
    - iMod "Hvs" as "(%ε & %ε2 & Herr & Hfrag & %Hpos & %Hineq & Hrest)".
      iFrame. iModIntro.
      iExists (λ l, match l with |[x] => ε2 x | _ => 1 end)%R, 1%nat.
      repeat iSplit.
      + iPureIntro. intros; repeat case_match; try lra. naive_solver.
      + iPureIntro. etrans; last exact.
        rewrite SeriesC_list.
        * Local Transparent enum_uniform_fin_list.
          simpl. lra.
        * apply NoDup_fmap_2; last apply NoDup_enum_uniform_fin_list.
          apply list_fmap_eq_inj, fin_to_nat_inj.
      + iIntros (ns') "[Herr Hfrag]". destruct (ns') as [|n[|??]]; [by iDestruct (ec_contradict with "[$]") as "%"| |by iDestruct (ec_contradict with "[$]") as "%"].
        iMod ("Hrest" $! n with "[$]").
        iFrame.
        by iPureIntro.
    - wp_apply (incr_counter_tape_spec_some _ _ _ _ _ (λ z n ns, ∃ ε ε2, Q z n ε ε2)%I with "[Hrest]"); first exact.
      + iSplit; first done.
        iIntros (z) "Hauth".
        iMod ("Hrest" with "[$]") as "[Hfrag Hrest]".
        iFrame.
        iModIntro.
        iIntros "Hfrag".
        iMod ("Hrest" with "[$]") as "[Hauth HQ]".
        by iFrame.
      + iIntros (??) "(%&%&%&HQ)".
        iApply "HΦ".
        iFrame.
  Qed.
  
  Lemma incr_counter_tape_spec_none' N E c γ1 γ2 ε (ε2:nat -> R)(α:loc) (ns:list nat) (q:Qp) (z:nat):
    ↑N ⊆ E->
    (∀ n, 0<= ε2 n)%R->
    (((ε2 0%nat) + (ε2 1%nat)+ (ε2 2%nat)+ (ε2 3%nat))/4 <= ε)%R →
    {{{ is_counter (L:=L) N c γ1 γ2 ∗
        ↯ ε ∗
        counter_tapes_frag (L:=L) γ1 α [] ∗
        counter_content_frag (L:=L) γ2 q z
    }}}
      incr_counter_tape c #lbl:α @ E
                                 {{{ (z':nat) (n:nat),
                                       RET (#z', #n); ⌜(0<=n<4)%nat⌝ ∗
                                                      ⌜(z<=z')%nat⌝ ∗
                                                      ↯(ε2 n) ∗
                                                     counter_tapes_frag (L:=L) γ1 α [] ∗
                                                     counter_content_frag (L:=L) γ2 q (z+n)%nat }}}.
  Proof.
    iIntros (Hsubset Hpos Hineq Φ) "(#Hinv & Herr & Htapes & Hcontent) HΦ".
    pose (ε2' := (λ x, if (x<=?3)%nat then ε2 x else 1%R)).
    wp_apply (incr_counter_tape_spec_none _ _ _ _ _ 
                (λ z' n ε' ε2'', ⌜0<=n<4⌝ ∗ ⌜z<=z'⌝ ∗ ⌜ε=ε'⌝ ∗ ⌜ε2''=ε2'⌝ ∗
                                 ↯ (ε2' n) ∗ counter_tapes_frag (L:=L) γ1 α [] ∗
                                 counter_content_frag (L:=L) γ2 q (z+n)%nat
                )%I
               with "[-HΦ]").
    - done.
    - iSplit; first done.
      iApply fupd_mask_intro; first set_solver.
      iIntros "Hclose".
      iFrame.
      iExists ε2'.
      repeat iSplit.
      + iPureIntro. rewrite /ε2'. intros; case_match; [naive_solver|lra].
      + done.
      + iIntros (n) "[Herr Hfrag]".
        iMod "Hclose" as "_".
        iModIntro.
        iIntros (z') "Hauth".
        iApply fupd_mask_intro; first set_solver.
        iIntros "Hclose".
        rewrite /ε2'.
        case_match eqn:H; last by (iDestruct (ec_contradict with "[$]") as "%").
        iFrame.
        iIntros "Hfrag'".
        iDestruct (counter_content_less_than with "[$][$]") as "%".
        iMod (counter_content_update with "[$][$]") as "[??]".
        iMod "Hclose" as "_".
        iFrame.
        apply leb_complete in H.
        iPureIntro; repeat split; try done; lia. 
    - iIntros (z' n) "(%ε' & %ε2'' & % & % &-> & -> & Herr & Hfrag & Hfrag')".
      iApply "HΦ".
      iFrame.
      iSplit; first done.
      iSplit; first done.
      iApply ec_eq; last done.
      rewrite /ε2'.
      case_match eqn :K; first done.
      exfalso.
      apply leb_complete_conv in K.
      lia.
  Qed.
  
End lemmas.

