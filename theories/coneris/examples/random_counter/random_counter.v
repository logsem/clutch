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
  error_name : Type;
  tape_name: Type;
  counter_name: Type;
  (** * Predicates *)
  is_counter {L : counterG Σ} (N:namespace) (counter: val)
    (γ1: error_name) (γ2: tape_name) (γ3: counter_name): iProp Σ;
  counter_error_auth {L : counterG Σ} (γ: error_name) (x:R): iProp Σ;
  counter_error_frag {L : counterG Σ} (γ: error_name) (x:R): iProp Σ;
  counter_tapes_auth {L : counterG Σ} (γ: tape_name) (m:gmap loc (list nat)): iProp Σ;
  counter_tapes_frag {L : counterG Σ} (γ: tape_name) (α:loc) (ns:list nat): iProp Σ;
  counter_content_auth {L : counterG Σ} (γ: counter_name) (z:nat): iProp Σ;
  counter_content_frag {L : counterG Σ} (γ: counter_name) (f:frac) (z:nat): iProp Σ;
  (** * General properties of the predicates *)
  #[global] is_counter_persistent {L : counterG Σ} N c γ1 γ2 γ3 ::
    Persistent (is_counter (L:=L) N c γ1 γ2 γ3);
  #[global] counter_error_auth_timeless {L : counterG Σ} γ x ::
    Timeless (counter_error_auth (L:=L) γ x);
  #[global] counter_error_frag_timeless {L : counterG Σ} γ x ::
    Timeless (counter_error_frag (L:=L) γ x);
  #[global] counter_tapes_auth_timeless {L : counterG Σ} γ m ::
    Timeless (counter_tapes_auth (L:=L) γ m);
  #[global] counter_tapes_frag_timeless {L : counterG Σ} γ α ns ::
    Timeless (counter_tapes_frag (L:=L) γ α ns);
  #[global] counter_content_auth_timeless {L : counterG Σ} γ z ::
    Timeless (counter_content_auth (L:=L) γ z);
  #[global] counter_content_frag_timeless {L : counterG Σ} γ f z ::
    Timeless (counter_content_frag (L:=L) γ f z);

  counter_error_auth_exclusive {L : counterG Σ} γ x1 x2:
    counter_error_auth (L:=L) γ x1 -∗ counter_error_auth (L:=L) γ x2 -∗ False;
  counter_error_frag_exclusive {L : counterG Σ} γ x1 x2:
  counter_error_frag (L:=L) γ x1 -∗ counter_error_frag (L:=L) γ x2 -∗ False;
  counter_error_auth_valid {L : counterG Σ} γ x:
    counter_error_auth (L:=L) γ x -∗ ⌜(0<=x<1)%R⌝;
  counter_error_auth_valid {L : counterG Σ} γ x:
    counter_error_frag (L:=L) γ x -∗ ⌜(0<=x<1)%R⌝;
  counter_error_agree {L : counterG Σ} γ x1 x2:
    counter_error_auth (L:=L) γ x1 -∗ counter_error_frag (L:=L) γ x2 -∗ ⌜x1 = x2 ⌝;
  counter_error_update {L : counterG Σ} γ x1 x2 (x3:nonnegreal):
    counter_error_auth (L:=L) γ x1 -∗ counter_error_frag (L:=L) γ x2 ==∗
    counter_error_auth (L:=L) γ x3 ∗ counter_error_frag (L:=L) γ x3;

  counter_tapes_auth_exclusive {L : counterG Σ} γ m m':
  counter_tapes_auth (L:=L) γ m -∗ counter_tapes_auth (L:=L) γ m' -∗ False;
  counter_tapes_frag_exclusive {L : counterG Σ} γ α ns ns':
  counter_tapes_frag (L:=L) γ α ns -∗ counter_tapes_frag (L:=L) γ α ns' -∗ False;
  counter_tapes_agree {L : counterG Σ} γ α m ns:
    counter_tapes_auth (L:=L) γ m -∗ counter_tapes_frag (L:=L) γ α ns -∗ ⌜ m!! α = Some (ns) ⌝;
  counter_tapes_update {L : counterG Σ} γ α m ns n:
    counter_tapes_auth (L:=L) γ m -∗ counter_tapes_frag (L:=L) γ α ns ==∗
    counter_tapes_auth (L:=L) γ (<[α := (ns ++[n])]> m) ∗ counter_tapes_frag (L:=L) γ α (ns ++ [n]);

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
  new_counter_spec {L : counterG Σ} E ε N:
  {{{ ↯ ε }}} new_counter #() @E
    {{{ c, RET c; ∃ γ1 γ2 γ3, is_counter (L:=L) N c γ1 γ2 γ3 ∗
                              counter_error_frag (L:=L) γ1 ε ∗
                              counter_content_frag (L:=L) γ3 1%Qp 0%nat
    }}};
  allocate_tape_spec {L: counterG Σ} N E c γ1 γ2 γ3:
    ↑N ⊆ E->
    {{{ is_counter (L:=L) N c γ1 γ2 γ3 }}}
      allocate_tape #() @ E
      {{{ (v:val), RET v;
          ∃ (α:loc), ⌜v=#lbl:α⌝ ∗ counter_tapes_frag (L:=L) γ2 α []
      }}};
  incr_counter_tape_spec_some {L: counterG Σ} N E c γ1 γ2 γ3 (P: iProp Σ) (Q:nat->iProp Σ) (α:loc) (n:nat) ns:
    ↑N⊆E -> 
    {{{ is_counter (L:=L) N c γ1 γ2 γ3 ∗
        □ (∀ (z:nat), P ∗ counter_content_auth (L:=L) γ3 z ={E∖↑N}=∗
                          counter_content_auth (L:=L) γ3 (z+n)%nat ∗ Q z) ∗
        P ∗ counter_tapes_frag (L:=L) γ2 α (n::ns)
    }}}
      incr_counter_tape c #lbl:α @ E
                                 {{{ (z:nat), RET (#z, #n); Q z ∗ counter_tapes_frag (L:=L) γ2 α ns}}};
  counter_presample_spec {L: counterG Σ} NS E ns α
     (ε2 : R -> nat -> R)
    (P : iProp Σ) T γ1 γ2 γ3 c:
    ↑NS ⊆ E ->
    (∀ ε n, 0<= ε -> 0<=ε2 ε n)%R ->
    (∀ (ε:R), 0<= ε ->SeriesC (λ n, if (bool_decide (n≤3%nat)) then 1 / (S 3%nat) * ε2 ε n else 0%R)%R <= ε)%R->
    is_counter (L:=L) NS c γ1 γ2 γ3 -∗
    (□∀ (ε:R) n, (P ∗ counter_error_auth (L:=L) γ1 ε) ={E∖↑NS}=∗
        (⌜(1<=ε2 ε n)%R⌝ ∨ (counter_error_auth (L:=L) γ1 (ε2 ε n)  ∗ T (n)))) 
        -∗
    P -∗ counter_tapes_frag (L:=L) γ2 α ns-∗
        wp_update E (∃ n, T (n) ∗ counter_tapes_frag (L:=L) γ2 α (ns++[n]));
  read_counter_spec {L: counterG Σ} N E c γ1 γ2 γ3 P Q:
    ↑N ⊆ E ->
    {{{  is_counter (L:=L) N c γ1 γ2 γ3  ∗
        □ (∀ (z:nat), P ∗ counter_content_auth (L:=L) γ3 z ={E∖↑N}=∗
                    counter_content_auth (L:=L) γ3 z∗ Q z)
         ∗ P
    }}}
      read_counter c @ E
      {{{ (n':nat), RET #n'; Q n'
      }}}
}.


Section lemmas.
  Context `{rc:random_counter} {L: counterG Σ}.
  
  Lemma incr_counter_tape_spec_none  N E c γ1 γ2 γ3 (ε2:R -> nat -> R) (P: iProp Σ) (T: nat -> iProp Σ) (Q: nat -> nat -> iProp Σ)(α:loc):
    ↑N ⊆ E->
    (∀ ε n, 0<= ε -> 0<= ε2 ε n)%R->
    (∀ (ε:R), 0<=ε -> ((ε2 ε 0%nat) + (ε2 ε 1%nat)+ (ε2 ε 2%nat)+ (ε2 ε 3%nat))/4 <= ε)%R →
    {{{ is_counter (L:=L) N c γ1 γ2 γ3 ∗
        □(∀ (ε:R) (n : nat), P ∗ counter_error_auth (L:=L) γ1 ε
                           ={E∖↑N}=∗ (⌜(1<=ε2 ε n)%R⌝∨ counter_error_auth (L:=L) γ1 (ε2 ε n) ∗ T n) ) ∗
        □ (∀ (n:nat) (z:nat), T n ∗ counter_content_auth (L:=L) γ3 z  ={E∖↑N}=∗
                          counter_content_auth (L:=L) γ3 (z+n)%nat ∗ Q z n) ∗
        P ∗ counter_tapes_frag (L:=L) γ2 α []
    }}}
      incr_counter_tape c #lbl:α @ E
                                 {{{ (z:nat) (n:nat), RET (#z, #n); Q z n ∗ counter_tapes_frag (L:=L) γ2 α [] }}}.
  Proof.
    iIntros (Hsubset Hpos Hineq Φ) "(#Hinv & #Hvs1 & #Hvs2 & HP & Hα) HΦ".
    iMod (counter_presample_spec with "[//][//][$][$]") as "(%&HT&Hα)"; try done.
    { intros ε Hε. specialize (Hineq ε Hε).
      rewrite SeriesC_nat_bounded_fin SeriesC_finite_foldr /=. lra.
    }
    iApply (incr_counter_tape_spec_some _ _ _ _ _ _ (T n) (λ x, Q x n) with "[$Hα $HT]"); try done.
    { by iSplit. }
    iNext.
    iIntros. iApply ("HΦ" with "[$]").
  Qed.

  Lemma incr_counter_tape_spec_none' N E c γ1 γ2 γ3 ε (ε2:R -> nat -> R)(α:loc) (ns:list nat) (q:Qp) (z:nat):
    ↑N ⊆ E->
    (∀ ε n, 0<= ε -> 0<= ε2 ε n)%R->
    (∀ (ε:R), 0<=ε -> ((ε2 ε 0%nat) + (ε2 ε 1%nat)+ (ε2 ε 2%nat)+ (ε2 ε 3%nat))/4 <= ε)%R →
    {{{ is_counter (L:=L) N c γ1 γ2 γ3 ∗
        counter_error_frag (L:=L) γ1 ε ∗
        counter_tapes_frag (L:=L) γ2 α [] ∗
        counter_content_frag (L:=L) γ3 q z 
    }}}
      incr_counter_tape c #lbl:α @ E
                                 {{{ (z':nat) (n:nat),
                                       RET (#z', #n); ⌜(0<=n<4)%nat⌝ ∗
                                                      ⌜(z<=z')%nat⌝ ∗
                                                     counter_error_frag (L:=L) γ1 (ε2 ε n) ∗
                                                     counter_tapes_frag (L:=L) γ2 α [] ∗
                                                     counter_content_frag (L:=L) γ3 q (z+n)%nat }}}.
  Proof.
    iIntros (Hsubset Hpos Hineq Φ) "(#Hinv & Herr & Htapes & Hcontent) HΦ".
    pose (ε2' := (λ ε x, if (x<=?3)%nat then ε2 ε x else 1%R)).
    wp_apply (incr_counter_tape_spec_none _ _ _ _ _ _ ε2'
                (counter_error_frag γ1 ε ∗ counter_content_frag γ3 q z)%I
                (λ n, ⌜0<=n<4⌝ ∗ counter_error_frag γ1 (ε2' ε n) ∗ counter_content_frag γ3 q z)%I
                (λ z' n, ⌜0<=n<4⌝ ∗ ⌜z<=z'⌝ ∗ counter_error_frag γ1 (ε2' ε n) ∗ counter_content_frag γ3 q (z+n)%nat)%I
               with "[$Herr $Htapes $Hcontent]").
    - done.
    - rewrite /ε2'. intros.
      case_match; [naive_solver|lra].
    - rewrite /ε2'. simpl. intros. naive_solver.
    - repeat iSplit; first done.
      + iModIntro.
        iIntros (ε' n) "[(Herr &Hcontent) Herr_auth]".
        destruct (n<=?3) eqn:H; last first.
        { iLeft. iPureIntro. rewrite /ε2'. by rewrite H. }
        iRight.
        iFrame.
        iDestruct (counter_error_agree with "[$][$]") as "->".
        iDestruct (counter_error_auth_pos with "[$]") as "%".
        unshelve iMod (counter_error_update _ _ _ (mknonnegreal (ε2' ε n) _) with "[$][$]") as "[$$]".
        { rewrite /ε2' H. 
          naive_solver. }
        iPureIntro. split; first lia.
        apply leb_complete in H. lia.
      + iModIntro.
        iIntros (??) "[(%&Herr & Hcontent) Hcontent_auth]".
        iFrame.
        iDestruct (counter_content_less_than with "[$][$]") as "%".
        by iMod (counter_content_update with "[$][$]") as "[$ $]".
    - iIntros (??) "[(%&%&?&?)?]".
      iApply "HΦ".
      iFrame.
      rewrite /ε2'. case_match eqn: H2; first by iFrame.
      apply leb_iff_conv in H2. lia.
  Qed.
  
End lemmas.
