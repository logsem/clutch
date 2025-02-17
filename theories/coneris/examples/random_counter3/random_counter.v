From clutch.coneris Require Import coneris.

Set Default Proof Using "Type*".

Class random_counter `{!conerisGS Σ} := RandCounter
{
  (** * Operations *)
  new_counter : val;
  (* incr_counter : val; *)
  incr_counter : val;
  read_counter : val;
  (** * Ghost state *)
  (** The assumptions about [Σ] *)
  counterG : gFunctors → Type;
  (** [name] is used to associate [locked] with [is_lock] *)
  counter_name: Type;
  (** * Predicates *)
  is_counter {L : counterG Σ} (N:namespace) (counter: val) (γ: counter_name): iProp Σ;
  counter_content_auth {L : counterG Σ} (γ: counter_name) (z:nat): iProp Σ;
  counter_content_frag {L : counterG Σ} (γ: counter_name) (f:frac) (z:nat): iProp Σ;
  (** * General properties of the predicates *)
  #[global] is_counter_persistent {L : counterG Σ} N c γ1 ::
    Persistent (is_counter (L:=L) N c γ1);
  #[global] counter_content_auth_timeless {L : counterG Σ} γ z ::
    Timeless (counter_content_auth (L:=L) γ z);
  #[global] counter_content_frag_timeless {L : counterG Σ} γ f z ::
    Timeless (counter_content_frag (L:=L) γ f z);

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
    {{{ c, RET c; ∃ γ1, is_counter (L:=L) N c γ1 ∗
                           counter_content_frag (L:=L) γ1 1%Qp 0%nat
    }}};
  incr_counter_spec {L: counterG Σ} N E c γ1 (Q:_->_->nat->nat->iProp Σ)  :
    ↑N⊆E ->
    {{{ is_counter (L:=L) N c γ1 ∗
        |={E,∅}=>
          (∃ ε (ε2 : fin 4%nat -> R),
              ↯ ε ∗ ⌜(∀ x, 0<=ε2 x)%R⌝∗
              ⌜(SeriesC (λ n, 1 / 4 * ε2 n)%R <= ε)%R ⌝ ∗
              (∀ n, ↯ (ε2 n) ={∅, E}=∗
          (∀ (z:nat), counter_content_auth (L:=L) γ1 z ={E∖↑N}=∗
                      counter_content_auth (L:=L) γ1 (z+n) ∗ Q ε ε2 z n)))
           
    }}}
      incr_counter c @ E
                                 {{{ (z n:nat), RET (#z, #n); ∃ ε ε2, Q ε ε2 z n }}}; 
  read_counter_spec {L: counterG Σ} N E c γ1 Q:
    ↑N ⊆ E ->
    {{{  is_counter (L:=L) N c γ1 ∗
         (∀ (z:nat), counter_content_auth (L:=L) γ1 z ={E∖↑N}=∗
                    counter_content_auth (L:=L) γ1 z∗ Q z)
        
    }}}
      read_counter c @ E
      {{{ (n':nat), RET #n'; Q n'
      }}}
}.


Section lemmas.
  Context `{rc:random_counter} {L: counterG Σ}.
  
  Lemma incr_counter_spec_seq N E c γ1 ε (ε2:nat -> R) (q:Qp) (z:nat):
    ↑N ⊆ E->
    (∀ n, 0<= ε2 n)%R->
    (((ε2 0%nat) + (ε2 1%nat)+ (ε2 2%nat)+ (ε2 3%nat))/4 <= ε)%R →
    {{{ is_counter (L:=L) N c γ1 ∗
        ↯ ε ∗
        counter_content_frag (L:=L) γ1 q z
    }}}
      incr_counter c  @ E
                                 {{{ (z':nat) (n:nat),
                                       RET (#z', #n); ⌜(0<=n<4)%nat⌝ ∗
                                                      ⌜(z<=z')%nat⌝ ∗
                                                      ↯(ε2 n) ∗
                                                     counter_content_frag (L:=L) γ1 q (z+n)%nat }}}.
  Proof.
    iIntros (Hsubset Hpos Hineq Φ) "(#Hinv & Herr & Hcontent) HΦ".
    pose (ε2' := (λ x, if (x<=?3)%nat then ε2 x else 1%R)).
    wp_apply (incr_counter_spec _ _ _ _
                (λ _ _ z' n , ⌜0<=n<4⌝ ∗ ⌜z<=z'⌝ ∗
                          ↯ (ε2 n) ∗
                                 counter_content_frag (L:=L) γ1 q (z+n)%nat
                )%I
               with "[-HΦ]").
    - done.
    - iSplit; first done.
      iApply fupd_mask_intro; first set_solver.
      iIntros "Hclose".
      iFrame.
      iExists (λ x, ε2 (fin_to_nat x)); repeat iSplit; try done.
      + rewrite SeriesC_finite_foldr/=. iPureIntro. lra.
      + iIntros (?) "?".
        iMod "Hclose". iModIntro.
        iIntros (?) "?".
        iDestruct (counter_content_less_than with "[$][$]") as "%".
        iMod (counter_content_update with "[$][$]") as "[??]".
        iFrame.
        iModIntro.
        iPureIntro; repeat split; try done; try lia.
        apply fin_to_nat_lt.
    - iIntros (z' n) "(% & % & Herr & Hfrag' )".
      iApply "HΦ".
      iFrame.
  Qed.
  
End lemmas.

