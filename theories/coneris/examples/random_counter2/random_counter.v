From coneris.coneris Require Import coneris.

Set Default Proof Using "Type*".

Class random_counter `{!conerisGS Σ} := RandCounter
{
  (** * Operations *)
  new_counter : val;
  incr_counter : val;
  read_counter : val;
  (** * Ghost state *)
  (** The assumptions about [Σ] *)
  counterG : gFunctors → Type;
  (** [name] is used to associate [locked] with [is_lock] *)
  (* tape_name: Type; *)
  counter_name: Type;
  (** * Predicates *)
  is_counter {L : counterG Σ} (N:namespace) (counter: val) (γ: counter_name): iProp Σ;
  counter_tapes {L : counterG Σ} (α:val) (n:option nat): iProp Σ;
  counter_content_auth {L : counterG Σ} (γ: counter_name) (z:nat): iProp Σ;
  counter_content_frag {L : counterG Σ} (γ: counter_name) (f:frac) (z:nat): iProp Σ;
  (** * General properties of the predicates *)
  #[global] is_counter_persistent {L : counterG Σ} N c γ1 ::
    Persistent (is_counter (L:=L) N c γ1);
  #[global] counter_tapes_timeless {L : counterG Σ} α ns ::
    Timeless (counter_tapes (L:=L) α ns);
  #[global] counter_content_auth_timeless {L : counterG Σ} γ z ::
    Timeless (counter_content_auth (L:=L) γ z);
  #[global] counter_content_frag_timeless {L : counterG Σ} γ f z ::
    Timeless (counter_content_frag (L:=L) γ f z);
  
                                
  counter_tapes_presample {L:counterG Σ} N E γ c α ε (ε2 : fin 4%nat -> R):
  ↑N ⊆ E ->
  (∀ x, 0<=ε2 x)%R ->
  (SeriesC (λ n, 1 / 4 * ε2 n)%R <= ε)%R ->
  is_counter(L:=L) N c γ  -∗
  counter_tapes (L:=L) α None -∗
  ↯ ε  -∗
  state_update E E (∃ n, ↯ (ε2 n) ∗ counter_tapes (L:=L) α (Some (fin_to_nat n)));

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
  incr_counter_spec {L: counterG Σ} N E c γ1 (Q:nat->nat->iProp Σ)  :
    ↑N⊆E ->
    {{{ is_counter (L:=L) N c γ1 ∗
        (∀ α, counter_tapes (L:=L) α None -∗
         state_update (E) (E)
           (∃ n, counter_tapes (L:=L) α (Some n) ∗
            (∀ (z:nat), counter_content_auth (L:=L) γ1 z ={E∖↑N}=∗
                      counter_content_auth (L:=L) γ1 (z+n) ∗ Q z n)))
           
    }}}
      incr_counter c @ E
                                 {{{ (z n:nat), RET (#z, #n); Q z n }}}; 
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
                (λ z' n , ⌜0<=n<4⌝ ∗ ⌜z<=z'⌝ ∗
                          ↯ (ε2 n) ∗
                                 counter_content_frag (L:=L) γ1 q (z+n)%nat
                )%I
               with "[-HΦ]").
    - done.
    - iSplit; first done.
      iIntros (α) "Htape".
      iMod (counter_tapes_presample _ _ _ _ _ _ (λ x, ε2 (fin_to_nat x)) with "[//][$][$]") as "(%n & Herr & Htape)"; [try done..|].
      + rewrite SeriesC_finite_foldr/=. lra.
      + iModIntro. iFrame.
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
      by iSplit.
  Qed.
  
End lemmas.

