From Coquelicot Require Import Rcomplements.
From mathcomp Require all_boot ssrnat prime solvable.cyclic.
From clutch.prelude Require base stdpp_ext.
From Stdlib Require Import Lia.
Set Default Proof Using "Type*".

Section bij_cancel.

  Import prime div ssrnat all_boot cyclic.
  
  Variable n'' : nat.
  #[local] Notation n := (S (S n'')).
  Context {n_prime : prime n}.
  Variable (k : nat).
  Context `{Hpos : 0 < k, Hlt: k < n}.

  Lemma prime_lt_coprime :
    coprime k n .
  Proof.
    rewrite coprime_sym.
    rewrite prime_coprime; last done.
    apply/negP. intros Hdiv.
    apply dvdn_leq in Hdiv.
    - move/ltP: Hlt => Hlt_prop. 
      move/ltP: Hdiv => Hdiv_prop.
      lia.
    - done.
  Qed.
  
  Lemma bij_cancel x :
    k * ((x * k ^n'') %% n) = x %[mod n].
  Proof.
    rewrite modnMmr.
    rewrite mulnA.
    rewrite (mulnC k x).
    rewrite -mulnA.
    rewrite -expnS.
    rewrite -modnMm.
    assert (totient n = n''.+1) as Htot by (apply totient_prime; done).
    rewrite -{2}Htot.
    rewrite Euler_exp_totient; last apply prime_lt_coprime. 
    rewrite modnMm. by rewrite muln1.
  Qed. 

End bij_cancel.

Section ot_bijection.

  Import prime div base stdpp_ext. 
  
  Variable n'' : nat.
  #[local] Notation n := (S (S n'')).
  Variable (k : nat).
   
  (* k should be less than S n for this to be a bijection *)
  Definition f := λ x, if x <? n then
                                   (modn (ssrnat.muln x (ssrnat.expn k n'')) n)%nat
                       else x.

  Definition h := λ x, if x <? n then
                         modn (ssrnat.muln k x) n
                       else x.
  
  Lemma f_lt :
    ∀ x : nat, x < n → f x < n.
  Proof.
    intros x Hx. unfold f.
    rewrite -Nat.ltb_lt in Hx.
    rewrite Hx. 
    apply Rcomplements.SSR_leq.
    apply ltn_pmod. done.
  Qed.

  Context {n_prime : is_true (prime n)}.
  Context `{Hpos : 0 < k, Hlt: k < n}.
 
  Lemma f_h_cancel x : f (h x) = x. 
  Proof.
    destruct (x <? n) eqn:Hx; rewrite /f /h !Hx //.
    set (hx := ssrnat.muln k x %% n).
    destruct (hx <? n) eqn:Hhx.
    2:{ apply Nat.ltb_nlt in Hhx.
        exfalso. apply Hhx.
        apply ->Nat.le_succ_l.
        rewrite -Rcomplements.SSR_leq.
        apply ltn_pmod. done. }
    subst hx.
    rewrite modnMml.
    rewrite -ssrnat.mulnA.
    rewrite -modnMmr.
    rewrite bij_cancel.
    - apply modn_small. apply Rcomplements.SSR_leq.
      apply Nat.ltb_lt in Hx. lia.
    - done.
    - apply Rcomplements.SSR_leq. lia.
    - apply Rcomplements.SSR_leq. lia.
  Qed.

  Lemma h_f_cancel x : h (f x) = x.
  Proof.
    destruct (x <? n) eqn:Hx; rewrite /f /h !Hx //.
    set (fx := ssrnat.muln x (ssrnat.expn k n'') %% n).
    destruct (fx <? n) eqn:Hfx.
    2:{ apply Nat.ltb_nlt in Hfx.
        exfalso. apply Hfx.
        apply ->Nat.le_succ_l.
        rewrite -Rcomplements.SSR_leq.
        apply ltn_pmod. done. }
    subst fx.
    rewrite bij_cancel.
    - apply modn_small. apply Rcomplements.SSR_leq.
      apply Nat.ltb_lt in Hx. lia.
    - done.
    - apply Rcomplements.SSR_leq. lia.
    - apply Rcomplements.SSR_leq. lia.
  Qed.

  #[export] Instance f_inj : base.Inj eq eq f.
  Proof. intros x y hf. rewrite -(h_f_cancel x) -(h_f_cancel y) hf => //. Qed.

  #[export] Instance f_surj : base.Surj eq f.
  Proof. intros x. exists (h x). by rewrite f_h_cancel. Qed.

  #[export] Instance f_bij : Bij f | 1.
  Proof. constructor; apply _. Qed.

  #[export] Instance h_inj : base.Inj eq eq h.
  Proof. intros x y hh. rewrite -(f_h_cancel x) -(f_h_cancel y) hh => //. Qed.

  #[export] Instance h_surj : base.Surj eq h.
  Proof. intros x. exists (f x). by rewrite h_f_cancel. Qed.

  #[export] Instance h_bij : Bij h | 1.
  Proof. constructor; apply _. Qed.
  
End ot_bijection. 


