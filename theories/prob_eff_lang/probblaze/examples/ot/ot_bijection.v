From Coquelicot Require Import Rcomplements.
From clutch.clutch Require ElGamal_bijection.
From mathcomp Require all_boot ssrnat prime solvable.cyclic.
From clutch.prelude Require base stdpp_ext.
From clutch.prob_eff_lang.probblaze Require valgroup.
From Stdlib Require Import Lia.
Set Default Proof Using "Type*".

Section Fp_fin.

  Import prime fingroup ssralg all_boot zmodp.
  Import GroupScope. (* For group-related notations *)
  Import GRing.Theory. (* For ring-related notations like + and * *)
  Open Scope ring_scope.
  Context {n'' : nat}.
  #[local] Notation n := n''.+2.
  Context `{n_prime : prime n}.

  Definition Fp_of_fin (c : Fin.t n) : 'F_n := GRing.one 'F_n *+ (fin.fin_to_nat c).

End Fp_fin.
  
Section crs_bij_cancel.

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
  
  Lemma crs_bij_cancel x :
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

End crs_bij_cancel.

Section crs_bijection.

  Import prime div base stdpp_ext. 
  
  Variable n'' : nat.
  #[local] Notation n := (S (S n'')).
  Variable (k : nat).
   
  (* k should be less than S n for this to be a bijection *)
  Definition f : nat -> nat := λ x, if x <? n then
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
    rewrite crs_bij_cancel.
    - apply modn_small. apply Rcomplements.SSR_leq.
      apply Nat.ltb_lt in Hx. lia.
    - done.
    - apply Rcomplements.SSR_leq. lia.
    - apply Rcomplements.SSR_leq. lia.
  Qed
  .

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
    rewrite crs_bij_cancel.
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
  
End crs_bijection.

Section crs_bijection_Fp.
  
  Import prime zmodp fingroup ssralg all_boot stdpp_ext.
  Import GroupScope. (* For group-related notations *)
  Import GRing.Theory. (* For ring-related notations like + and * *)
  Open Scope ring_scope.
  Context {n'' : nat}.
  #[local] Notation n := n''.+2.
  Context `{n_prime : prime n}.
  Variable (k : 'F_n).

   (* k should be less than S n for this to be a bijection *)
  Definition f_ring (x : nat) : nat := if x < n then
                                         val ((inZp x)  * k ^-1)
                                       else
                                         x.

  Definition h_ring (x : nat) : nat := if x < n then
                                        val (k * inZp x)
                                       else x.

  Lemma f_lt_ring :
    forall x : nat, x < n -> (f_ring x) < n.
  Proof.
    intros x Hx.
    unfold f_ring. rewrite Hx.
    simpl. rewrite {3}Fp_cast //.
    rewrite ltn_pmod //.
  Qed. 

  Context {Hnz : k != 0}.

  Lemma f_h_cancel_ring x : f_ring (h_ring x) = x. 
  Proof.
    destruct (x < n) eqn:Hx; rewrite /f_ring /h_ring !Hx //.
    assert (\val (_ * (inZp x)) < n) as ->.
    { simpl. rewrite {3}Fp_cast //. rewrite ltn_pmod //. }
    rewrite valZpK.
    rewrite (mulrC k).
    rewrite -mulrA. 
    rewrite mulfV //.
    rewrite mulr1.
    simpl. rewrite modn_small //.
    rewrite pdiv_id //.
  Qed. 

  Lemma h_f_cancel_ring x : h_ring  (f_ring x) = x.
  Proof.
    destruct (x < n) eqn:Hx; rewrite /f_ring /h_ring !Hx //.
    assert (\val ((inZp x) / k) < n) as ->.
    { simpl. rewrite {3}Fp_cast //. rewrite ltn_pmod //. }
    rewrite valZpK.
    rewrite mulrA.
    rewrite (mulrC k).
    rewrite -mulrA.
    rewrite mulfV //.
    rewrite mulr1.
    simpl. rewrite modn_small //.
    rewrite pdiv_id //.
  Qed. 

  #[export] Instance f_inj_ring : base.Inj eq eq f_ring.
  Proof. intros x y hf. rewrite -(h_f_cancel_ring x) -(h_f_cancel_ring y) hf => //. Qed.

  #[export] Instance f_surj_ring : base.Surj eq f_ring.
  Proof. intros x. exists (h_ring x). by rewrite f_h_cancel_ring. Qed.

  #[export] Instance f_bij_ring : Bij f_ring | 1.
  Proof. constructor; apply _. Qed.

  #[export] Instance h_inj_ring : base.Inj eq eq h_ring.
  Proof. intros x y hh. rewrite -(f_h_cancel_ring x) -(f_h_cancel_ring y) hh => //. Qed.

  #[export] Instance h_surj_ring : base.Surj eq h_ring.
  Proof. intros x. exists (f_ring x). by rewrite h_f_cancel_ring. Qed.

  #[export] Instance h_bij_ring : Bij h_ring | 1.
  Proof. constructor; apply _. Qed.

  Lemma crs_bij_ring_cancel x :
    k * (x * k ^-1) = x.
  Proof.
    rewrite mulrA.
    rewrite mulrC mulrA.
    rewrite mulVf //.
    by rewrite mul1r.
  Qed. 

End crs_bijection_Fp.

Section crs_fin_cancel.

  Import prime fingroup ssralg all_boot zmodp valgroup.
  Import GroupScope. (* For group-related notations *)
  Import GRing.Theory. (* For ring-related notations like + and * *)
  Open Scope ring_scope.
  Context {n'' : nat}.
  #[local] Notation n := n''.+2.
  Context {n_prime : prime n}.

  Lemma crs_fin_cancel (g0 : Fin.t n) (t0 : nat) :
    Fp_of_fin g0 != 0 ->
    t0 < n ->
    ((fin.fin_to_nat g0 * (f_ring (Fp_of_fin g0) t0))) = t0  %[mod n].
  Proof.
    intros Hnz Hlt.
    unfold f_ring. rewrite Hlt.
    rewrite -val_Fp_nat //.
    rewrite natrM. rewrite natr_Zp.
    rewrite crs_bij_ring_cancel //.
    rewrite Fp_Zcast //.
  Qed.

End crs_fin_cancel.
  
Section enc_bijection.

  Import prime zmodp fingroup ssralg all_boot stdpp_ext.
  Import GroupScope. (* For group-related notations *)
  Import GRing.Theory. (* For ring-related notations like + and * *)
  Open Scope ring_scope.
  Context {n'' : nat}.
  #[local] Notation n := n''.+2.
  Context {n_prime : prime n}.
  Variable (k : 'F_n).

  Definition minus_ring (x : nat) : nat := if x < n then
                                          val (inZp x - k)
                                        else
                                          x.

  Definition plus_ring (x : nat) : nat := if x < n then
                                          val (inZp x + k)
                                        else
                                          x.

  Lemma minus_ring_lt :
    forall x : nat, x < n -> (minus_ring x) < n.
  Proof.
    intros x Hx.
    unfold minus_ring. rewrite Hx.
    simpl.
    rewrite {5}Fp_cast //.
    rewrite ltn_pmod //.
  Qed.

  Lemma plus_ring_lt :
    forall x : nat, x < n -> (plus_ring x) < n.
  Proof.
    intros x Hx.
    unfold plus_ring. rewrite Hx.
    simpl.
    rewrite {3}Fp_cast //.
    rewrite ltn_pmod //.
  Qed. 

  Lemma minus_plus_ring_cancel x : minus_ring (plus_ring x) = x. 
  Proof.
    destruct (x < n) eqn:Hx; rewrite /minus_ring /plus_ring !Hx //.
    assert (\val ((inZp x) + k) < n) as ->.
    { simpl. rewrite {3}Fp_cast //. rewrite ltn_pmod //. }
    rewrite valZpK.
    rewrite addrK.
    simpl. rewrite modn_small //.
    rewrite pdiv_id //.
  Qed. 

  Lemma plus_minus_ring_cancel x : plus_ring (minus_ring x) = x.
  Proof.
    destruct (x < n) eqn:Hx; rewrite /minus_ring /plus_ring !Hx //.
    assert (\val ((inZp x) - k) < n) as ->.
    { simpl. rewrite {5}Fp_cast //. rewrite ltn_pmod //. }
    rewrite valZpK.
    rewrite -addrA.
    rewrite addrC.
    rewrite -addrA.
    rewrite addKr.
    simpl. rewrite modn_small //.
    rewrite pdiv_id //.
  Qed. 
  
   #[export] Instance minus_ring_inj : base.Inj eq eq minus_ring.
  Proof. intros x y hf. rewrite -(plus_minus_ring_cancel x) -(plus_minus_ring_cancel y) hf => //. Qed.

  #[export] Instance minus_ring_surj : base.Surj eq minus_ring.
  Proof. intros x. exists (plus_ring x). by rewrite minus_plus_ring_cancel. Qed.

  #[export] Instance minus_ring_bij : Bij minus_ring | 1.
  Proof. constructor; apply _. Qed.

  #[export] Instance plus_ring_inj : base.Inj eq eq plus_ring.
  Proof. intros x y hh. rewrite -(minus_plus_ring_cancel x) -(minus_plus_ring_cancel y) hh => //. Qed.

  #[export] Instance plus_surj_ring : base.Surj eq plus_ring.
  Proof. intros x. exists (minus_ring x). by rewrite plus_minus_ring_cancel. Qed.

  #[export] Instance plus_bij_ring : Bij plus_ring | 1.
  Proof. constructor; apply _. Qed.

End enc_bijection.


Section enc_bij_cancel.

  Import prime zmodp fingroup ssralg all_boot.
  Import GroupScope. (* For group-related notations *)
  Import GRing.Theory. (* For ring-related notations like + and * *)
  Open Scope ring_scope.
  Context {n'' : nat}.
  #[local] Notation n := (S (S n'')).
  Context {n_prime : prime n}.
  (* Variable (t g km ku kv : nat).
     Import prime div ssrnat all_boot cyclic ElGamal_bijection.bij_nat.
     
     Definition c1 := (t * ((km - 1) * (((g * kv) - (t * ku)) ^ n'')))%% n.
     Definition c2 := (g * ((km -1) * (((g * kv) - (t * ku)) ^ n'')))%% n.
     
     Fact fin_c1 : (c1 < n)%coq_nat.
     Proof. apply div_modn_lt. lia. Qed.
     
     Fact fin_c2 : (c2 < n)%coq_nat.
     Proof. apply div_modn_lt. lia. Qed.
     
     Lemma enc_bij_cancel1 r s :
       (g * ((n - c1 + r) %% n)) + (t * ((c2 + s) %% n)) = (g * r) + (t * s) %[mod n].
     Proof.
       rewrite -modnDm.
       rewrite !modnMmr.
       rewrite !mulnDr.
       rewrite -(modnDml (t * c2)).
       assert (g * c1 = t * c2 %[mod n]) as <-.
       { unfold c1, c2. rewrite !modnMmr. rewrite !mulnA. by rewrite (mulnC g t). }
       rewrite (modnDml (g * c1)).
       rewrite mulnBr.
       rewrite modnDm.
       rewrite addnA.
       rewrite (addnC _ (g * r)).
       rewrite -(addnA _ _ (g * c1)).
       rewrite subnK.
       2 : { apply leq_mul; first done. apply ltnW. by apply ltn_pmod. }
       rewrite addnC.
       rewrite addnA.
       rewrite -modnDmr.
       rewrite modnMl.
       rewrite addn0.
       by rewrite addnC.
     Qed. *)


  Variable (t' g' km' ku' kv' : 'F_n).  
  Definition c1' := (t' * ((km' - Zp1) * (((g' * kv') - (t' * ku')) ^-1))).
  Definition c2' := (g' * ((km' - Zp1) * (((g' * kv') - (t' * ku')) ^-1))).

  Lemma enc_bij_cancel1' r s :
    (g' * (r - c1')) + (t' * (c2' + s)) = (g' * r) + (t' * s).
  Proof.
    rewrite mulrBr.
    rewrite mulrDr.
    rewrite addrA.
    rewrite addrC.
    unfold c1', c2'.
    rewrite !mulrA.
    rewrite (mulrC g' t').
    rewrite addrNK.
    by rewrite addrC.
  Qed. 
    
  Lemma sub_reduction :
    (g' * kv') - (t' * ku') != Zp0 ->
     kv' * c2' - ku' * c1' = km' - Zp1. 
  Proof.
    intros Hneq.
    rewrite !mulrA.
    rewrite (mulrC ku') (mulrC kv').
    do 2 rewrite -mulrA.
    rewrite -mulrBl.
    rewrite mulrA.
    rewrite -(mulrC (km' - Zp1)).
    rewrite -mulrA.
    by rewrite mulfV // mulr1.
  Qed.

  Lemma enc_bij_cancel2 (r s : 'F_n) :
    (g' * kv') - (t' * ku') != Zp0 ->
    Zp1 + ku' * (r - c1') + kv' * (c2' + s) = km' + ku' * r + kv' * s.
  Proof.
    intros Hneq.
    rewrite mulrBr.
    rewrite mulrDr.
    do 2 rewrite addrA.
    rewrite -(addrA _ _ (kv' * c2')).
    rewrite (addrC _ (kv' * c2')).
    rewrite sub_reduction //.
    rewrite (addrC _ (km' - Zp1)).
    rewrite addrA. 
    by rewrite addrNK.  
  Qed. 
  
End enc_bij_cancel.

Section enc_fin_cancel.

  Import prime fingroup ssralg all_boot zmodp valgroup.
  Import GroupScope. (* For group-related notations *)
  Import GRing.Theory. (* For ring-related notations like + and * *)
  Open Scope ring_scope.
  Context {n'' : nat}.
  #[local] Notation n := n''.+2.
  Context {n_prime : prime n}.
  Variable (t : nat).
  Variable (g km ku kv : Fin.t n).

  Definition c1 : 'F_n := c1' (inZp t) (Fp_of_fin g) (Fp_of_fin km) (Fp_of_fin ku) (Fp_of_fin kv).
  Definition c2 := c2' (inZp t) (Fp_of_fin g) (Fp_of_fin km) (Fp_of_fin ku) (Fp_of_fin kv).

  Lemma enc_fin_cancel1 (r s : nat) :
    r < n ->
    s < n ->
    (fin.fin_to_nat g) * (minus_ring c1 r) +  t * (plus_ring c2 s) = (fin.fin_to_nat g) * r + t * s %[mod n].
  Proof.
    intros Hltr Hlts.
    unfold minus_ring, plus_ring. rewrite Hltr Hlts.
    rewrite -modnDm.
    rewrite -!val_Fp_nat //.
    rewrite -finalg.FinRing.val_unit1.
    rewrite !natrM. rewrite -finalg.FinRing.val_unit1.
    rewrite natrD. rewrite -finalg.FinRing.val_unit1. rewrite !natr_Zp.
    rewrite (addrC _ c2).
    rewrite (Zp_nat _ t).
    rewrite enc_bij_cancel1' //.
    rewrite natrD. rewrite !natrM.
    rewrite -finalg.FinRing.val_unit1.
    rewrite (Zp_nat _ r).
    rewrite (Zp_nat _ s).
    rewrite (Zp_nat _ t).
    done.
  Qed.

  Lemma enc_fin_cancel2 (r s : nat) :
    Fp_of_fin g * Fp_of_fin kv - inZp t * Fp_of_fin ku != Zp0 ->
    r < n ->
    s < n ->
    1%nat + (fin.fin_to_nat ku * (minus_ring c1 r)) + (fin.fin_to_nat kv * (plus_ring c2 s)) = (fin.fin_to_nat km) + (fin.fin_to_nat ku) * r + (fin.fin_to_nat kv) * s %[mod n].
  Proof.
    intros Hnz Hltr Hlts.
    unfold minus_ring, plus_ring. rewrite Hltr Hlts.
    rewrite -modnDm.
    rewrite -!val_Fp_nat //.
    rewrite -finalg.FinRing.val_unit1.
    rewrite !natrD.
    rewrite -finalg.FinRing.val_unit1.
    rewrite !natrM.
    rewrite -finalg.FinRing.val_unit1.
    rewrite Zp_nat.
    rewrite valZpK.
    rewrite !natr_Zp.
    rewrite Zp_mulrn.
    rewrite muln1.
    rewrite valZpK.
    rewrite (addrC _ c2).
    rewrite enc_bij_cancel2 //.
    rewrite (Zp_nat _ r).
    rewrite (Zp_nat _ s).
    done.
  Qed.    
    
End enc_fin_cancel.
