From iris.proofmode Require Import base.
From mathcomp Require all_boot ssrnat prime solvable.cyclic.
From clutch.prelude Require base classical.
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require valgroup mask.
From Stdlib Require Import Lia.
Set Default Proof Using "Type*".

Section sc_bijection.

  Import prime fingroup ssralg (* all_boot *) zmodp valgroup mask base stdpp_ext.
  Import GroupScope. (* For group-related notations *)
  Import GRing.Theory. (* For ring-related notations like + and * *)
  Import classical.
  Open Scope ring_scope.
  Context `{logic.probblazeRGS Σ}.
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  #[local] Notation n := (S (S n'')).
  Context {mask_struct : @Mask (@vgG vg) (vgval)}.
  Context `{!Mask_struc}.

  Lemma g_log_exp (x : Fin.t n) : g_log (g ^+ fin.fin_to_nat x)%g = x.
  Proof. destruct (base.surj g_log x) as [v Hv]. by rewrite -Hv g_log_id. Qed.

  Global Instance g_exp_bij : Bij (fun (x : Fin.t n) => (g ^+ (fin.fin_to_nat x))%g).
  Proof.
    split.
    - intros a b Hab. by rewrite -(g_log_exp a) -(g_log_exp b) Hab.
    - intros v. exists (g_log v). apply g_log_id.
  Qed.

  Definition sc_coupling_fin (m : vgG) : Fin.t n -> Fin.t n := fun (k : Fin.t n) => g_log (mask_sem (g ^+ fin.fin_to_nat k)%g m).

  Global Instance sc_coupling_fin_bij (m : vgG) : Bij (sc_coupling_fin m).
  Proof.
    split. 
    - intros x y Heq. unfold sc_coupling_fin in Heq. 
      apply (base.inj _) in Heq.
      apply (base.inj (λ x, mask_sem x m)) in Heq.
      by apply (base.inj (λ x, (g ^+ fin.fin_to_nat x)%g)) in Heq.
    - unfold sc_coupling_fin.
      apply (base.compose_surj eq _ g_log); last apply bij_surj.
      apply (base.compose_surj eq _ (λ x, mask_sem x m)); first apply bij_surj.
      apply bij_surj.
  Qed.       

  Definition sc_coupling_nat (m : vgG) : nat -> nat := fun (k : nat) => if (decide (k < n)) then g_log (f_inv (λ x, mask_sem x m) (g ^+ k)%g) else k.

  Global Instance sc_coupling_nat_bij (m : vgG) : Bij (sc_coupling_nat m).
  Proof.
    split. 
    - intros x y Heq. unfold sc_coupling_nat in Heq. 
        case_decide as Hx; case_decide as Hy; last done.
        + destruct (f_inv_bij (λ x : vgG, mask_sem x m))  as [Hinj _].
          repeat apply (inj _) in Heq. 
          rewrite -(fin_to_nat_to_fin x n Hx) -(fin_to_nat_to_fin y n Hy) in Heq.
          apply (inj (λ x, (g ^+ fin.fin_to_nat x)%g)) in Heq.
          apply (f_equal fin_to_nat) in Heq. 
          by rewrite !fin_to_nat_to_fin in Heq. 
        + subst. exfalso. eauto using fin_to_nat_lt.
        + subst. exfalso. eauto using fin_to_nat_lt.
      - intros k. unfold sc_coupling_nat.
        destruct (decide (k < S (S n''))%nat) as [Hk | Hk]; try (exists k; case_decide; done).
        destruct (surj g_log (nat_to_fin Hk)) as [k1 Hk1].  
        destruct (f_inv_bij (λ x : vgG, mask_sem x m))  as [_ Hfsurj].
        destruct (surj (f_inv (λ x0, mask_sem x0 m)) k1) as [k2 Hk2].
        destruct (surj (λ x : fin n, (g ^+ x)%g) k2) as [k3 Hk3].
        exists (fin_to_nat k3). case_decide.
        + by rewrite Hk3 Hk2 Hk1 fin_to_nat_to_fin.
        + exfalso. apply H1. apply fin_to_nat_lt.  
  Qed.    

  Lemma sc_coupling_nat_bound m :  ∀ k : nat, (k < S (S n''))%nat → (sc_coupling_nat m k < S (S n''))%nat.
  Proof. 
    intros k Hlt.
    unfold sc_coupling_nat.
    case_decide; last done.
    apply fin_to_nat_lt.
  Qed. 

  Lemma sc_coupling_mask (m : vgG) (x : Fin.t n) :
    (g ^+ fin.fin_to_nat (sc_coupling_fin m x))%g = mask_sem (g ^+ fin.fin_to_nat x)%g m.
  Proof.
    unfold sc_coupling_fin.
    by rewrite g_log_id.
  Qed.
  
  Lemma sc_coupling_invol (m : vgG) (x : Fin.t n) :
    (g ^+ fin.fin_to_nat (sc_coupling_fin (g ^+ fin.fin_to_nat (sc_coupling_fin m x)) x))%g = m.
  Proof.
    unfold sc_coupling_fin.
    rewrite !sc_coupling_mask.
    by rewrite mask_involutive.
  Qed.
  
  Lemma sc_coupling_nat_mask (m : vgG) (x : nat) : 
    (x < n) → 
    (g ^+ x)%g = mask_sem (g ^+ (sc_coupling_nat m x))%g m.
  Proof. 
    intros Hlt.
    unfold sc_coupling_nat. case_decide; last lia.
    rewrite g_log_id.
    by rewrite (f_inv_cancel_r (λ x, mask_sem x m)).
  Qed. 

  Lemma sc_coupling_nat_invol (m : vgG) (x : nat) :
    (x < n) →
    m = mask_sem (g ^+ (sc_coupling_nat m x))%g (g ^+ x)%g.
  Proof. 
    intros Hlt.
    unfold sc_coupling_nat.
    case_decide; last lia.
    rewrite g_log_id.
    rewrite (sc_coupling_nat_mask m); last done.
    rewrite (f_inv_cancel_l (λ x, mask_sem x m)).
    by rewrite mask_involutive.
  Qed. 
  
  (* [g_log_exp] for a nat exponent.  Needed where the index is a [nat]
     carrying a separate bound rather than a [Fin.t n] -- e.g. proofs that go
     through [brel_couple_rand_rand], which wants [Bij nat nat]. *)
  Lemma g_log_exp_bounded (x : nat) (Hx : (x < S (S n''))%nat) :
    g_log (g ^+ x)%g = fin.nat_to_fin Hx.
  Proof.
    apply (base.inj fin.fin_to_nat).
    rewrite fin.fin_to_nat_to_fin.
    rewrite -(fin.fin_to_nat_to_fin _ _ Hx) g_log_exp.
    reflexivity.
  Qed.

End sc_bijection.
