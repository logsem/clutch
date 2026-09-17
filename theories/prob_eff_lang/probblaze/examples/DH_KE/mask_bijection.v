From iris.proofmode Require Import base.
From mathcomp Require all_boot ssrnat prime solvable.cyclic.
From clutch.prelude Require base.
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require valgroup mask.
From Stdlib Require Import Lia.
Set Default Proof Using "Type*".

Section sc_bijection.

  Import prime fingroup ssralg (* all_boot *) zmodp valgroup mask base stdpp_ext.
  Import GroupScope. (* For group-related notations *)
  Import GRing.Theory. (* For ring-related notations like + and * *)
  Open Scope ring_scope.
  Context `{logic.probblazeRGS Σ}.
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  #[local] Notation n := (S (S n'')).
  Context {mask_struct : @Mask (@vgG vg)}.
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

  Definition sc_coupling_nat (m : vgG) : nat -> nat := fun (k : nat) => match (decide (k < n)) with
                                                                        | left H => fin.fin_to_nat (sc_coupling_fin m (nat_to_fin H))
                                                                        | right _ => k
                                                                        end .

  Global Instance sc_coupling_nat_bij (m : vgG) : Bij (sc_coupling_nat m).
  Proof.
    split. 
    - intros x y Heq. unfold sc_coupling_nat in Heq. 
        case_decide as Hx; case_decide as Hy; last done.
        + repeat apply (inj _) in Heq. 
          apply (f_equal fin_to_nat) in Heq. 
          by rewrite !fin_to_nat_to_fin in Heq. 
        + subst. exfalso. eauto using fin_to_nat_lt.
        + subst. exfalso. eauto using fin_to_nat_lt.
      - intros k. unfold sc_coupling_nat.
        destruct (decide (k < S (S n''))%nat) as [Hk | Hk]; try (exists k; case_decide; done).
        destruct (surj (sc_coupling_fin m) (nat_to_fin Hk)) as [i Hi].
        exists (fin_to_nat i).
        case_decide as Hi'; [| pose proof (fin_to_nat_lt i); lia].
        rewrite -(fin_to_nat_to_fin _ _ Hk).
        rewrite -Hi. by rewrite nat_to_fin_to_nat.
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
    by rewrite mask_masklutive.
  Qed.
  
  (* I don't think we need this lemma *)
  (* Lemma sc_coupling_involutive (m : vgG) : Involutive eq (sc_coupling_fin m).
     Proof.
       intros x. unfold sc_coupling_fin.
       rewrite sc_coupling_mask. 
       rewrite mask_bij.
       destruct g_exp_bij as [Hg _]. apply Hg.
       apply int_of_vg_sem_inj.
       rewrite !int_sc_coupling.
       apply xor_sem_invol.
       - pose proof (int_of_vg_sem_bound m) as Hb. rewrite vgG_card in Hb. lia.
       - pose proof (int_of_vg_sem_bound (g ^+ fin.fin_to_nat x)%g) as Hb.
         rewrite vgG_card in Hb. lia.
     Qed. *)
  
  
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
