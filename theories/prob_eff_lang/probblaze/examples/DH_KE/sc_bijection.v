From Coquelicot Require Import Rcomplements.
From mathcomp Require all_boot ssrnat prime solvable.cyclic.
From clutch.prelude Require base stdpp_ext.
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require valgroup xor.
From clutch.prob_eff_lang.probblaze Require logic.
From Stdlib Require Import Lia.
Set Default Proof Using "Type*".

Section sc_bijection.

  Import prime fingroup ssralg all_boot zmodp valgroup xor stdpp_ext.
  Import GroupScope. (* For group-related notations *)
  Import GRing.Theory. (* For ring-related notations like + and * *)
  Open Scope ring_scope.
  (* Context {n'' : nat}. *)
  Context `{logic.probblazeRGS Σ}.
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  #[local] Notation n := n''.+2.
  Context {xor_struct : XOR (Key := (S n'')) (Support := (S n''))}.
  Context `{!XOR_spec (Key := (S n'')) (Support := (S n'')) (H := xor_struct)}.


  (* Lemma xor_bij (m : nat) : @Bij vgG  (fun (x : vgG) => xor_sem m (int_of_vg_sem x)).
     Proof.
       split; intros x.


       apply xor_bij. *)

  Lemma g_log_exp (x : Fin.t n) : g_log (g ^+ fin.fin_to_nat x)%g = x.
  Proof. destruct (base.surj g_log x) as [v Hv]. by rewrite -Hv g_log_id. Qed.

  Lemma g_exp_bij : Bij (fun (x : Fin.t n) => (g ^+ (fin.fin_to_nat x))%g).
  Proof.
    split.
    - intros a b Hab. by rewrite -(g_log_exp a) -(g_log_exp b) Hab.
    - intros v. exists (g_log v). apply g_log_id.
  Qed.

  Definition sc_coupling (m : vgG) : Fin.t n -> Fin.t n := fun (x : Fin.t n) =>
                                                             let xn := vg_of_int_sem (xor_sem (int_of_vg_sem m) (int_of_vg_sem (g ^+ fin.fin_to_nat x))) in
                                                             match xn with
                                                             | None => x
                                                             | Some xn => g_log xn
                                                             end.

  Global Instance sc_coupling_bij (m : vgG) : Bij (sc_coupling m).
  Proof.
    assert (Hm : (int_of_vg_sem m < S (S n''))%coq_nat).
    { pose proof (int_of_vg_sem_bound m) as Hb. rewrite vgG_card in Hb. lia. }
    destruct (xor_bij (int_of_vg_sem m)) as [Hxinj _].
    (* codes, xor support and Fin.t n all have size n''.+2, so None is dead *)
    assert (Hdec : forall x : Fin.t n, exists h,
       vg_of_int_sem (xor_sem (int_of_vg_sem m) (int_of_vg_sem (g ^+ fin.fin_to_nat x)%g)) = Some h
       /\ int_of_vg_sem h = xor_sem (int_of_vg_sem m) (int_of_vg_sem (g ^+ fin.fin_to_nat x)%g)).
    { intros x.
      pose proof (int_of_vg_sem_bound (g ^+ fin.fin_to_nat x)%g) as Hh.
      rewrite vgG_card in Hh.
      assert (Hin : (int_of_vg_sem (g ^+ fin.fin_to_nat x)%g < S (S n''))%coq_nat) by lia.
      pose proof (xor_dom _ Hm _ Hin).
      apply vg_of_int_sem_surj; rewrite ?vgG_card; lia. }
    assert (Hinj : base.Inj eq eq (sc_coupling m)).
    { intros x y Heq.
      destruct (Hdec x) as [hx [Hsx Hix]]. destruct (Hdec y) as [hy [Hsy Hiy]].
      rewrite /sc_coupling in Heq. cbv zeta in Heq. rewrite Hsx Hsy in Heq.
      apply (base.inj g_log) in Heq. subst hy. rewrite Hix in Hiy.
      apply Hxinj in Hiy.
      destruct g_exp_bij as [Hg _]. apply Hg. apply int_of_vg_sem_inj. exact Hiy. }
    (* an injective endo-map of a finite type is surjective *)
    split; [exact Hinj |].
    apply (@finite.finite_inj_surj _ _ _ _ _ _ (sc_coupling m) Hinj). reflexivity.
  Qed.

  (* [sc_coupling] read at the level of codes: it *is* the xor. *)
  Lemma int_sc_coupling (m : vgG) (x : Fin.t n) :
    int_of_vg_sem (g ^+ fin.fin_to_nat (sc_coupling m x))%g
    = xor_sem (int_of_vg_sem m) (int_of_vg_sem (g ^+ fin.fin_to_nat x)%g).
  Proof.
    assert (Hm : (int_of_vg_sem m < S (S n''))%coq_nat).
    { pose proof (int_of_vg_sem_bound m) as Hb. rewrite vgG_card in Hb. lia. }
    assert (Hx : (int_of_vg_sem (g ^+ fin.fin_to_nat x)%g < S (S n''))%coq_nat).
    { pose proof (int_of_vg_sem_bound (g ^+ fin.fin_to_nat x)%g) as Hb.
      rewrite vgG_card in Hb. lia. }
    pose proof (xor_dom _ Hm _ Hx) as Hw.
    assert (Hsurj : exists h,
      vg_of_int_sem (xor_sem (int_of_vg_sem m) (int_of_vg_sem (g ^+ fin.fin_to_nat x)%g)) = Some h
      /\ int_of_vg_sem h = xor_sem (int_of_vg_sem m) (int_of_vg_sem (g ^+ fin.fin_to_nat x)%g)).
    { apply vg_of_int_sem_surj. rewrite vgG_card. lia. }
    destruct Hsurj as [h [Hsome Hint]].
    rewrite /sc_coupling. cbv zeta. rewrite Hsome g_log_id. exact Hint.
  Qed.

  (* Decrypt-after-encrypt.  This is what [Bij_xor_sem] used to assume; it
     follows from [xor_sem_inverse_r], already a field of [XOR_spec]. *)
  Lemma sc_coupling_invol (m : vgG) (x : Fin.t n) :
    (g ^+ fin.fin_to_nat (sc_coupling (g ^+ fin.fin_to_nat (sc_coupling m x)) x))%g = m.
  Proof.
    apply int_of_vg_sem_inj.
    rewrite !int_sc_coupling.
    apply xor_sem_inverse_r.
    - pose proof (int_of_vg_sem_bound m) as Hb. rewrite vgG_card in Hb. lia.
    - pose proof (int_of_vg_sem_bound (g ^+ fin.fin_to_nat x)%g) as Hb.
      rewrite vgG_card in Hb. lia.
  Qed.

  (* Applying the coupling twice with the *same* key is the identity.  Note the
     contrast with [sc_coupling_invol] above, where the key slot is what varies
     (the ciphertext becomes the key); that one follows from
     [xor_sem_inverse_r], this one needs [xor_sem_invol]. *)
  Lemma sc_coupling_involutive (m : vgG) : involutive (sc_coupling m).
  Proof.
    intros x.
    destruct g_exp_bij as [Hg _]. apply Hg.
    apply int_of_vg_sem_inj.
    rewrite !int_sc_coupling.
    apply xor_sem_invol.
    - pose proof (int_of_vg_sem_bound m) as Hb. rewrite vgG_card in Hb. lia.
    - pose proof (int_of_vg_sem_bound (g ^+ fin.fin_to_nat x)%g) as Hb.
      rewrite vgG_card in Hb. lia.
  Qed.


  (* [g_log_exp] for a nat exponent.  Needed where the index is a [nat]
     carrying a separate bound rather than a [Fin.t n] -- e.g. proofs that go
     through [brel_couple_rand_rand], which wants [Bij nat nat]. *)
  Lemma g_log_exp_bounded (x : nat) (Hx : (x < S (S n''))%coq_nat) :
    g_log (g ^+ x)%g = fin.nat_to_fin Hx.
  Proof.
    apply (base.inj fin.fin_to_nat).
    rewrite fin.fin_to_nat_to_fin.
    rewrite -(fin.fin_to_nat_to_fin _ _ Hx) g_log_exp.
    reflexivity.
  Qed.

End sc_bijection.
