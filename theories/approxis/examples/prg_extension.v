(* Extension of a PRG: for any PRG extending a random between [0; N]
  to a random between [0; N+d], we can construct another PRG extending
  to [0; N+2d]. *)
From clutch.approxis Require Import approxis map prf prg list.
From clutch.approxis.examples Require Import option.
Import prg.bounds_check.
Set Default Proof Using "Type*".

Section defs.

    Lemma base_mult_inj : forall (n m n' m' p : nat),
      n < p -> n' < p -> m * p + n = m' * p + n' -> m = m' ∧ n = n'.
    Proof. intros * Hn Hn' Heq.
      pose proof (Nat.mod_unique (m * p + n) p m n) as H1.
      pose proof (Nat.mod_unique (m * p + n) p m' n') as H2.
      pose proof (Nat.div_unique (m * p + n) p m n) as H1'.
      pose proof (Nat.div_unique (m * p + n) p m' n') as H2'.
      apply H1' in Hn as Heq1'; apply H2' in Hn' as Heq2';
      apply H1 in Hn as Heq1; apply H2 in Hn' as Heq2; try lia.
    Qed.

  (*** A PRG *)
  Context `{PRG}.

  Local Opaque INR.

  Let Input := 2^card_input - 1.
  Let Extension := 2^card_extension - 1.
  Let TwiceExtension := 2^(2*card_extension) - 1.

  Definition prg_extension : val :=
    λ: "x",
      let: "r2" := prg "x" in
      let: "r1" := Fst "r2" in
      let: "r2" := Snd "r2" in
      let: "r2'" := prg "r1" in
      let: "r1'" := Fst "r2'" in
      let: "r2'" := Snd "r2'" in
      ("r1'", "r2'" * #(Extension+1) + "r2").

  Definition prg_extension_adv : val :=
    λ: "prg" <>,
      let: "r2" := "prg" #() in
      let: "r1" := Fst "r2" in
      let: "r2" := Snd "r2" in
      let: "r2'" := prg "r1" in
      let: "r1'" := Fst "r2'" in
      let: "r2'" := Snd "r2'" in
      ("r1'", "r2'" * #(Extension+1) + "r2").
  
  Definition prg_extension_interm : val :=
    λ: "l" "l'" <>,
      let: "r2" := rand("l") #Extension in
      let: "r2'" := prg (rand("l'") #Input) in
      let: "r1'" := Fst "r2'" in
      let: "r2'" := Snd "r2'" in
      ("r1'", "r2'" * #(Extension+1) + "r2").

  Definition prg_extension_interm_adv : val :=
    λ: "l" "l'" "x",
      let: "r2" := rand("l") #Extension in
      let: "r2'" := "prg" #() in
      let: "r1'" := Fst "r2'" in
      let: "r2'" := Snd "r2'" in
      ("r1'", "r2'" * #(Extension+1) + "r2").
 
  (** RandML types of the scheme. *)
  Definition TInput := TInt.
  Definition TOutput := TInt.
  Definition THybrid := (TInput → TOutput)%ty.
  Definition THybridOpt := (TInput → TOption TOutput)%ty.

  Section proofs.
    Context `{!approxisRGS Σ}.

    Theorem refines_prg_l' K e E A (l l' : expr) :
        refines E (fill K (let: "r1" := rand #Input in let: "r2" := rand(l) #Extension in ("r1", "r2"))) e A
      ⊢
        REL (fill K (prg (rand(l') #Input)%E)) << e @ E : A.
    Admitted.

    Theorem refines_prg_l K e E A (l : expr) :
        refines E (fill K (let: "r1" := rand #Input in let: "r2" := rand(l) #Extension in ("r1", "r2"))) e A
      ⊢
        REL (fill K (prg (rand #Input)%E)) << e @ E : A.
    Admitted.

    Theorem prg_sem_typed :
      ⊢ REL prg << prg : lrel_int → lrel_int * lrel_int.
    Admitted.

    Definition random_generator_tape : val :=
      (λ: "l" "card_input" "card_extension" "x",
        let: "r1" := rand ((#1 ≪ "card_input") - #1) in
        let: "r2" := rand("l") ((#1 ≪ "card_extension") - #1) in
        ("r1", "r2"))%V.

    Definition twice__extension (l : list nat) : nat := match l with
      | x1 :: x2 :: [] => x2 * (S Extension) + x1
      | _ => 0
    end.   


  Variable adv : val.

  Definition TAdv : type := ((TInput → (TUnit+ TOutput)) → TBool)%ty.
  Variable adv_typed : (∅ ⊢ₜ adv : TAdv).
  Definition q_calls := q_calls #card_input.
      

    Theorem prg_ext_is_prg (Q : nat) : ⊢
      REL PRG_real_rand #true  adv prg_scheme #Q
       << PRG_real_rand #false adv prg_scheme #Q : lrel_bool.
    Proof with rel_pures_l; rel_pures_r.
      rewrite /PRG_real_rand... rewrite /get_prg...
      rewrite /random_generator...
      rewrite /get_card_input; rewrite /get_card_extension...
      rel_bind_l (bounded_oracle.q_calls _ _ _).
      rel_bind_r (bounded_oracle.q_calls _ _ _).
      rel_apply (refines_bind _ _ _ (lrel_int → lrel_int)).
      2 : {
        admit.
      }
      rewrite /bounded_oracle.q_calls...
      rel_alloc_l cnt as "Hcnt";
      rel_alloc_r cnt' as "Hcnt'"...
      rel_apply (refines_na_alloc (∃ (q : nat),
          cnt  ↦  #q
        ∗ cnt' ↦ₛ #q
      ) (nroot.@"prg_ext")).
      iSplitL; first iExists 0; iFrame.
      iIntros "Inv".
      rel_arrow_val.
      iIntros (v1 v2) "[%x [%eq1 %eq2]]"; subst...
  Admitted.
    
  End proofs.


End defs.