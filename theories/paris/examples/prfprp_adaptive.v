From clutch Require Import lib.flip.
From clutch.paris Require Import paris map list prf prp examples.prf_cpa.
Set Default Proof Using "Type*".

Section prp_prf.

  Variable Key : nat.
  Variable val_size : nat.
  Let Input := val_size.
  Let Output := val_size.

  (** RandML types of the scheme. *)
  Definition TKey := TInt.
  Definition TInput := TInt.
  Definition TOutput := TInt.

  (** We will prove the PRF/PRP switching lemma.
      We assume that the adversaries are well-typed. *)
  Variable adv : val.
  Definition TAdv := ((TInput → TOutput) → TBool)%ty.
  Variable adv_typed : (∅ ⊢ₜ adv : TAdv).
  Definition q_calls := q_calls Input.
  Definition PRF := PRF val_size val_size.
  Definition PRP := PRP val_size.
  (* Definition PRP_PRF : val := λ:"b" "adv",
         if: "b" then PRP #false "adv" #() else PRF #false "adv" #(). *)

  Local Opaque INR.

  Section proofs.
    Context `{!parisRGS Σ}.

    Theorem PRP_PRF (Q : nat) ε :
      (INR (fold_left (Nat.add) (seq 0 Q) 0%nat) / INR (S val_size))%R = ε
      →
      ↯ ε ⊢ (REL (PRP #false adv #() #Q) << (PRF #false adv #() #Q) : lrel_bool).
    Proof with (rel_pures_l ; rel_pures_r).
    Admitted.

    Theorem PRF_PRP (Q : nat) ε :
      (INR (fold_left (Nat.add) (seq 0 Q) 0%nat) / INR (S val_size))%R = ε
      →
      ↯ ε ⊢ (REL (PRF #false adv #() #Q) << (PRP #false adv #() #Q) : lrel_bool).
    Proof with (rel_pures_l ; rel_pures_r).
    Admitted.

  End proofs.

End prp_prf.
