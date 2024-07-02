(** The PRP/PRF switching Lemma.

References:
- Lemma 1, Bellare and Rogaway, 2006, Code-Based Game-Playing Proofs and the Security of Triple Encryption.
- Lemma 6.7, Mike Rosulek, 2020, The Joy of Cryptography.
- Theorem 4.4, Boneh and Shoup, 2023, A Graduate Course in Applied Cryptography (Version 0.6).

Our definition deviates from Rosulek's and Boneh/Shoup in that we wrap the encryption oracle with [q_calls] to enforce the bound [Q] on the number of oracle calls, while loc. cit. rely on the assumption that the adversary runs in polynomial time in the security parameter.

     *)

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

    (* Can we give a nice *amortized* spec for relating
       [q_calls random_function] and [q_calls random_permutation] ? *)

    Theorem PRP_PRF (Q : nat) ε :
      (INR (fold_left (Nat.add) (seq 0 Q) 0%nat) / INR (S val_size))%R = ε
      →
      ↯ ε ⊢ (REL (PRP #false adv #() #Q) << (PRF #false adv #() #Q) : lrel_bool).
    Proof with (rel_pures_l ; rel_pures_r).
      iIntros (<-) "Hε".
      rewrite /PRP/PRF/prp.PRP/prf.PRF...
    Admitted.

    Theorem PRF_PRP (Q : nat) ε :
      (INR (fold_left (Nat.add) (seq 0 Q) 0%nat) / INR (S val_size))%R = ε
      →
      ↯ ε ⊢ (REL (PRF #false adv #() #Q) << (PRP #false adv #() #Q) : lrel_bool).
    Proof with (rel_pures_l ; rel_pures_r).
    Admitted.

  End proofs.

End prp_prf.
