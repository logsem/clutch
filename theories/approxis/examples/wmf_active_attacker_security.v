From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From clutch.approxis Require Import map reltac2 approxis option.
From clutch.approxis.examples Require Import
  security_aux option symmetric_init wmf_protocol
  pubkey advantage_laws iterable_expression.
From mathcomp Require Import ssrbool.
Set Default Proof Using "All".
Import map.

Section logrel.

  Context `{!approxisRGS Σ}.

  (* security parameter *)
  Variable η : nat.

  Let N := 2^η.

  Variable Key Output : nat.

  (* ASSUMPTION ON THE ENCRYPTION SCHEME *)

  Definition left_lrel (τ : lrel Σ) (v : val) : iProp Σ := ∃ v', (lrel_car τ) v v'.
  Definition right_lrel (τ : lrel Σ) (v : val) : iProp Σ := ∃ v', (lrel_car τ) v' v.

  Definition lrel_id : lrel Σ := lrel_int_bounded 0 1.

  Definition lrel_input : lrel Σ := lrel_int_bounded 0 N * lrel_int_bounded 0 N.
  Definition lrel_rand : lrel Σ := lrel_int_bounded 0 N.
  Variable lrel_output : lrel Σ.
  Variable lrel_key : lrel Σ.

  Variable senc : list loc → val.
  Variable sdec : list loc → val.

  Variable P0l : list loc → iProp Σ.
  Variable P0r : list loc → iProp Σ.

  Variable Pl : list loc → iProp Σ.
  Variable Pr : list loc → iProp Σ.
  Variable Plr : list loc → list loc → iProp Σ.

  Definition P0_P_l_prop := ∀ lls, P0l lls -∗ Pl lls.
  Definition P0_P_r_prop := ∀ rls, P0r rls -∗ Pr rls.
  Definition P0lr_Plr_prop := ∀ lls rls, P0l lls -∗ P0r rls -∗ Plr lls rls.
  Hypothesis P0_P_l : P0_P_l_prop.
  Hypothesis P0_P_r : P0_P_r_prop.
  Hypothesis P0lr_Plr : P0lr_Plr_prop.
  
  #[local] Instance sym_params : SYM_init_params := @sym_params_wmf η Key Output.

  Context `{sym : !SYM_init}.

  Let init_scheme : expr → expr := init_scheme η Key Output.

  Let CPA' : val := CPA' η Key Output.

  Definition refines_init_scheme_l_prop := forall K e E A,
    (∀ lls,
      P0l lls -∗
      refines E
        (fill K (senc lls, sdec lls))
        e A)
    ⊢ refines E
        (fill K (get_enc_scheme sym_scheme #()))
        e A.

  Definition refines_init_scheme_r_prop := forall K e E A,
    (∀ rls,
      P0r rls -∗
      refines E
        e
        (fill K (senc rls, sdec rls))
        A)
    ⊢ refines E
        e
        (fill K (get_enc_scheme sym_scheme #()))
        A.

  Hypothesis refines_init_scheme_l : refines_init_scheme_l_prop.

  Hypothesis refines_init_scheme_r : refines_init_scheme_r_prop.

  Definition refines_sym_keygen_couple_prop := forall K K' E A,
    (∀ key,
      (lrel_car lrel_key) key key -∗
        refines E
          (fill K  (Val key))
          (fill K' (Val key))
          A)
    ⊢ refines E
        (fill K  (keygen #()))
        (fill K' (keygen #()))
        A.
  Hypothesis refines_sym_keygen_couple : refines_sym_keygen_couple_prop.

  Definition refines_keygen_l_prop := forall K e E A,
    (∀ key,
      left_lrel lrel_key key -∗
      refines E
        (fill K (Val key))
        e A)
    ⊢ refines E
        (fill K (symmetric_init.keygen #()))
        e A.
  Definition refines_keygen_r_prop := forall K e E A,
    (∀ key,
      right_lrel lrel_key key -∗
      refines E
        e
        (fill K (Val key))
        A)
    ⊢ refines E
        e
        (fill K (symmetric_init.keygen #()))
        A.
  Hypothesis refines_keygen_l : refines_keygen_l_prop.
  Hypothesis refines_keygen_r : refines_keygen_r_prop.

  Definition sym_is_cipher_lr_l {lls rls : list loc} (msg : val) (c k : val) : iProp Σ :=
    ∀ K e E A,
      (Plr lls rls -∗
        refines E
        (fill K (Val msg))
        e A)
    -∗ refines E
        (fill K (sdec lls k c))
        e A.
  
  Definition sym_is_cipher_lr_r {lls rls : list loc} (msg : val) (c k : val) : iProp Σ :=
    ∀ K e E A,
      (Plr lls rls -∗
        refines E
        e (fill K (Val msg)) A)
    -∗ refines E
        e (fill K (sdec rls k c)) A.

  Definition refines_senc_lr_l_prop :=
    ∀ (lls rls : list loc) (msg msg' : val) (k k' : val) K K' E A,
    lrel_key k k' ∗ lrel_input msg msg' ∗ Plr lls rls ⊢
      ((∀ (c c' : val),
        lrel_output c c'
      -∗ @sym_is_cipher_lr_l lls rls msg c k
      -∗ refines E
          (fill K (Val c))
          (fill K' (Val c'))
          A)
    -∗ refines E
        (fill K  (senc lls k  msg ))
        (fill K' (senc rls k' msg'))
        A).
      
  Definition refines_senc_lr_r_prop :=
    ∀ (lls rls : list loc) (msg msg' : val) (k k' : val) K K' E A,
    lrel_key k k' ∗ lrel_input msg msg' ∗ Plr lls rls ⊢
      ((∀ (c c' : val),
        lrel_output c c'
      -∗ @sym_is_cipher_lr_r lls rls msg c' k
      -∗ refines E
          (fill K (Val c))
          (fill K' (Val c'))
          A)
    -∗ refines E
        (fill K  (senc lls k  msg ))
        (fill K' (senc rls k' msg'))
        A).

  Hypothesis refines_couple_senc_lr_l : refines_senc_lr_l_prop.

  Hypothesis refines_couple_senc_lr_r : refines_senc_lr_r_prop.

  Definition senc_sem_typed_prop :=
    ∀ lls rls (𝒩 : namespace) (P : iProp Σ),
    (∃ (Q : iProp Σ),
      P ⊣⊢
        (Q
      ∗ Plr lls rls)
    ) →
    na_invP 𝒩 P
      ⊢ refines top (senc lls)
      (senc rls) (lrel_key → lrel_input → lrel_output).

  Hypothesis senc_sem_typed : senc_sem_typed_prop.

End logrel.