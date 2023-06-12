(** This is a partial, unfinished port of the definition of asymmetric
    encryption schemes in
    https://github.com/SSProve/ssprove/blob/main/theories/Crypt/examples/AsymScheme.v

  In the stateful and probabilistic setting. This module defines:

    1. CPA_security "security under chosen plaintext attacks" 2. CPA_rnd_cipher
    "cipher looks random" 3. OT_secrecy "one-time secrecy" 4. OT_rnd_cipher
    "cipher looks random when the key is used only once"

    4. -> 3. -> 2. -> 1

*)

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require all_algebra choice.

From clutch Require Import clutch.

From mathcomp Require Import fingroup.

Set Warnings "notation-overridden,ambiguous-paths".
Set Default Proof Using "Type*".

Class group_struct t :=
  { e : t ; inv : t → t ; mult : t → t → t }.

Class is_group `{G : group_struct} :=
  { _ : Assoc (=) mult
  ; _ : LeftId (=) e mult
  ; _ : RightId (=) e mult
  ; _ : ∀ x, mult x (inv x) = e
  ; _ : ∀ x, mult (inv x) x = e
  }.

Definition exp `{G : group_struct t} (x : t) (k : Z) :=
  match k with
  | Zneg n => Pos.to_nat n
  | 0%Z => 42
  | Zpos p => Pos.to_nat p end.

Definition is_generator `{G : group_struct T} (g : T) :=
  forall a, exists (n : nat), a = exp g n.

Definition cyclic `{G : group_struct T} := exists g, is_generator g.

Section EGroup.
  Context `{!clutchRGS Σ}.
  Variable P : val → Set.
  Definition vt := sigT P.
  Definition vgroup_struct := group_struct vt.
  Definition is_vgroup := @is_group vt.
  Context `{G : !group_struct vt}.
  Context `{!@is_vgroup G}.
  Coercion vvt := λ (x : vt), projT1 x.
  Coercion evt := λ (x : vt), of_val (vvt x).

  Coercion vG := λ (x : vt), projT1 x.
  Coercion inG := (fun {vt} (G : group_struct vt) => vt).

  Definition is_id (v : G) := v = e.
  Definition is_mult (m : val) := ∀ (x y : vt),
    {{{ True }}}
      m x y
    {{{ v, RET v; ⌜v = vvt (mult x y)⌝ }}}.
  Definition is_inv (i : val) := ∀ (x : vt),
    {{{ True }}}
      i x
    {{{ v, RET v; ⌜vvt (inv x) = v⌝ }}}.
  Definition is_egroup e i m := is_id e /\ is_inv i /\ is_mult m.
End EGroup.


Definition Z2 := sig (fun (z : nat) => (z < 2)).
#[local] Instance Z2_group_struct : group_struct Z2.
Proof.
  constructor.
  - unshelve econstructor.
    + exact 0.
    + lia.
  - intros [z hz].
    exists ((2-z) `mod` 2).
    apply Nat.mod_upper_bound. done.
  - intros [x hx].
    intros [y hy].
    exists ((x + y) `mod` 2).
    apply Nat.mod_upper_bound. done.
Defined.

Lemma Z2_set (x y : Z2) : `x = `y → x = y.
  apply eq_sig_hprop.
  intros.
  apply Nat.lt_pi.
Qed.

#[local] Instance Z2_group : @is_group Z2 Z2_group_struct.
Proof.
  constructor.
  - intros [x hx] [y hy] [z hz].
    apply Z2_set.
    rewrite /proj1_sig.
    rewrite /mult. rewrite /Z2_group_struct.
    rewrite PeanoNat.Nat.add_mod_idemp_r => //.
    rewrite PeanoNat.Nat.add_mod_idemp_l => //.
    rewrite assoc. done.
  - intros [x hx].
    apply Z2_set.
    rewrite /proj1_sig.
    rewrite /e /mult. rewrite /Z2_group_struct.
    by apply PeanoNat.Nat.mod_small.
  - intros [x hx].
    apply Z2_set.
    rewrite /proj1_sig.
    rewrite /e /mult. rewrite /Z2_group_struct.
    replace (x + 0) with x by lia.
    by apply PeanoNat.Nat.mod_small.
  - intros [x hx].
    apply Z2_set.
    rewrite /proj1_sig.
    rewrite /e /mult /inv. rewrite /Z2_group_struct.
    rewrite PeanoNat.Nat.add_mod_idemp_r => //.
    replace (x + (2 - x)) with 2 by lia.
    done.
  - intros [x hx].
    apply Z2_set.
    rewrite /proj1_sig.
    rewrite /e /mult /inv. rewrite /Z2_group_struct.
    rewrite PeanoNat.Nat.add_mod_idemp_l => //.
    replace (2 - x + x) with 2 by lia.
    done.
Qed.

Definition PZ2 v := sig (λ n : nat, v = #n /\ n < 2).
Definition EZ2 := sigT (λ v : val, PZ2 v).
#[local] Instance EZ2_group_struct : group_struct EZ2.
Proof.
  constructor.
  - unshelve econstructor.
    + exact #0.
    + unfold PZ2. exists 0. auto with lia.
  - intros (?&n&->&hn).
    unfold EZ2.
    exists #((2-n) `mod` 2)%nat.
    unfold PZ2.
    exists (((2 - n) `mod` 2)).
    split => //.
    apply Nat.mod_upper_bound. done.
  - intros (?&x&->&hx).
    intros (?&y&->&hy).
    unfold EZ2, PZ2.
    exists #((x + y) `mod` 2)%nat.
    exists ((x + y) `mod` 2)%nat.
    split => //.
    apply Nat.mod_upper_bound. done.
Defined.

Lemma EZ2_set (x y : EZ2) : projT1 x = projT1 y → x = y.
  intros h.
  unfold EZ2, PZ2 in x,y.

  unshelve eapply (eq_sigT_hprop _ _ _ h).
  intros v p q.
  unfold PZ2 in p,q.

  unshelve eapply (eq_sig_hprop _ _ _) ; last first.
  (* unshelve eapply eq_sig. *)
  - destruct p as [n [en hn]] eqn:hp.
    destruct q as [k [ek hk]] eqn:hq.
    assert (n = k) as hnk.
    { clear hq hp. subst. inversion ek as [enk].
      by apply Nat2Z.inj in enk.
    }
    simpl.
    exact hnk.
  - simpl. intros n p' q'.
    (* apply eq_sig_uncurried. *)
    destruct p' as [en hn].
    destruct q' as [en' hn'].
    subst.
    f_equal.
    2: apply Nat.lt_pi.
    clear -en'.
    epose val_eq_dec.
    unfold EqDecision, Decision in X.
    by apply Eqdep_dec.UIP_dec.
Qed.

Definition emodulo : val :=
  rec: "mod" "x" "y" :=
    if: "x" < "y" then
      "x"
    else
      "mod" ("x" - "y") "y"
.

Context `{!clutchRGS Σ}.
Definition ee : EZ2_group_struct.
Proof.
  exists #0.
  unfold PZ2. exists 0. auto with lia.
Defined.

Definition einv : val :=
  λ:"x", emodulo (#2 - "x") #2.
Definition emult : val :=
  λ:"x" "y", emodulo ("x" * "y") #2.

Lemma EZ2_group : @is_egroup Σ _ PZ2 EZ2_group_struct
                    ee einv emult.
Proof.
  do 2 constructor.
  - rewrite /PZ2 /einv /is_inv.
    intros.
    iIntros "_ H".
    unfold inv.
    destruct x.
    destruct s.
    destruct a.
    rewrite /EZ2_group_struct.
    subst.
    simpl.
    replace (1 - (PeanoNat.Nat.divmod (2 - x0) 1 0 1).2)
      with ((2 - x0) `mod` 2) => //.
    iRevert (x0 l) "H".
    iLöb as "hh".
    iIntros (x hx) "H".
    wp_pure.
    destruct x.
    + wp_pures.
      rewrite {2}/emodulo.
      replace (2 - 0%nat) with 2 by lia.
      replace (Val (LitV (LitInt (Z.sub (Zpos (xO xH)) (Z.of_nat O))))) with (Val (LitV (LitInt (Zpos (xO xH))))) by (f_equal ; lia).
      replace (2 `mod` 2) with 0 by easy.

      wp_pures.
      iApply "H". simpl.
      iPureIntro. f_equal.
    + destruct x eqn:hh. 2: exfalso ; lia. subst.
      wp_pures. replace (2 - 1) with (1) by lia.
      rewrite {2}/emodulo.
      replace (2 - 1%nat) with 1 by lia.
      replace (Val (LitV (LitInt (Z.sub (Zpos (xO xH)) (Z.of_nat 1))))) with (Val (LitV (LitInt (Zpos xH)))) by (f_equal ; lia).
      replace (1 `mod` 2) with 1 by easy.
      wp_pures.
      simpl.
      iApply "H". simpl.
      iPureIntro. f_equal.
  - admit.
Admitted.



(** Algorithms for Key Generation, Encryption and Decryption  **)
Module Type AsymmetricSchemeAlgorithms.

  (* Key Generation *)
  Parameter KeyGen : expr.    (* unit → (PubKey * SecKey) *)

  (* Encryption algorithm *)
  Parameter Enc : expr.         (* PubKey → Plain → Cipher *)

  (* Decryption algorithm *)
  Parameter Dec_open : expr.    (* SecKey → Cipher → Plain *)

End AsymmetricSchemeAlgorithms.

(* A Module for Asymmetric Encryption Schemes, inspired to Joy of Crypto *)
Module AsymmetricScheme (ASA : AsymmetricSchemeAlgorithms).
  Import ASA.

  Parameters SecurityParameter Plain Cipher PubKey SecKey : type.

   (* Define what it means for an asymmetric encryption scheme to be: *)
   (** SECURE AGAINST CHOSEN-PLAINTEXT ATTACKS **)

  Definition L_pk_cpa_L pk_loc sk_loc
    :=
    (λ:<>, !pk_loc,
     λ:"mL" "mR",
      let: "pk_sk" := KeyGen #() in
      let: "pk" := Fst "pk_sk" in
      let: "sk" := Snd "pk_sk" in
      pk_loc <- "pk" ;;
      sk_loc <- "sk" ;;
      Enc "pk" "mL"
    )%E.
  Definition getpk_id := Fst.
  Definition challenge_id := Snd.

  Definition L_pk_cpa_R pk_loc sk_loc :=
    ( λ:<>, !pk_loc,
      λ:"mL" "mR",
      let: "pk_sk" := KeyGen #() in
      let: "pk" := Fst "pk_sk" in
      let: "sk" := Snd "pk_sk" in
      pk_loc <- "pk" ;;
      sk_loc <- "sk" ;;
      Enc "pk" "mR"
    )%E.

  Definition cpa_L_vs_R := (L_pk_cpa_L, L_pk_cpa_R).

  (** [The Joy of Cryptography] Definition 15.1

    A public-key encryption scheme is secure against chosen-plaintext attacks
    when the following holds.
  *)

  Definition CPA_security pk_loc sk_loc : Prop :=
    ∅ ⊨ L_pk_cpa_L pk_loc sk_loc
        =ctx=
        L_pk_cpa_R pk_loc sk_loc
      :
      (() → PubKey) * (Plain * Plain → Cipher) .


  (* Define what it means for an asymmetric encryption scheme to: *)
  (** HAVE PSEUDORND CIPHERTEXT IN PRESENCE OF CHOSEN PLAINTEXT ATTACKS **)

  Definition L_pk_cpa_real pk_loc sk_loc :=
    (λ:<>, !pk_loc,
     λ:"m",
      let: "pk_sk" := KeyGen #() in
      let: "pk" := Fst "pk_sk" in
      let: "sk" := Snd "pk_sk" in
      pk_loc <- "pk" ;;
      sk_loc <- "sk" ;;
      Enc "pk" "m"
    )%E.

  Definition L_pk_cpa_rand pk_loc sk_loc :=
    (λ:<>, !pk_loc,
     λ:"m",
      let: "pk_sk" := KeyGen #() in
      let: "pk" := Fst "pk_sk" in
      let: "sk" := Snd "pk_sk" in
      pk_loc <- "pk" ;;
      sk_loc <- "sk" ;;
      let: "c" := rand "n" from #() in
      "c"
    )%E.

  Definition cpa_real_vs_rand := (L_pk_cpa_real, L_pk_cpa_rand).

  (** [The Joy of Cryptography] Definition 15.2

    A public-key encryption scheme *has pseudorandom ciphertexts in the
    presence of chosen-plaintext attacks* when the following holds. *)

  Definition CPA_rnd_cipher pk_loc sk_loc : Prop :=
    ∅ ⊨ L_pk_cpa_real pk_loc sk_loc
        =ctx=
        L_pk_cpa_rand pk_loc sk_loc
      : (() → PubKey) * (Plain → Cipher) .

  (* Define what it means for an asymmetric encryption scheme to have: *)
  (** ONE-TIME SECRECY **)

  Definition Ω : expr := (rec: "f" "x" := "f" "x") #().
  Definition assert b : expr := if: b then #() else Ω.

  Definition L_pk_ots_L counter_loc pk_loc sk_loc :=
    (λ:<>, !pk_loc,
     λ:"mL" "mR",
      assert !counter_loc = #0 ;;
      counter_loc <- #1 ;;
      let: "pk_sk" := KeyGen #() in
      let: "pk" := Fst "pk_sk" in
      let: "sk" := Snd "pk_sk" in
      pk_loc <- "pk" ;;
      sk_loc <- "sk" ;;
      Enc "pk" "mL"
    )%E.

  Definition L_pk_ots_R counter_loc pk_loc sk_loc :=
    (λ:<>, !pk_loc,
     λ:"mL" "mR",
      assert !counter_loc = #0 ;;
      counter_loc <- #1 ;;
      let: "pk_sk" := KeyGen #() in
      let: "pk" := Fst "pk_sk" in
      let: "sk" := Snd "pk_sk" in
      pk_loc <- "pk" ;;
      sk_loc <- "sk" ;;
      Enc "pk" "mR"
    )%E.

  (** [The Joy of Cryptography] Definition 15.4

    A public-key encryption scheme is secure against chosen-plaintext attacks
    when the following holds.
  *)

  Definition ots_L_vs_R counter_loc pk_loc sk_loc : Prop :=
    ∅ ⊨ L_pk_ots_L counter_loc pk_loc sk_loc
        =ctx=
        L_pk_ots_R counter_loc pk_loc sk_loc
      :
      (() → PubKey) * (Plain * Plain → Cipher) .


  Definition L_pk_ots_real counter_loc pk_loc sk_loc :=
    (λ:<>, !pk_loc,
     λ:"m",
      assert !counter_loc = #0 ;;
      counter_loc <- #1 ;;
      let: "pk_sk" := KeyGen #() in
      let: "pk" := Fst "pk_sk" in
      let: "sk" := Snd "pk_sk" in
      pk_loc <- "pk" ;;
      sk_loc <- "sk" ;;
      Enc "pk" "m"
    )%E.

  Definition L_pk_ots_rand counter_loc pk_loc sk_loc :=
    (λ:<>, !pk_loc,
     λ:"mL" "mR",
      assert !counter_loc = #0 ;;
      counter_loc <- #1 ;;
      let: "pk_sk" := KeyGen #() in
      let: "pk" := Fst "pk_sk" in
      let: "sk" := Snd "pk_sk" in
      pk_loc <- "pk" ;;
      sk_loc <- "sk" ;;
      let: "c" := rand "n" from #() in
      "c"
    )%E.

  Definition ots_real_vs_rnd counter_loc pk_loc sk_loc : Prop :=
    ∅ ⊨ L_pk_ots_real counter_loc pk_loc sk_loc
        =ctx=
        L_pk_ots_rand counter_loc pk_loc sk_loc
      :
      (() → PubKey) * (Plain → Cipher) .

End AsymmetricScheme.
