(** Asymmetric encryption schemes

  In the stateful and probabilistic setting.
  This module defines:

    1. CPA_security    "security under chosen plaintext attacks"
    2. CPA_rnd_cipher  "cipher looks random"
    3. OT_secrecy      "one-time secrecy"
    4. OT_rnd_cipher   "cipher looks random when the key is used only once"

    4. -> 3. -> 2. -> 1

*)

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require
  (* Import *)
  (* all_ssreflect *)
  all_algebra
  (* ssrnat *)
  (* ssreflect *)
  (* ssrfun ssrbool *)
  choice
  (* ssrnum eqtype choice *)
  (* seq *)
.
Set Warnings "notation-overridden,ambiguous-paths".

From stdpp Require Import namespaces.
From clutch.prob_lang Require Import spec_ra notation proofmode primitive_laws lang.
From clutch.logrel Require Import model rel_rules rel_tactics adequacy.
From clutch.typing Require Import types contextual_refinement soundness.
From clutch.prelude Require Import base.
Set Default Proof Using "Type*".

From mathcomp Require Import fingroup.

Set Warnings "-notation-overridden,-ambiguous-paths".
(* From mathcomp Require Import all_ssreflect all_algebra reals distr realsum *)
(*   ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq. *)
(* Set Warnings "notation-overridden,ambiguous-paths". *)

From clutch.program_logic Require Import weakestpre.
From iris.base_logic Require Import invariants na_invariants.

From iris.base_logic Require Import invariants na_invariants.
From clutch.program_logic Require Import weakestpre.
From clutch.prob_lang Require Import spec_ra notation proofmode primitive_laws spec_tactics locations lang.
From clutch.logrel Require Import model rel_rules rel_tactics.
From clutch.prelude Require Import base.
(* From clutch.examples Require Import hash. *)

(* Module Type AsymmetricSchemeParams. *)

(*   Parameter SecurityParameter : choice .choiceType. *)
(*   Parameters Plain Cipher PubKey SecKey : finType. *)
(*   Parameter plain0 : Plain. *)
(*   Parameter cipher0 : Cipher. *)
(*   Parameter pub0 : PubKey. *)
(*   Parameter sec0 : SecKey. *)

(* End AsymmetricSchemeParams. *)

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
  Context `{!prelogrelGS Σ}.
  Variable P : val → Set.
  Definition vt := {v : val & P v}.
  Definition vgroup_struct := group_struct vt.
  Definition is_vgroup := @is_group vt.
  Context `{G : !group_struct vt}.
  Context `{!@is_vgroup G}.
  Coercion vvt := λ (x : vt), projT1 x.
  Coercion evt := λ (x : vt), of_val (vvt x).

  Coercion vG := λ (x : vt), projT1 x.
  Coercion inG := (fun (G : group_struct vt) => vt).

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


Definition Z2 := {z : nat | (z < 2)}.
Instance Z2_group_struct : group_struct Z2.
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

Instance Z2_group : @is_group Z2 Z2_group_struct.
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

Definition PZ2 v := {n : nat | v = #n /\ n < 2}.
Definition EZ2 := {v : val & PZ2 v}.
Instance EZ2_group_struct : group_struct EZ2.
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

Context `{!prelogrelGS Σ}.
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



(* Asymmetric Schemes *)
Module Type AsymmetricSchemeParams.

  Parameter SecurityParameter : type.
  Parameters Plain Cipher PubKey SecKey : type.
  (* Parameter plain0 : Plain. *)
  (* Parameter cipher0 : Cipher. *)
  (* Parameter pub0 : PubKey. *)
  (* Parameter sec0 : SecKey. *)

End AsymmetricSchemeParams.

(** Algorithms for Key Generation, Encryption and Decryption  **)
Module Type AsymmetricSchemeAlgorithms (ASP : AsymmetricSchemeParams).
  Import ASP.

  (* Key Generation *)
  Parameter KeyGen : expr.    (* unit → (PubKey * SecKey) *)

  (* Encryption algorithm *)
  Parameter Enc : expr.         (* PubKey → Plain → Cipher *)

  (* Decryption algorithm *)
  Parameter Dec_open : expr.    (* SecKey → Cipher → Plain *)

End AsymmetricSchemeAlgorithms.

(* A Module for Asymmetric Encryption Schemes, inspired to Joy of Crypto *)
Module AsymmetricScheme (ASP : AsymmetricSchemeParams)
                        (ASA : AsymmetricSchemeAlgorithms ASP).

  Import ASP.
  Import ASA.


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
      let: "c" := flip #() in
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
      let: "c" := flip #() in
      "c"
    )%E.

  Definition ots_real_vs_rnd counter_loc pk_loc sk_loc : Prop :=
    ∅ ⊨ L_pk_ots_real counter_loc pk_loc sk_loc
        =ctx=
        L_pk_ots_rand counter_loc pk_loc sk_loc
      :
      (() → PubKey) * (Plain → Cipher) .

End AsymmetricScheme.


(** ElGamal encryption scheme.

  We show that DH security implies the security of ElGamal.

*)


Module Type ElGamalParam.

  Context `{!gT : group_struct vt}.
  Parameter g : gT.
  Parameter g_gen : is_generator _ gT g.
  (* Parameter g_gen : ζ = <[g]>. *)
  Parameter order_gt1 : (1 < order _ gT)%N.

End ElGamalParam.

Module ElGamal (EGP : ElGamalParam).

Import EGP.
Definition ζ := gT.
Parameter cyclic_zeta : cyclic _ ζ.

(* order of g *)
Definition q : N := order _ gT.

Parameter group_prodC :
  ∀ x y : gT, @mult _ gT x y = @mult _ gT y x.

Module MyParam <: AsymmetricSchemeParams.

  Definition SecurityParameter : type := TInt.
  Definition Plain := gT.
  Definition Cipher := (vt * vt)%type.
  Definition PubKey := vt.
  Definition SecKey := vt. (* [finType of 'Z_q] *)

  (* Definition plain0 := g. *)
  (* Definition cipher0 := (g, g). *)
  (* Definition pub0 := g. *)
  (* Definition sec0 : SecKey := 0. *)

End MyParam.

Module MyAlg <: AsymmetricSchemeAlgorithms MyParam.

  Import MyParam.

  #[export] Instance positive_gT : Positive #|gT|.
  Proof.
    apply /card_gt0P. exists g. auto.
  Qed.

  #[export] Instance positive_SecKey : Positive #|SecKey|.
  Proof.
    apply /card_gt0P. exists sec0. auto.
  Qed.

  Definition Plain_pos : Positive #|Plain| := _.
  Definition PubKey_pos : Positive #|PubKey| := _.
  Definition SecKey_pos : Positive #|SecKey| := _.

  #[export] Instance Cipher_pos : Positive #|Cipher|.
  Proof.
    unfold Cipher. rewrite card_prod.
    exact _.
  Qed.

  Definition chPlain  : choice_type := 'fin #|gT|.
  Definition chPubKey : choice_type := 'fin #|gT|.
  Definition chCipher : choice_type := 'fin #|Cipher|.
  Definition chSecKey : choice_type := 'fin #|SecKey|.

  Definition counter_loc : Location := ('nat ; 0%N).
  Definition pk_loc : Location := (chPubKey ; 1%N).
  Definition sk_loc : Location := (chSecKey ; 2%N).
  Definition m_loc  : Location := (chPlain ; 3%N).
  Definition c_loc  : Location := (chCipher ; 4%N).

  Definition kg_id : nat := 5.
  Definition enc_id : nat := 6.
  Definition dec_id : nat := 7.
  Definition challenge_id : nat := 8. (*challenge for LR *)
  Definition challenge_id' : nat := 9. (*challenge for real rnd *)
  Definition getpk_id : nat := 42. (* routine to get the public key *)

  Definition i_plain := #|Plain|.
  Definition i_cipher := #|Cipher|.
  Definition i_pk := #|PubKey|.
  Definition i_sk := #|SecKey|.
  Definition i_bool := 2.


  (** Key Generation algorithm *)
  Definition KeyGen {L : {fset Location}} :
    code L [interface] (chPubKey × chSecKey) :=
    {code
      x ← sample uniform i_sk ;;
      let x := otf x in
      ret (fto (g^+x), fto x)
    }.

  (** Encryption algorithm *)
  Definition Enc {L : {fset Location}} (pk : chPubKey) (m : chPlain) :
    code L [interface] chCipher :=
    {code
      y ← sample uniform i_sk ;;
      let y := otf y in
      ret (fto (g^+y, (otf pk)^+y * (otf m)))
    }.

  (** Decryption algorithm *)
  Definition Dec_open {L : {fset Location}} (sk : chSecKey) (c : chCipher) :
    code L [interface] chPlain :=
    {code
      ret (fto ((fst (otf c)) * ((snd (otf c))^-(otf sk))))
    }.

  Notation " 'plain " :=
    chPlain
    (in custom pack_type at level 2).

  Notation " 'cipher " :=
    chCipher
    (in custom pack_type at level 2).

  Notation " 'pubkey " :=
    chPubKey
    (in custom pack_type at level 2).

End MyAlg.

Local Open Scope package_scope.

Module ElGamal_Scheme := AsymmetricScheme MyParam MyAlg.

Import MyParam MyAlg ElGamal_Scheme.

Lemma counter_loc_in :
  counter_loc \in (fset [:: counter_loc; pk_loc; sk_loc ]).
Proof.
  auto_in_fset.
Qed.

Lemma pk_loc_in :
  pk_loc \in (fset [:: counter_loc; pk_loc; sk_loc ]).
Proof.
  auto_in_fset.
Qed.

Lemma sk_loc_in :
  sk_loc \in (fset [:: counter_loc; pk_loc; sk_loc ]).
Proof.
  auto_in_fset.
Qed.

Definition DH_loc := fset [:: pk_loc ; sk_loc].

Definition DH_real :
  package DH_loc [interface]
    [interface #val #[10] : 'unit → 'pubkey × 'cipher ] :=
    [package
      #def #[10] (_ : 'unit) : 'pubkey × 'cipher
      {
        a ← sample uniform i_sk ;;
        let a := otf a in
        b ← sample uniform i_sk ;;
        let b := otf b in
        #put pk_loc := fto (g^+a) ;;
        #put sk_loc := fto a ;;
        ret (fto (g^+a), fto (g^+b, g^+(a * b)))
      }
    ].

Definition DH_rnd :
  package DH_loc [interface]
    [interface #val #[10] : 'unit → 'pubkey × 'cipher ] :=
    [package
      #def #[10] (_ : 'unit) : 'pubkey × 'cipher
      {
        a ← sample uniform i_sk ;;
        let a := otf a in
        b ← sample uniform i_sk ;;
        let b := otf b in
        c ← sample uniform i_sk ;;
        let c := otf c  in
        #put pk_loc := fto (g^+a) ;;
        #put sk_loc := fto a ;;
        ret (fto (g^+a), fto (g^+b, g^+c))
      }
    ].

Definition Aux :
  package (fset [:: counter_loc ; pk_loc ])
    [interface #val #[10] : 'unit → 'pubkey × 'cipher]
    [interface
      #val #[getpk_id] : 'unit → 'pubkey ;
      #val #[challenge_id'] : 'plain → 'cipher
    ]
  :=
  [package
    #def #[getpk_id] (_ : 'unit) : 'pubkey
    {
      pk ← get pk_loc ;;
      ret pk
    } ;

    #def #[challenge_id'] (m : 'plain) : 'cipher
    {
      #import {sig #[10] : 'unit → 'pubkey × 'cipher } as query ;;
      count ← get counter_loc ;;
      #assert (count == 0)%N ;;
      #put counter_loc := (count + 1)%N ;;
      '(pk, c) ← query Datatypes.tt ;;
      @ret chCipher (fto ((otf c).1 , (otf m) * ((otf c).2)))
    }
  ].

Lemma ots_real_vs_rnd_equiv_true :
  Aux ∘ DH_real ≈₀ ots_real_vs_rnd true.
Proof.
  (* We go to the relation logic using equality as invariant. *)
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  all: ssprove_code_simpl.
  (* We are now in the realm of program logic *)
  - eapply rpost_weaken_rule. 1: eapply rreflexivity_rule.
    move => [a1 h1] [a2 h2] [Heqa Heqh]. intuition auto.
  - ssprove_sync_eq. intro count.
    ssprove_sync_eq. move => /eqP e. subst.
    ssprove_sync_eq.
    ssprove_sync_eq. intro a.
    ssprove_swap_lhs 0%N.
    ssprove_sync_eq.
    ssprove_swap_lhs 0%N.
    ssprove_sync_eq.
    ssprove_sync_eq. intro b.
    rewrite !otf_fto. simpl.
    eapply r_ret. intuition eauto.
    f_equal. f_equal.
    rewrite group_prodC. f_equal.
    apply expgM.
Qed.

Lemma bijective_expgn :
  bijective (λ (a : 'Z_q), g ^+ a).
Proof.
  unshelve eexists (λ x, (proj1_sig (@cyclePmin gT g x _) %% q)%:R).
  - rewrite -g_gen. unfold ζ. apply in_setT.
  - simpl. intros a.
    match goal with
    | |- context [ @cyclePmin _ _ _ ?hh ] =>
      set (h := hh)
    end.
    clearbody h. simpl in h.
    destruct cyclePmin as [n hn e]. simpl.
    move: e => /eqP e. rewrite eq_expg_mod_order in e.
    move: e => /eqP e.
    rewrite -e.
    (* case_eq (q == 1)%N.
    1:{
      fold q in *. set (q' := q) in *. clearbody q'.
      move /eqP => ?. subst. rewrite modn1.
      clear h n e hn.
      destruct a as [a h]. unfold Zp_trunc in *. simpl in *.
      (* So in the case where q = 1, we have 'Z_1 = {0, 1} but a mod 1 = 0. *)
    } *)
    rewrite modn_small.
    2:{
      fold q. eapply leq_trans. 1: eapply ltn_ord.
      rewrite Zp_cast.
      2: apply order_gt1.
      auto.
    }
    apply natr_Zp.
  - simpl. intro x.
    match goal with
    | |- context [ @cyclePmin _ _ _ ?hh ] =>
      set (h := hh)
    end.
    clearbody h. simpl in h.
    destruct cyclePmin as [n hn e]. simpl. subst.
    rewrite modn_small. 2: auto.
    f_equal. rewrite val_Zp_nat. 2: apply order_gt1.
    apply modn_small. auto.
Qed.

#[local] Definition f m : 'Z_q * 'Z_q → gT * gT :=
  λ '(a,b), (g^+a, (otf m) * g^+b).

Lemma bijective_f : ∀ m, bijective (f m).
Proof.
  intro m.
  pose proof bijective_expgn as bij.
  destruct bij as [d hed hde].
  eexists (λ '(x,y), (d x, d ((otf m)^-1 * y))).
  - intros [? ?]. simpl. rewrite hed. f_equal.
    rewrite mulgA. rewrite mulVg. rewrite mul1g.
    apply hed.
  - intros [x y]. simpl. rewrite hde. f_equal.
    rewrite hde. rewrite mulgA. rewrite mulgV. rewrite mul1g.
    reflexivity.
Qed.

#[local] Definition f' (m : chPlain) :
  Arit (uniform (i_sk * i_sk)) → Arit (uniform i_cipher) :=
  λ x,
    let '(a, b) := ch2prod x in
    fto (f m (otf a, otf b)).

Lemma bijective_f' : ∀ m, bijective (f' m).
Proof.
  intro m.
  pose proof (bijective_f m) as bij. destruct bij as [g gf fg].
  unfold f'.
  exists (λ x, let '(a,b) := g (otf x) in prod2ch (fto a, fto b)).
  - cbn - [f]. intros x. rewrite -[RHS]prod2ch_ch2prod.
    set (y := ch2prod x). clearbody y. clear x.
    simpl in y. destruct y as [a b].
    rewrite otf_fto. rewrite gf.
    rewrite !fto_otf. reflexivity.
  - cbn - [f]. intro x.
    replace x with (fto (f m (g (otf x)))) at 2.
    2:{ rewrite fg. rewrite fto_otf. reflexivity. }
    set (y := g (otf x)). change (g (otf x)) with y. clearbody y. clear x.
    destruct y as [a b]. rewrite ch2prod_prod2ch. rewrite !otf_fto.
    reflexivity.
Qed.

Lemma ots_real_vs_rnd_equiv_false :
  ots_real_vs_rnd false ≈₀ Aux ∘ DH_rnd.
Proof.
  (* We go to the relation logic using equality as invariant. *)
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  all: ssprove_code_simpl.
  (* We are now in the realm of program logic *)
  - eapply rpost_weaken_rule. 1: eapply rreflexivity_rule.
    cbn. intros [? ?] [? ?] e. inversion e. intuition auto.
  - ssprove_sync_eq. intro count.
    ssprove_sync_eq.
    intros h.
    ssprove_sync_eq.
    ssprove_sync_eq. intros a.
    ssprove_swap_rhs 1%N.
    ssprove_swap_rhs 0%N.
    ssprove_sync_eq.
    ssprove_swap_rhs 1%N.
    ssprove_swap_rhs 0%N.
    ssprove_sync_eq.
    eapply r_transR.
    1:{ eapply r_uniform_prod. intros x y. eapply rreflexivity_rule. }
    simpl.
    eapply rsymmetry.
    eapply @r_uniform_bij with (f := f' m). 1: apply bijective_f'.
    simpl. intros x.
    unfold f'. set (z := ch2prod x). clearbody z. clear x.
    destruct z as [x y]. simpl.
    rewrite !otf_fto.
    eapply r_ret.
    intros s ? e.
    subst. simpl. easy.
Qed.

Theorem ElGamal_OT :
  ∀ LA A,
    ValidPackage LA [interface
      #val #[getpk_id] : 'unit → 'pubkey ;
      #val #[challenge_id'] : 'plain → 'cipher
    ] A_export A →
    fdisjoint LA (ots_real_vs_rnd true).(locs) →
    fdisjoint LA (ots_real_vs_rnd false).(locs) →
    Advantage ots_real_vs_rnd A <= AdvantageE DH_rnd DH_real (A ∘ Aux).
Proof.
  intros LA A vA hd₀ hd₁.
  simpl in hd₀, hd₁. clear hd₁. rename hd₀ into hd.
  rewrite Advantage_E.
  ssprove triangle (ots_real_vs_rnd false) [::
    Aux ∘ DH_rnd ;
    Aux ∘ DH_real
  ] (ots_real_vs_rnd true) A
  as ineq.
  eapply le_trans. 1: exact ineq.
  clear ineq.
  rewrite ots_real_vs_rnd_equiv_true. 3: auto.
  2:{
    rewrite fdisjointUr. apply/andP. split.
    - unfold L_locs_counter in hd.
      rewrite fdisjointC.
      eapply fdisjoint_trans. 2:{ rewrite fdisjointC. exact hd. }
      rewrite [X in fsubset _ X]fset_cons.
      rewrite fset_cons. apply fsetUS.
      rewrite !fset_cons -fset0E.
      apply fsetUS.
      apply fsub0set.
    - unfold DH_loc. unfold L_locs_counter in hd.
      rewrite fdisjointC.
      eapply fdisjoint_trans. 2:{ rewrite fdisjointC. exact hd. }
      rewrite [X in fsubset _ X]fset_cons.
      apply fsubsetUr.
  }
  rewrite ots_real_vs_rnd_equiv_false. 2: auto.
  2:{
    rewrite fdisjointUr. apply/andP. split.
    - unfold L_locs_counter in hd.
      rewrite fdisjointC.
      eapply fdisjoint_trans. 2:{ rewrite fdisjointC. exact hd. }
      rewrite [X in fsubset _ X]fset_cons.
      rewrite fset_cons. apply fsetUS.
      rewrite !fset_cons -fset0E.
      apply fsetUS.
      apply fsub0set.
    - unfold DH_loc. unfold L_locs_counter in hd.
      rewrite fdisjointC.
      eapply fdisjoint_trans. 2:{ rewrite fdisjointC. exact hd. }
      rewrite [X in fsubset _ X]fset_cons.
      apply fsubsetUr.
  }
  rewrite GRing.addr0. rewrite GRing.add0r.
  rewrite -Advantage_link. auto.
Qed.

End ElGamal.

Module EGP_Z3 <: ElGamalParam.

  Definition gT : finGroupType := Zp_finGroupType 2.
  Definition ζ : {set gT} := [set : gT].
  Definition g :  gT := Zp1.

  Lemma g_gen : ζ = <[g]>.
  Proof.
    unfold ζ, g. apply Zp_cycle.
  Qed.

  Lemma order_gt1 : (1 < #[g])%N.
  Proof.
    unfold g.
    rewrite order_Zp1.
    reflexivity.
  Qed.

End EGP_Z3.

Module ElGamal_Z3 := ElGamal EGP_Z3.
