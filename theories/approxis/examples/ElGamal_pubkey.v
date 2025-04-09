(* One-time indistinguishability from random for ElGamal encryption.

   The main difference with the Clutch version is that we use the "standard"
   security games for public key encryption defined in pubkey.v. Since these
   rely on semantically well-typed adversaries instead of syntactically typed
   ones, we can drop the well-formedness check for messages from the adversary.
   In the Clutch version of ElGamal, we explicitly checked if the message was a
   valid group element. *)
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From clutch.prob_lang Require Import advantage typing.tychk.
From clutch.approxis Require Import reltac2 approxis map list option.
From clutch.clutch.examples.crypto Require ElGamal_bijection.
Import ElGamal_bijection.bij_nat.
From clutch.approxis.examples Require Import symmetric security_aux sum_seq xor prf advantage_laws pubkey valgroup ElGamal.
Set Default Proof Using "All".

From mathcomp Require ssrnat.
From mathcomp Require Import zmodp finset ssrbool fingroup.fingroup solvable.cyclic.
Import valgroup_notation.


Section ElGamal_alt.

Context {vg : val_group}.           (* A group on a subset of values. *)
Context {cg : clutch_group_struct}. (* Implementations of the vg group operations *)
Context {vgg : @val_group_generator vg}.   (* G is generated by g. *)
Context {cgg : @clutch_group_generator vg cg vgg}. (* g is well-typed *)

#[local] Notation n := (S n'').
#[local] Definition rnd t := (rand(t) #n)%E.

Definition rand_cipher : val :=
  λ:"msg",
    let: "b" := rnd #() in
    let: "x" := rnd #() in
    let, ("B", "X") := (g^"b", g^"x") in
    ("B", "X").

Definition pk_real := CPA_OTS_real keygen enc.
Definition pk_rand := CPA_OTS_rand keygen rand_cipher.

(* Unfold definitions and label the flips. We need to label the flip in
   "query" since it occurs in a closure, and we want to relate it to an
   eager sampling in the set-up phase in order to make DH_real appear as a
   sub-expression. *)
Definition pk_real_tape : expr :=
  let: "β" := alloc #n in
  let: "sk" := rnd #() in
  let: "pk" := g^"sk" in
  let: "count" := ref #0 in
  let: "query" := λ:"msg",
      (* let:m "msg" := vg_of_int "msg" in *)
      assert (!"count" = #0) ;;;
      "count" <- #1 ;;
      let: "b" := rnd "β" in
      let: "B" := g^"b" in
      let: "C" := "pk"^"b" in
      let: "X" := "msg" · "C" in
      ("B", "X") in
  ("pk", "query").

(* Pull out DH_real/rand. This requires moving the sampling of "b" from "query"
   to the initialisation. Only equivalent because "query" gets called only
   once: only one message is encrypted, so only one nonce "b" is required, and
   we can pre-sample it in the setup. *)

Definition eC : val :=
  (λ: "DH_real_or_rnd",
       let, ("pk", "B", "C") := "DH_real_or_rnd" in
       let: "count" := ref #0 in
       let: "query" := λ: "msg",
           assert (!"count" = #0) ;;;
           "count" <- #1 ;;
           let: "X" := "msg" · "C" in
           ("B", "X") in
       ("pk", "query")).

Definition C : list ectx_item := [AppRCtx eC].
Definition C_DH_real : expr := fill C DH_real.
Definition C_DH_rand : expr := fill C DH_rand.

(* Inline DH_rand and push the two random samplings not required for the key
   generation back down (using tapes β and γ). *)
Definition pk_rand_tape : expr :=
  let: "β" := alloc #n in
  let: "γ" := alloc #n in
  let: "sk" := rnd #() in
  let: "pk" := g^"sk" in
  let: "count" := ref #0 in
  let: "query" := λ:"msg",
      assert (!"count" = #0) ;;;
      "count" <- #1 ;;
      let: "b" := rnd "β" in
      let: "c" := rnd "γ" in
      let: "B" := g^"b" in
      let: "C" := g^"c" in
      let: "X" := "msg" · "C" in
      ("B", "X") in
  ("pk", "query").


Section LogRel.

Context `{!approxisRGS Σ}.
Context {G : clutch_group (vg:=vg) (cg:=cg)}. (* cg satisfies the group laws. *)
Context {Δ : listO (lrelC Σ)}.

#[local] Notation T := (interp τG Δ).

(* The semantic type of the Diffie-Hellman game(s). *)
Definition T_DH := Eval cbn in (interp τ_DH Δ).

Definition τ_EG := (τG * (τG → () + τG * τG))%ty.
(* The semantic type of the ElGamal game(s). *)
Definition T_EG := Eval cbn in (interp τ_EG Δ).

Import valgroup_tactics.

Ltac rel_red :=
  iStartProof ;
  repeat (iredrs ; try first [rel_exp_r | rel_mult_r | rel_inv_r]) ;
  repeat (iredls ; try first [rel_exp_l | rel_mult_l | rel_inv_l]).

Definition pkN := nroot.@"pks".

Local Tactic Notation "inv_prove" :=
  iSplitL ; [ by (repeat (iExists _) ; (by iFrame) || (iLeft ; by iFrame) || (iRight ; by iFrame)) |].

Local Tactic Notation "inv_mk" constr(Pinv) constr(h) :=
  iApply (refines_na_alloc Pinv pkN) ; inv_prove ; iIntros h.

Local Tactic Notation "inv_cl" constr(h) :=
  iApply (refines_na_close with h) ; inv_prove.

Variable (T_eq : (forall m1 m2, ⊢ (T m1 m2 -∗ ∃ vmsg : vgG, ⌜m1 = vmsg⌝ ∧ ⌜m2 = vmsg⌝))%I).


Lemma real_real_tape : ⊢ refines top pk_real pk_real_tape T_EG.
Proof with rel_red.
  rel_red. rewrite /keygen... rel_apply (refines_couple_UU n). 1: intuition auto ; lia.
  iIntros "!> %sk %le_sk_n".
  idtac...
  rewrite /q_calls_poly...
  inv_mk (βₛ ↪ₛN (n;[]) ∗ (counter ↦ #0 ∗ countₛ ↦ₛ #0) ∨ (counter ↦ #1 ∗ countₛ ↦ₛ #1) )%I "#Hinv"...
  rel_vals ; iIntros "!>" (??) "#rel_m"...
  iPoseProof (T_eq with "rel_m") as "(%&->&->)".
  iApply (refines_na_inv with "[-$Hinv]"); [done|].
  iIntros "[>[(β&c&c')|(c&c')] Hclose]"...
  2: inv_cl "[- $Hclose]" ; rel_vals.
  rewrite /enc...
  rel_apply (refines_couple_UT). 1: intuition auto ; lia.
  iFrame. iIntros (b bn) "!> β". iredpures.
  rel_rand_r. iIntros (_)...
  inv_cl "[- $Hclose]"... rel_vals.
Qed.

Lemma real_tape_real : ⊢ refines top pk_real_tape pk_real T_EG.
Proof with rel_red.
  rel_red. rewrite /keygen... rel_apply (refines_couple_UU n). 1: intuition auto ; lia.
  iIntros "!> %sk %le_sk_n".
  idtac...
  rewrite /q_calls_poly...
  inv_mk (β ↪N (n;[]) ∗ (count ↦ #0 ∗ counterₛ ↦ₛ #0) ∨ (count ↦ #1 ∗ counterₛ ↦ₛ #1) )%I "#Hinv"...
  rel_vals ; iIntros "!>" (??) "#rel_m"...
  iPoseProof (T_eq with "rel_m") as "(%&->&->)"...
  iApply (refines_na_inv with "[-$Hinv]"); [done|].
  iIntros "[>[(β&c&c')|(c&c')] Hclose]"...
  2: inv_cl "[- $Hclose]" ; rel_vals.
  rewrite /enc...
  rel_apply (refines_couple_TU n). 1: intuition auto ; lia.
  iFrame. iIntros (b bn) "β". iredpures.
  rel_rand_l. iIntros (_)...
  inv_cl "[- $Hclose]" ; rel_vals.
Qed.


Lemma real_tape_C_DH_real : ⊢ refines top pk_real_tape C_DH_real T_EG.
Proof with rel_red.
  rewrite /C_DH_real /=. rel_red.
  rel_apply (refines_couple_UU n). 1: intuition auto ; lia.
  iIntros "!> %sk %le_sk_n".
  idtac...
  rel_apply (refines_couple_TU n). 1: intuition auto ; lia.
  iFrame. iIntros (b bn) "β". iredpures.
  rewrite -Nat2Z.inj_mul/eC...
  inv_mk ((β ↪N (n;[b]) ∗ count ↦ #0 ∗ countₛ ↦ₛ #0)
          ∨ (count ↦ #1 ∗ countₛ ↦ₛ #1))%I "#Hinv".
  rel_vals ; iIntros "!>" (??) "#rel_m"...
  iPoseProof (T_eq with "rel_m") as "(%&->&->)"...
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "[>[(β&cnt&cnt')|(c&c')] Hclose]".
  2: by (ireds ; inv_cl "[- $Hclose]" ; rel_vals).
  do 6 iredl.
  iredl. iIntros (_).
  rel_load_r...
  inv_cl "[- $Hclose]"...
  rewrite -expgM -ssrnat.multE. rel_vals.
Qed.

Lemma C_DH_real_real_tape : ⊢ refines top C_DH_real pk_real_tape T_EG.
Proof with rel_red.
  rewrite /C_DH_real /=. rel_red.
  rel_apply (refines_couple_UU n). 1: intuition auto ; lia.
  iIntros "!> %sk %le_sk_n".
  idtac...
  rewrite /q_calls_poly...
  ireds.
  rel_apply (refines_couple_UT). 1: intuition auto ; lia.
  iFrame. iIntros (b bn) "!> βₛ". iredpures.
  rewrite -Nat2Z.inj_mul/eC...
  inv_mk ((βₛ ↪ₛN (n;[b]) ∗ count ↦ #0 ∗ countₛ ↦ₛ #0)
          ∨ (count ↦ #1 ∗ countₛ ↦ₛ #1))%I "#Hinv".
  rel_vals ; iIntros "!>" (??) "#rel_m"...
  iPoseProof (T_eq with "rel_m") as "(%&->&->)"...
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "[[(β&cnt&cnt')|(c&c')] Hclose]"...
  2: (rel_load_r ; rel_red ; inv_cl "[- $Hclose]" ; rel_vals).
  rel_load_r. do 6 iredr. iIntros (_). rel_red.
  inv_cl "[- $Hclose]"...
  rewrite -expgM -ssrnat.multE. rel_vals.
Qed.

Lemma C_DH_rand_rand_tape : ⊢ refines top C_DH_rand pk_rand_tape T_EG.
Proof with rel_red.
  rewrite /C_DH_rand/C/eC /=. rel_red.
  rel_apply (refines_couple_UU n). 1: intuition auto ; lia.
  iIntros "!> %sk %le_sk_n".
  idtac...
  rel_apply (refines_couple_UT). 1: intuition auto ; lia.
  iFrame "βₛ". iIntros (b bn) "!> βₛ". iredpures.
  rel_apply (refines_couple_UT). 1: intuition auto ; lia.
  iFrame "γₛ". iIntros (c cn) "!> γₛ". iredpures...
  inv_mk ((βₛ ↪ₛN (n;[b]) ∗ γₛ ↪ₛN (n;[c]) ∗ count ↦ #0 ∗ countₛ ↦ₛ #0)
          ∨ (count ↦ #1 ∗ countₛ ↦ₛ #1))%I "#Hinv".
  rel_vals ; iIntros "!>" (??) "#rel_m"...
  iPoseProof (T_eq with "rel_m") as "(%&->&->)".
  iApply (refines_na_inv with "[$Hinv]") => //.
  iIntros "[>[(β'&γ'&cnt&cnt')|(cnt&cnt')] Hclose]". 2: idtac...
  2: inv_cl "[- $Hclose]" ; rel_vals.
  rel_load_l ; rel_load_r. iredpures. rel_store_r. rel_store_l.
  iredpures. rel_randT_r. iIntros (_). do 3 iredr. iIntros (_).
  rel_red.
  inv_cl "[- $Hclose]" ; rel_vals.
Qed.

Lemma rand_tape_C_DH_rand : ⊢ refines top pk_rand_tape C_DH_rand T_EG.
Proof with rel_red.
  rewrite /C_DH_rand/C/eC /=. rel_red.
  rel_apply (refines_couple_UU n). 1: intuition auto ; lia.
  iIntros "!> %sk %le_sk_n"...
  rel_apply (refines_couple_TU n). 1: intuition auto ; lia.
  iFrame "β". iIntros (b bn) "β"...
  rel_apply (refines_couple_TU n). 1: intuition auto ; lia.
  iFrame "γ". iIntros (c cn) "γ"...
  inv_mk ((β ↪N (n;[b]) ∗ γ ↪N (n;[c]) ∗ count ↦ #0 ∗ countₛ ↦ₛ #0)
          ∨ (count ↦ #1 ∗ countₛ ↦ₛ #1))%I "#Hinv".
  rel_vals ; iIntros "!>" (??) "#rel_m"...
  iPoseProof (T_eq with "rel_m") as "(%&->&->)".
  iApply (refines_na_inv with "[$Hinv]") => //.
  iIntros "[>[(β'&γ'&cnt&cnt')|(cnt&cnt')] Hclose]" ; rel_load_l ; rel_load_r.
  2: inv_cl "[- $Hclose]" ; rel_red ; rel_vals.
  do 6 iredl. iIntros (_). rel_pures_r. rel_store_r. rel_pures_l. iredl. iIntros (_)...
  inv_cl "[- $Hclose]" ; rel_red ; rel_vals.
Qed.

Lemma rand_tape_rand : ⊢ refines top pk_rand_tape pk_rand T_EG.
Proof with rel_red.
  rel_red. rewrite /keygen...
  rel_apply (refines_couple_UU n). 1: intuition auto ; lia.
  iIntros "!> %sk %le_sk_n"...
  rewrite /q_calls_poly...
  inv_mk ((β ↪N (n;[]) ∗ γ ↪N (n;[]) ∗ count ↦ #0 ∗ counterₛ ↦ₛ #0)
          ∨ (count ↦ #1 ∗ counterₛ ↦ₛ #1))%I "#Hinv".
  rel_vals ; iIntros "!>" (??) "#rel_m"...
  iPoseProof (T_eq with "rel_m") as "(%&->&->)"...
  iApply (refines_na_inv with "[-$Hinv]") => //.
  iIntros "[>[(β&γ&cnt&cnt')|(cnt&cnt')] Hclose]"...
  2: by (inv_cl "[-$Hclose]" ; rel_vals).
  rewrite /rand_cipher...
  rel_apply (refines_couple_TU n). 1: intuition auto ; lia.
  iFrame "β". iIntros (b bn) "β".
  rel_pures_r.
  (* Rewrite msg into g^k_msg for some k_msg. *)
  destruct (log_g vmsg) as [k_msg ->].
  (* Sample c on the left, and ((k_msg + c) mod (S n)) on the right. *)
  rel_apply (refines_couple_TU n (mod_plus _ k_msg)).
  1: apply mod_plus_lt.
  iFrame "γ". iIntros (x xn) "γ". rel_rand_l. iIntros (_). rel_rand_l. iIntros (_)...
  inv_cl "[- $Hclose]"...
  rewrite -expgD -ssrnat.plusE.
  rewrite /mod_plus...
  assert ((g ^+ (k_msg + x)) = (g ^+ mod_plus _ k_msg x))%g as heq.
  { clear -xn.
    rewrite /mod_plus.
    destruct (x <? S n) eqn:h.
    2:{ exfalso. eapply Nat.ltb_nlt. 1: eauto. apply PeanoNat.le_lt_n_Sm. done. }
    pose proof (e := eq_sym (expg_mod_order g (k_msg+x))).
    rewrite g_nontriv in e.
    exact e.
  }
  rewrite -heq. rel_vals.
Qed.

Lemma rand_rand_tape : ⊢ refines top pk_rand pk_rand_tape T_EG.
Proof with rel_red.
  rel_red. rewrite /keygen...
  rel_apply (refines_couple_UU n). 1: intuition auto ; lia.
  iIntros "!> %sk %le_sk_n"...
  rewrite /q_calls_poly...
  inv_mk ((βₛ ↪ₛN (n;[]) ∗ γₛ ↪ₛN (n;[]) ∗ counter ↦ #0 ∗ countₛ ↦ₛ #0)
          ∨ (counter ↦ #1 ∗ countₛ ↦ₛ #1))%I "#Hinv"...
  rel_vals ; iIntros "!>" (??) "#rel_m"...
  iPoseProof (T_eq with "rel_m") as "(%&->&->)"...
  iApply (refines_na_inv with "[-$Hinv]") => //.
  iIntros "[>[(βₛ&γₛ&count&countₛ)|(count&countₛ)] Hclose]"...
  2: by (inv_cl "[-$Hclose]" ; rel_vals).
  rewrite /rand_cipher...
  rel_apply (refines_couple_UT n). 1: intuition auto ; lia.
  iFrame "βₛ". iIntros "!>" (b bn) "βₛ". rel_pures_l.
  (* Rewrite msg into g^k_msg for some k_msg. *)
  destruct (log_g vmsg) as [k_msg ->].
  (* Sample x on the left, and ((-x + k_msg) mod (S n)) on the right. *)
  rel_apply (refines_couple_UT n (mod_minus _ k_msg)). 1: apply mod_minus_lt.
  iFrame "γₛ". iIntros "!>" (x xn) "γₛ". rel_rand_r. iIntros (_).
  rel_pures_r. rel_rand_r. iIntros (le_gx_n)...
  inv_cl "[- $Hclose]"...
  rewrite -expgD -ssrnat.plusE.
  assert ((g ^+ x) = (g ^+ (k_msg + mod_minus _ k_msg x)))%g as heq.
  {
    clear -xn le_gx_n.
    rewrite /mod_minus.
    destruct (x <? S n) eqn:h.
    2:{ exfalso. eapply Nat.ltb_nlt. 1: eauto. apply PeanoNat.le_lt_n_Sm. done. }
    pose proof (e := (expg_mod_order g)).
    rewrite g_nontriv in e.
    rewrite -[in LHS]e -{}[in RHS]e.
    f_equal.
    rewrite !ssrnat.plusE !ssrnat.minusE.
    rewrite div.modnDmr.
    rewrite ssrnat.addnC.
    rewrite -ssrnat.addnA.
    rewrite [ssrnat.addn x _]ssrnat.addnC ssrnat.addnA.
    rewrite ssrnat.subnK.
    - rewrite div.modnDl. reflexivity.
    - apply /ssrnat.leP. move : (fin_to_nat_lt k_msg). lia.
  }
  rewrite -heq. rel_vals.
Qed.

(* Decryption is left inverse to encryption. We only consider valid messages. *)
Lemma ElGamal_correct :
  ⊢ refines top
      (let, ("sk", "pk") := keygen #() in
       λ:"msg", dec "sk" (enc "pk" "msg"))
      (λ:"msg", "msg")
      (lrel_G → lrel_G).
Proof with rel_red.
  rewrite /keygen...
  rel_apply_l refines_randU_l ; iIntros...
  rel_arrow_val ; iIntros (??) "#(%msg&->&->)"...
  rewrite /enc/dec... rel_apply_l refines_randU_l ; iIntros...
  rewrite -?expgM -ssrnat.multE -mulgA Nat.mul_comm mulgV mulg1.
  rel_vals.
Qed.

End LogRel.

Section Ctx.

Context {G : forall `{!approxisRGS Σ}, clutch_group (vg:=vg) (cg:=cg)}.

Variable (T_eq : (forall `{!approxisRGS Σ} Δ m1 m2, ⊢ (interp τG Δ m1 m2 -∗ ∃ vmsg : vgG, ⌜m1 = vmsg⌝ ∧ ⌜m2 = vmsg⌝))%I).

Lemma ctx_real_real_tape : ∅ ⊨ pk_real =ctx= pk_real_tape : τ_EG.
Proof. split ; apply (refines_sound approxisRΣ) ; intros ; [ apply: real_real_tape | apply: real_tape_real ]. 1,2: apply T_eq. Qed.

Lemma ctx_real_tape_C_DH_real : ∅ ⊨ pk_real_tape =ctx= (fill C DH_real) : τ_EG.
Proof. split ; apply (refines_sound approxisRΣ) ; intros ; [ apply: real_tape_C_DH_real | apply: C_DH_real_real_tape ]. 1,2: apply T_eq. Qed.

Lemma ctx_C_DH_rand_rand_tape : ∅ ⊨ (fill C DH_rand) =ctx= pk_rand_tape : τ_EG.
Proof. split ; apply (refines_sound approxisRΣ) ; intros ; [ apply: C_DH_rand_rand_tape | apply: rand_tape_C_DH_rand ]. 1,2: apply T_eq. Qed.

Lemma ctx_rand_tape_rand : ∅ ⊨ pk_rand_tape =ctx= pk_rand : τ_EG.
Proof. split ; apply (refines_sound approxisRΣ) ; intros ; [ apply: rand_tape_rand | apply: rand_rand_tape ]. 1,2: apply T_eq. Qed.

Lemma ctx_real_C_DH_real : ∅ ⊨ pk_real =ctx= (fill C DH_real) : τ_EG.
Proof. eapply ctx_equiv_transitive ; [ apply: ctx_real_real_tape | apply: ctx_real_tape_C_DH_real ]. Qed.

Lemma ctx_C_DH_rand_rand : ∅ ⊨ (fill C DH_rand) =ctx= pk_rand : τ_EG.
Proof. eapply ctx_equiv_transitive ; [ apply: ctx_C_DH_rand_rand_tape | apply: ctx_rand_tape_rand ]. Qed.

Theorem ElGamal_DH_secure :
  forall (A : val), (⊢ᵥ A : (τ_EG → TBool)) ->
  let AC := (λ:"v", A (fill C "v"))%E in
  (advantage A pk_real pk_rand #true <= advantage AC DH_real DH_rand #true)%R.
Proof.
  intros ; eapply (advantage_triangle _ _ (fill C DH_real) _ _ 0).
  3: right ; rewrite Rplus_0_l ; eauto.
  2: eapply (advantage_triangle _ _ (fill C DH_rand) _ _ _ 0) ; first last.
  2: rewrite Rplus_0_r ; right ; eauto.
  - right. eapply ctx_advantage. 2: by tychk.
    apply ctx_real_C_DH_real.
  - right. eapply ctx_advantage. 2: by tychk.
    apply ctx_C_DH_rand_rand.
  - simpl. eapply advantage_reduction_ty ; rewrite /eC /DH_real /DH_rand ; tychk => //.
    all: rewrite /rnd/ElGamal.rnd ; apply Subsume_int_nat ; tychk.
Qed.


(* The following lemmas make the unreasonably strong assumption that
   DH_real/rand are contextually equivalent when they really should only be
   assumed to be computationally indistinguishable, but they illustrate how one
   would combine the results in a logic with support for reasoning about
   computational indistinguishability. *)
Lemma ctx_C_DH_real_C_DH_rand :
  (∅ ⊨ DH_real =ctx= DH_rand : τ_DH) →
  (∅ ⊨ (fill C DH_real) =ctx= (fill C DH_rand) : τ_EG).
Proof.
  replace (fill C _) with (fill_ctx [CTX_AppR eC] DH_real) ; auto ;
    replace (fill C _) with (fill_ctx [CTX_AppR eC] DH_rand) => //.
  intros DDH.
  split.
  - eapply ctx_refines_congruence.
    2: apply DDH.
    unfold eC. tychk => //.
  - eapply ctx_refines_congruence.
    2: apply DDH.
    unfold eC. tychk => //.
Qed.

Lemma pk_ots_rnd_ddh (DDH : ∅ ⊨ DH_real =ctx= DH_rand : τ_DH) :
  (∅ ⊨ pk_real =ctx= pk_rand : τ_EG).
Proof.
  eapply ctx_equiv_transitive.
  - apply: ctx_real_C_DH_real.
  - eapply ctx_equiv_transitive.
    + apply: ctx_C_DH_real_C_DH_rand => //.
    + apply: ctx_C_DH_rand_rand.
Qed.

End Ctx.

End ElGamal_alt.
