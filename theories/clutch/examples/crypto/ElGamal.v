(* ElGamal encryption has one-time secrecy against chosen plaintext attack, in
   the real/random paradigm. Following Rosulek's "The Joy of Crypto". *)
From clutch Require Import clutch.
From clutch.prob_lang Require Import advantage.
From clutch.prob_lang.typing Require Import tychk.
From clutch.clutch.examples.crypto Require Import valgroup advantage_laws.
From clutch.clutch.examples.crypto Require ElGamal_bijection.

From mathcomp Require ssrnat.
From mathcomp Require Import zmodp finset ssrbool fingroup.fingroup solvable.cyclic.
Import valgroup_notation.

Set Default Proof Using "Type*".

Section ElGamal.

Context {vg : val_group}.           (* A group on a subset of values. *)
Context {cg : clutch_group_struct}. (* Implementations of the vg group operations *)
Context {vgg : @val_group_generator vg}.   (* G is generated by g. *)
Context {cgg : @clutch_group_generator vg cg vgg}. (* g is well-typed *)

#[local] Notation n := (S n'').
#[local] Definition rnd t := (rand(t) #n)%E.

(* ElGamal public key encryption *)
Definition keygen : expr :=
  λ:<>, let: "sk" := rnd #() in
    let: "pk" := g^"sk" in
    ("sk", "pk").

Definition enc : expr :=
  λ: "pk", λ: "msg",
    let: "b" := rnd #() in
    let: "B" := g^"b" in
    let: "X" := "msg" · ("pk"^"b") in
    ("B", "X").

Definition dec : expr :=
  λ:"sk" "BX",
    let, ("B", "X") := "BX" in
    "X" · ("B"^-"sk").

(* The syntactic type of the Diffie-Hellman game(s). *)
Definition τ_DH := (τG * τG * τG)%ty.

(* The Decisional Diffie Hellman assumption says the following two programs are
   PPT(n) indistinguishable. *)
Definition DH_real : expr :=
  let: "a" := rnd #() in
  let: "b" := rnd #() in
  (g^"a", g^"b", g^("a"*"b")).

Definition DH_rand : expr :=
  let: "a" := rnd #() in
  let: "b" := rnd #() in
  let: "c" := rnd #() in
  (g^"a", g^"b", g^"c").


(* The syntactic type of the ElGamal game(s). *)
Definition τ_EG := (τG * (TInt → () + τG * τG))%ty.

(* Public key OTS-CPA$ security (one-time secrecy chosen plaintext attack -
   real/random) is defined as the indistinguishability of pk_real and
   pk_rnd. *)
(* In the random game, rather than encrypting the message, "query" returns a
   random ciphertext, i.e. two random group elements (B,X). *)
Definition pk_rand : expr :=
  let, ("sk", "pk") := keygen #() in
  let: "count" := ref #0 in
  let: "query" := λ:"msg",
      let:m "msg" := vg_of_int "msg" in
      assert (!"count" = #0) ;;;
      "count" <- #1 ;;
      let: "b" := rnd #() in
      let: "x" := rnd #() in
      let, ("B", "X") := (g^"b", g^"x") in
      ("B", "X") in
  ("pk", "query").

(* The real game instead encrypts the message in "query". Below, we transform
   pk_real into C[DH_real] and C[DH_rnd] into pk_rnd. *)
Definition pk_real : expr :=
  let, ("sk", "pk") := keygen #() in
  let: "count" := ref #0 in
  let: "query" := λ:"msg",
      let:m "msg" := vg_of_int "msg" in
      assert (!"count" = #0) ;;;
      "count" <- #1 ;;
      enc "pk" "msg" in
  ("pk", "query").

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
      let:m "msg" := vg_of_int "msg" in
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
           let:m "msg" := vg_of_int "msg" in
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
      let:m "msg" := vg_of_int "msg" in
      assert (!"count" = #0) ;;;
      "count" <- #1 ;;
      let: "b" := rnd "β" in
      let: "c" := rnd "γ" in
      let: "B" := g^"b" in
      let: "C" := g^"c" in
      let: "X" := "msg" · "C" in
      ("B", "X") in
  ("pk", "query").

(* Finally, we connect pk_rand_tape to pk_rand. For this last step, we
   want to show that multiplying the message with a random group element really
   looks random, i.e. that msg⋅C = msg⋅g^c looks random, just like X = g^x. *)
(* We prove this by showing that multiplying by msg induces a bijection f on the
   set fin (S n) we sampled x from: Since msg = g^k for some unique k, msg has
   inverse g^(-k), i.e. we define f(c) := k+c (the inverse is obviously given
   by (λ c, c-k)). Let msg⋅g^c = g^k⋅g^c = g^(k+c). Let x = f(c) be sampled along
   the bijection f. Then g^x = g^f(c) = g^(c+k), as required. *)
(* Since we need to know the value of msg, we cannot combine this game-hop with
   the previous one: in C_DH_rand, c is sampled before msg is known. *)

Section LogRel.

Context `{!clutchRGS Σ}.
Context {G : clutch_group (vg:=vg) (cg:=cg)}. (* cg satisfies the group laws. *)
Context {Δ : listO (lrelC Σ)}.

#[local] Notation T := (interp τG Δ).

(* The semantic type of the Diffie-Hellman game(s). *)
Definition T_DH := Eval cbn in (interp τ_DH Δ).

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

Lemma real_real_tape : ⊢ refines top pk_real pk_real_tape T_EG.
Proof with rel_red.
  rel_red. rel_couple_UU...
  inv_mk (βₛ ↪ₛ (n;[]) ∗ (count ↦ #0 ∗ countₛ ↦ₛ #0) ∨ (count ↦ #1 ∗ countₛ ↦ₛ #1) )%I "#Hinv"...
  rel_vals ; iIntros "!>" (??) "[%v[->->]]"...
  rel_bind_l (vg_of_int _) ; rel_bind_r (vg_of_int _) ; rel_apply refines_bind.
  1: iApply vg_of_int_lrel_G ; iExists _ ; eauto.
  iIntros (??) "#(%_&%_'&[(->&->&->&->)|(->&->&%vmsg&->&->)])"... 1: rel_vals.
  iApply (refines_na_inv with "[-$Hinv]"); [done|].
  iIntros "[>[(β&c&c')|(c&c')] Hclose]"...
  2: inv_cl "[- $Hclose]" ; rel_vals.
  rel_couple_UT "β"...
  inv_cl "[- $Hclose]"... rel_vals.
Qed.

Lemma real_tape_real : ⊢ refines top pk_real_tape pk_real T_EG.
Proof with rel_red.
  rel_red. rel_couple_UU...
  inv_mk (β ↪ (n;[]) ∗ (count ↦ #0 ∗ countₛ ↦ₛ #0) ∨ (count ↦ #1 ∗ countₛ ↦ₛ #1) )%I "#Hinv"...
  rel_vals ; iIntros "!>" (??) "[%v[->->]]"...
  rel_bind_l (vg_of_int _) ; rel_bind_r (vg_of_int _) ; rel_apply refines_bind.
  1: iApply vg_of_int_lrel_G ; iExists _ ; eauto.
  iIntros (??) "#(%_&%_'&[(->&->&->&->)|(->&->&%vmsg&->&->)])"... 1: rel_vals.
  iApply (refines_na_inv with "[-$Hinv]"); [done|].
  iIntros "[>[(β&c&c')|(c&c')] Hclose]"...
  2: inv_cl "[- $Hclose]" ; rel_vals.
  rel_couple_TU "β"...
  inv_cl "[- $Hclose]" ; rel_vals.
Qed.

Lemma real_tape_C_DH_real : ⊢ refines top pk_real_tape C_DH_real T_EG.
Proof with rel_red.
  rewrite /C_DH_real /=. rel_red. rel_couple_UU. ireds.
  rel_couple_TU "β"...
  rewrite -Nat2Z.inj_mul/eC...
  inv_mk ((β ↪ (n;[b]) ∗ count ↦ #0 ∗ countₛ ↦ₛ #0)
          ∨ (count ↦ #1 ∗ countₛ ↦ₛ #1))%I "#Hinv".
  rel_vals ; iIntros "!>" (??) "#(%msg&->&->)"...
  rel_bind_l (vg_of_int _) ; rel_bind_r (vg_of_int _) ; rel_apply refines_bind.
  1: iApply vg_of_int_lrel_G ; iExists _ ; eauto.
  iIntros (??) "#(%_1&%_2&[(->&->&->&->)|(->&->&%vmsg&->&->)])"... 1: rel_vals.
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "[>[(β&cnt&cnt')|(c&c')] Hclose]"...
  2: by (inv_cl "[- $Hclose]" ; rel_vals).
  inv_cl "[- $Hclose]"...
  rewrite -expgM -ssrnat.multE. rel_vals.
Qed.

Lemma C_DH_real_real_tape : ⊢ refines top C_DH_real pk_real_tape T_EG.
Proof with rel_red.
  rewrite /C_DH_real /=. rel_red. rel_couple_UU. ireds.
  rel_couple_UT "βₛ"...
  rewrite -Nat2Z.inj_mul/eC...
  inv_mk ((βₛ ↪ₛ (n;[b]) ∗ count ↦ #0 ∗ countₛ ↦ₛ #0)
          ∨ (count ↦ #1 ∗ countₛ ↦ₛ #1))%I "#Hinv".
  rel_vals ; iIntros "!>" (??) "#(%msg&->&->)"...
  rel_bind_l (vg_of_int _) ; rel_bind_r (vg_of_int _) ; rel_apply refines_bind.
  1: iApply vg_of_int_lrel_G ; iExists _ ; eauto.
  iIntros (??) "#(%_1&%_2&[(->&->&->&->)|(->&->&%vmsg&->&->)])"... 1: rel_vals.
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "[>[(β&cnt&cnt')|(c&c')] Hclose]"...
  2: by (inv_cl "[- $Hclose]" ; rel_vals).
  inv_cl "[- $Hclose]"...
  rewrite -expgM -ssrnat.multE. rel_vals.
Qed.

(* This assumption is too strong in this generality, since it does not mention
   PPT indistinguishability and assumes a logical instead of contextual
   refinement. *)
Definition DDH_ref := ⊢ refines top DH_real DH_rand T_DH.
(* If we do make this assumption though, we may prove the following refinement. *)
Lemma DDH_C_DH_real_C_DH_rand (DDH : DDH_ref) : ⊢ refines top C_DH_real C_DH_rand T_EG.
Proof with rel_red.
  rewrite /C_DH_real /C_DH_rand.
  rel_bind_l DH_real. rel_bind_r DH_rand.
  rel_apply refines_app. 2: iApply DDH.
  replace (T_DH → T_EG)%lrel with (interp (τ_DH → τ_EG)%ty Δ) by auto.
  iApply refines_typed. unfold eC. tychk => //.
Qed.

Lemma C_DH_rand_rand_tape : ⊢ refines top C_DH_rand pk_rand_tape T_EG.
Proof with rel_red.
  rewrite /C_DH_rand/C/eC /=. rel_red. rel_couple_UU...
  rel_couple_UT "βₛ"...
  rel_couple_UT "γₛ"...
  inv_mk ((βₛ ↪ₛ (n;[b]) ∗ γₛ ↪ₛ (n;[c]) ∗ count ↦ #0 ∗ countₛ ↦ₛ #0)
          ∨ (count ↦ #1 ∗ countₛ ↦ₛ #1))%I "#Hinv".
  rel_vals ; iIntros "!>" (??) "#(%msg&->&->)"...
  rel_bind_l (vg_of_int _) ; rel_bind_r (vg_of_int _) ; rel_apply refines_bind ;
    [iApply vg_of_int_lrel_G ; iExists _ ; eauto|].
  iIntros (??) "#(%_1&%_2&[(->&->&->&->)|(->&->&%vmsg&->&->)])"... 1: rel_vals.
  iApply (refines_na_inv with "[$Hinv]") => //.
  iIntros "[>[(β'&γ'&cnt&cnt')|(cnt&cnt')] Hclose]"...
  all: inv_cl "[- $Hclose]" ; rel_vals.
Qed.

Lemma rand_tape_C_DH_rand : ⊢ refines top pk_rand_tape C_DH_rand T_EG.
Proof with rel_red.
  rewrite /C_DH_rand/C/eC /=. rel_red. rel_couple_UU. iredrs.
  rel_couple_TU "β". iredrs.
  rel_couple_TU "γ"...
  inv_mk ((β ↪ (n;[b]) ∗ γ ↪ (n;[c]) ∗ count ↦ #0 ∗ countₛ ↦ₛ #0)
          ∨ (count ↦ #1 ∗ countₛ ↦ₛ #1))%I "#Hinv".
  rel_vals ; iIntros "!>" (??) "#(%msg&->&->)"...
  rel_bind_l (vg_of_int _) ; rel_bind_r (vg_of_int _) ; rel_apply refines_bind
  ; [iApply vg_of_int_lrel_G ; iExists _ ; eauto|].
  iIntros (??) "#(%_1&%_2&[(->&->&->&->)|(->&->&%vmsg&->&->)])"... 1: rel_vals.
  iApply (refines_na_inv with "[$Hinv]") => //.
  iIntros "[>[(β'&γ'&cnt&cnt')|(cnt&cnt')] Hclose]"...
  all: inv_cl "[- $Hclose]" ; rel_vals.
Qed.

Lemma rand_tape_rand : ⊢ refines top pk_rand_tape pk_rand T_EG.
Proof with rel_red.
  rel_red. rel_couple_UU...
  inv_mk ((β ↪ (n;[]) ∗ γ ↪ (n;[]) ∗ count ↦ #0 ∗ countₛ ↦ₛ #0)
          ∨ (count ↦ #1 ∗ countₛ ↦ₛ #1))%I "#Hinv".
  rel_vals ; iIntros "!>" (??) "#(%msg&->&->)"...
  rel_bind_l (vg_of_int _) ; rel_bind_r (vg_of_int _) ; rel_apply refines_bind
  ; [iApply vg_of_int_lrel_G ; iExists _ ; eauto|].
  iIntros (??) "#(%_1&%_2&[(->&->&->&->)|(->&->&%vmsg&->&->)])"... 1: rel_vals.
  iApply (refines_na_inv with "[-$Hinv]") => //.
  iIntros "[>[(β&γ&cnt&cnt')|(cnt&cnt')] Hclose]"...
  2: by (inv_cl "[-$Hclose]" ; rel_vals).
  rel_couple_TU "β"...
  (* Rewrite msg into g^k_msg for some k_msg. *)
  destruct (log_g vmsg) as [k_msg ->].
  (* Sample c on the left, and ((k_msg + c) mod (S n)) on the right. *)
  pose (k_msg_plus := ElGamal_bijection.bij_fin.f n'' k_msg).
  unshelve rel_couple_TU "γ" k_msg_plus...
  inv_cl "[- $Hclose]"...
  rewrite -expgD -ssrnat.plusE.
  assert ((g ^+ (k_msg + x)) = (g ^+ k_msg_plus x))%g as heq.
  { clear. rewrite fin_to_nat_to_fin /= -ssrnat.plusE /Zp_trunc /=.
    pose proof (e := eq_sym (expg_mod_order g (k_msg+x))).
    rewrite g_nontriv in e. exact e.
  }
  rewrite -heq. rel_vals.
Qed.

Lemma rand_rand_tape : ⊢ refines top pk_rand pk_rand_tape T_EG.
Proof with rel_red.
  rel_red. rel_couple_UU...
  inv_mk ((βₛ ↪ₛ (n;[]) ∗ γₛ ↪ₛ (n;[]) ∗ count ↦ #0 ∗ countₛ ↦ₛ #0)
          ∨ (count ↦ #1 ∗ countₛ ↦ₛ #1))%I "#Hinv"...
  rel_vals ; iIntros "!>" (??) "#(%msg&->&->)"...
  rel_bind_l (vg_of_int _) ; rel_bind_r (vg_of_int _) ; rel_apply refines_bind
  ; [iApply vg_of_int_lrel_G ; iExists _ ; eauto|].
  iIntros (??) "#(%_1&%_2&[(->&->&->&->)|(->&->&%vmsg&->&->)])"... 1: rel_vals.
  iApply (refines_na_inv with "[-$Hinv]") => //.
  iIntros "[>[(βₛ&γₛ&count&countₛ)|(count&countₛ)] Hclose]"...
  2: by (inv_cl "[-$Hclose]" ; rel_vals).
  rel_couple_UT "βₛ"...
  (* Rewrite msg into g^k_msg for some k_msg. *)
  destruct (log_g vmsg) as [k_msg ->].
  (* Sample x on the left, and ((-x + k_msg) mod (S n)) on the right. *)
  pose (minus_k_msg_plus := ElGamal_bijection.bij_fin.g n'' k_msg).
  unshelve rel_couple_UT "γₛ" minus_k_msg_plus...
  inv_cl "[- $Hclose]"...
  rewrite -expgD -ssrnat.plusE.
  assert ((g ^+ x) = (g ^+ (k_msg + minus_k_msg_plus x)))%g as heq.
  { clear. rewrite fin_to_nat_to_fin /= /Zp_trunc /=.
    epose proof (e := (expg_mod_order g)).
    rewrite g_nontriv in e.
    rewrite -[in LHS]e -{}[in RHS]e.
    f_equal.
    rewrite div.modnDmr ssrnat.addnC -ssrnat.addnA div.modnDml.
    rewrite [ssrnat.addn x _]ssrnat.addnC ssrnat.addnA.
    rewrite ssrnat.subnK.
    - rewrite div.modnDl. reflexivity.
    - apply /ssrnat.leP. move : (fin_to_nat_lt k_msg). lia.
  }
  rewrite -heq. rel_vals.
Qed.

(* Decryption is left inverse to encryption. We only consider valid messages,
   i.e. integers that decode to a group element (in practice, this means that
   the integer has to be smaller than the group order). *)
Lemma ElGamal_correct :
  ⊢ refines top
      (let, ("sk", "pk") := keygen #() in
       λ:"msg",
         let:m "msg" := vg_of_int "msg" in
         let: "c" := enc "pk" "msg" in
         let: "vmsg" := dec "sk" "c" in
         SOME ("vmsg"))
      (λ:"msg",
         let:m "vmsg" := vg_of_int "msg" in
         SOME ("vmsg"))
      (lrel_int → () + lrel_G).
Proof with rel_red.
  rel_red. rel_randU_l...
  rel_arrow_val ; iIntros (??) "#(%msg&->&->)"...
  rel_bind_l (vg_of_int _) ; rel_bind_r (vg_of_int _) ; rel_apply refines_bind.
  1: iApply vg_of_int_lrel_G ; iExists _ ; eauto.
  iIntros (??) "#(%_1&%_2&[(->&->&->&->)|(->&->&%vmsg&->&->)])"... 1: rel_vals.
  rel_randU_l...
  rewrite -?expgM -ssrnat.multE -mulgA Nat.mul_comm mulgV mulg1.
  rel_vals.
Qed.

End LogRel.

Section Ctx.

Context {G : forall `{!clutchRGS Σ}, clutch_group (vg:=vg) (cg:=cg)}.

Lemma ctx_real_real_tape : ∅ ⊨ pk_real =ctx= pk_real_tape : τ_EG.
Proof. split ; apply (refines_sound clutchRΣ) ; intros ; [ apply: real_real_tape | apply: real_tape_real ]. Qed.

Lemma ctx_real_tape_C_DH_real : ∅ ⊨ pk_real_tape =ctx= (fill C DH_real) : τ_EG.
Proof. split ; apply (refines_sound clutchRΣ) ; intros ; [ apply: real_tape_C_DH_real | apply: C_DH_real_real_tape ]. Qed.

Lemma ctx_C_DH_rand_rand_tape : ∅ ⊨ (fill C DH_rand) =ctx= pk_rand_tape : τ_EG.
Proof. split ; apply (refines_sound clutchRΣ) ; intros ; [ apply: C_DH_rand_rand_tape | apply: rand_tape_C_DH_rand ]. Qed.

Lemma ctx_rand_tape_rand : ∅ ⊨ pk_rand_tape =ctx= pk_rand : τ_EG.
Proof. split ; apply (refines_sound clutchRΣ) ; intros ; [ apply: rand_tape_rand | apply: rand_rand_tape ]. Qed.

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
    all: rewrite /rnd ; apply Subsume_int_nat ; tychk.
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

End ElGamal.
