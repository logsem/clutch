(* A game based security proof of ElGamal encryption, following Rosulek's "The
   Joy of Crypto". *)

From stdpp Require Import namespaces.
From clutch.rel_logic Require Import model rel_rules rel_tactics adequacy.

From clutch.typing Require Import types contextual_refinement soundness.
From clutch.prelude Require Import base.
From clutch.program_logic Require Import weakestpre.
From clutch.prob_lang Require Import notation lang.
From clutch Require Import clutch lib.flip.
From clutch.examples.crypto Require Import homebrew_group.
Set Default Proof Using "Type*".

Section ElGamal.

Context `{!clutchRGS Σ}.

Context `{EG : !EGroup}.
Let G : group_struct _ := @G _ _ EG.
(* For sanity's sake, this assumption should probably be part of the EGroup
class, even though the definition doesn't require it. *)
Context `{G_group : !@is_group _ G}.

Variable τ : type.
Definition T := interp.interp τ [].
Context (all_typed : (∀ (x : @vt P), ⊢ᵥ x : τ)%ty).

Variable g : G.
Context (g_gen : @is_generator _ G g).
Context (g_typed : (∀ Γ, Γ ⊢ₜ (g : vt) : τ)%ty).

Variable eexp : val.

Context (is_exp_eexp : is_exp (G:=G) eexp).
Context (is_spec_exp_eexp : is_spec_exp (G:=G) eexp).

Definition order : nat := (projT1 (g_gen g)).
Let n := order.
Variable p0 : P #0.
Variable p1 : P #1.
Definition g0 : @vt P := exist _ #0 p0.
Definition g1 : @vt P := exist _ #1 p1.

(* A group should come with... *)
(* An integer indicating its order, so that we can sample an exponent. *)
(* Parameter n : nat. *)
(* A type! *)
(* Parameter τ : type. *)
(* Definition τ := TBool. *)
(* A generator *)
(* Parameter g : val. *)
Parameter gt : ⊢ REL evt g << evt g : interp.interp τ [].
(* Multiplication *)
(* Parameter mult : val. *)
(* Parameter mt : ⊢ REL mult << mult : τ → τ → τ. *)
Context (mult_typed : ∀ Γ, Γ ⊢ₜ vmult : (τ → τ → τ)%ty).
(* Inverse *)
(* Parameter inv : val. *)
(* Parameter it : ⊢ REL inv << inv : τ → τ. *)
(* An implementation of exponentiation (might do something smarter than just
   iterating multiplication). *)
(* Parameter exp : val. *)
Context (eexp_typed : ⊢ REL eexp << eexp : interp.interp τ [] → lrel_int → interp.interp τ []).

(* Parameter modulo : expr. *)
Let modulo := emodulo.

Let eexpb : expr := λ:"b" "x", eexp "b" (if: "x" then #1 else #0).

#[local] Infix "^^" := eexp (at level 35) : expr_scope.
#[local] Infix "**" := vmult (at level 40) : expr_scope.
#[local] Notation "--" := vinv : expr_scope.
#[local] Infix "%%" := modulo (at level 65) : expr_scope.

Definition rnd t : expr := let: "b" := flipL t in if: "b" then #1 else #0.

(* We'll need to know some laws about the group (TBD). *)
(* Hypothesis hexp : {{{True}}} of_val exp {{{v, RET (#v); False}}}. *)

(* ElGamal public key encryption *)
(* For now, without security parameter (order of the group). *)
Definition keygen : expr :=
  λ:<>, let: "sk" := rnd #() in
    let: "pk" := (evt g) ^^ "sk" in
    ("pk", "sk").

Definition enc : expr :=
  λ: "pk", λ: "m",
    let: "b" := rnd #() in
    let: "B" := (evt g)^^"b" in
    ("B", "m" ** "pk"^^"b").

Definition dec : expr :=
  λ:"sk" "BX",
    let: "B" := Fst "BX" in
    let: "X" := Snd "BX" in
    "X" ** ("B" ^^ (-- "sk")).

Let ge := evt g.

(* The Decisional Diffie Hellman assumption says the following two programs are
   PPT indistinguishable. *)
(* NB: Of course PPT (and thus PPT indistinguishability) only makes sense if we
   have a security parameter, see above. *)
Definition DH_real : expr :=
  λ:<>,
    let: "a" := rnd #() in
    let: "b" := rnd #() in
    (ge^^"a", (ge^^"b", ge^^("a" * "b"))).

Definition DH_rnd : expr :=
  λ:<>,
    let: "a" := rnd #() in
    let: "b" := rnd #() in
    let: "c" := rnd #() in
    (ge^^"a", (ge^^"b", ge^^"c")).

(* false assumption: only holds for PPT contexts *)
Parameter DDH : ⊢ REL DH_real << DH_rnd : lrel_bool → lrel_bool.
Parameter DDH' : ⊢ REL DH_rnd << DH_real : lrel_bool → lrel_bool.

Definition DH_real_lbl : expr :=
  let: "α" := allocB in
  let: "β" := allocB in
  λ:<>,
    let: "a" := rnd "α" in
    let: "b" := rnd "β" in
    (ge^^"a", (ge^^"b", ge^^("a" * "b"))).

Definition DH_rnd_lbl : expr :=
  let: "α" := allocB in
  let: "β" := allocB in
  let: "γ" := allocB in
  λ:<>,
    let: "a" := rnd "α" in
    let: "b" := rnd "β" in
    let: "c" := rnd "γ" in
    (ge^^"a", (ge^^"b", ge^^"c")).

Definition pkN := nroot.@"pks".

Definition is_exp' (eexp : val) := ∀ (b : vt) (x : Z),
    {{{ True }}}
      eexp b (#x)
    {{{ v, RET v; ⌜v = vvt (@exp _ G b x)⌝ }}}.

Lemma foo (b : bool) x y :
  {{{True}}}
    if: #b then #x else #y
  {{{v, RET #v; ⌜v = if b then x else y⌝}}}.
Proof.
  iIntros (?) "_ hlog".
  destruct b ; wp_pure ; iApply "hlog" ; done.
Qed.

Lemma bar (b : bool) x y :
  ∀ K, (refines_right K (if: #b then #x else #y)
        ={⊤}=∗
               refines_right K #(if b then x else y)).
Proof.
  iIntros (k) "hlog".
  destruct b ; by tp_pure.
Qed.

Lemma baz E K (b : bool) (x y : Z) t (A : lrel Σ) :
  (REL
     ectxi_language.fill K (of_val #(LitInt (if b then x else y))) <<
     t
     @ E : A)
  -∗ REL
     ectxi_language.fill K (if: #b then #x else #y) <<
     t
     @ E : A.
Proof.
  iIntros "hlog".
  rel_apply_l refines_wp_l.
  epose proof foo.
  wp_apply (H _ _ _) => //.
  iIntros (v) "->".
  rel_pures_l.
  destruct b ; done.
Qed.

Lemma qux E K (b : bool) (x y : Z) t (A : lrel Σ) :
  (REL
     t <<
     ectxi_language.fill K (of_val #(LitInt (if b then x else y)))
     @ E : A)
  -∗ REL
     t <<
     ectxi_language.fill K (if: #b then #x else #y)
     @ E : A.
Proof.
  iIntros "hlog".
  rel_apply_r refines_steps_r.
  { iIntros (?). iApply (bar _ _ _). }
  iModIntro. rel_pures_r.
  destruct b.
  all: done.
Qed.

Lemma refines_exp E K A (b : vt) (p : Z) t (h_exp : is_exp (G:=G) eexp) :
  (REL ectxi_language.fill K (evt (@exp vt G b p)) << t @ E : A)
    ⊢ REL ectxi_language.fill K (b ^^ #p) << t @ E : A.
Proof.
  clear -h_exp.
  unfold is_exp in h_exp.
  iIntros "H".
  rel_apply_l refines_wp_l.
  iApply (h_exp b p) => //.
  iModIntro ; iIntros (v) "->" => //.
Qed.

Lemma refines_exp' E K A (b : vt) (p : Z) t (h_exp : is_exp (G:=G) eexp) :
  (REL t << ectxi_language.fill K (evt (@exp vt G b p)) @ E : A)
    ⊢ REL t << ectxi_language.fill K (b ^^ #p) @ E : A.
Proof.
  iIntros "H".
  rel_apply_r refines_steps_r => //.
  iIntros (?). iApply (is_spec_exp_eexp _ _ _).
Qed.

Lemma DDH_real_real_lbl : ⊢ REL DH_real << DH_real_lbl
    : lrel_unit → (T * (T * T)).
Proof with rel_pures_l ; rel_pures_r.
  rewrite /DH_real /DH_real_lbl.
  rel_alloctape_r α as "α".
  rel_alloctape_r β as "β".
  iApply (refines_na_alloc (α ↪ₛB [] ∗ β ↪ₛB []) pkN).
  iSplitL. { iFrame. }
  iIntros "#Hinv".
  rel_arrow_val.
  iIntros (?? (-> & ->))...
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "[>[α β] Hclose]". unfold rnd.
  rel_apply (refines_couple_flip_tape with "[-$α]").
  iIntros "!>" (a) "α". rel_flipL_r...
  rel_apply_l baz...
  rel_apply_r qux...
  rel_apply (refines_couple_flip_tape with "[-$β]").
  iIntros "!>" (b) "β". rel_flipL_r...
  iApply (refines_na_close with "[- $Hclose]").
  iSplitL. 1: iFrame.
  rel_apply_l baz...
  rel_apply_r qux...
  rel_apply compatibility.refines_pair ; [| rel_apply compatibility.refines_pair].
  - rel_apply compatibility.refines_app.
    1: rel_apply compatibility.refines_app.
    1: iApply eexp_typed.
    1: iApply fundamental.refines_typed ; apply g_typed.
    destruct a ; rel_values.
  - rel_apply compatibility.refines_app.
    1: rel_apply compatibility.refines_app.
    1: iApply eexp_typed.
    1: iApply fundamental.refines_typed ; apply g_typed.
    destruct b ; rel_values.
  - rel_apply compatibility.refines_app.
    1: rel_apply compatibility.refines_app.
    1: iApply eexp_typed.
    1: iApply fundamental.refines_typed ; apply g_typed.
    destruct a,b...
    all: rel_values.
Qed.

(* Lemma DDH'_lbl : ⊢ REL DH_rnd << DH_real : lrel_unit → (T * (T * T)). *)

Lemma DDH_lbl : ⊢ REL DH_real_lbl << DH_rnd_lbl : lrel_unit → (T * (T * T)).
Admitted.

Definition abort : expr := (rec: "f" "x" := "f" "x") #().
Definition assert b : expr := if: b then #() else abort.

(* public key OTS-CPA$ security, for ElGamal
   (one-time secrecy chosen plaintext attack - real/random) *)
Definition pk_ots_rnd_real : expr :=
  (* "a" and "b" should be rnd n instead of flip #() *)
  let: "pk_sk" := keygen #() in
  let: "pk" := Fst "pk_sk" in
  let: "sk" := Snd "pk_sk" in
  let: "count" := ref #0 in

  let: "getpk" := λ:<>, "pk" in

  let: "query" := λ:"m",
      assert (!"count" = #0) ;;
      "count" <- #1 ;;
      enc "pk" "m" in
  ("getpk", "query").

(* unfold definitions and label the flips *)
Definition pk_ots_rnd_real_lbl : expr :=
  let: "α" := allocB in
  let: "β" := allocB in
  let: "pk_sk" :=
    let: "sk" := rnd "α" in
    let: "pk" := ge ^^ "sk" in
    ("pk", "sk") in
  let: "pk" := Fst "pk_sk" in
  let: "sk" := Snd "pk_sk" in
  let: "count" := ref #0 in

  let: "getpk" := λ:<>, "pk" in

  let: "query" := λ:"m",
      assert (!"count" = #0) ;;
      "count" <- #1 ;;
      let: "b" := rnd "β" in
      let: "B" := ge^^"b" in
      ("B", "m" ** "pk"^^"b") in
  ("getpk", "query").

Lemma pk_ots_rnd_real_real_lbl :
  ⊢ REL pk_ots_rnd_real << pk_ots_rnd_real_lbl :
    lrel_prod (lrel_unit → T) (T → lrel_prod T T).
Proof with rel_pures_l ; rel_pures_r.
  rewrite /pk_ots_rnd_real /pk_ots_rnd_real_lbl.
  rewrite /keygen /enc /rnd...
  rel_allocBtape_r α as "α"...
  rel_allocBtape_r β as "β"...
  rel_apply (refines_couple_flip_tape with "[- $α]").
  iIntros "!>" (sk) "α"...
  rel_flipL_r...
  rel_apply_l baz...
  rel_apply_r qux...
  rel_apply_r (refines_exp' _ _ _ _ _ _ is_exp_eexp) => //.
  rel_apply_l (refines_exp _ _ _ _ _ _ is_exp_eexp) => //.
  unfold evt, vvt. simpl...
  rel_alloc_l c as "c".
  rel_alloc_r c' as "c'".
  do 8 rel_pure_l.
  do 8 rel_pure_r.
  rel_apply compatibility.refines_pair.
  1:{ rel_arrow_val.
      iIntros (?? (-> & ->))...
      iApply fundamental.refines_typed.
      constructor.
      apply all_typed.
  }

  set (P := (α ↪ₛB [] ∗ β ↪ₛB [] ∗ (c ↦ #0 ∗ c' ↦ₛ #0)
             ∨ (c ↦ #1 ∗ c' ↦ₛ #1) )%I).
    iApply (refines_na_alloc P pkN).
    iSplitL.
    { iFrame. iLeft. iFrame. }
    iIntros "#Hinv".
    rel_arrow_val.
    iIntros (??)...
    iIntros "#Hv1v2"...
    iApply (refines_na_inv with "[-$Hinv]"); [done|].
    iIntros "[>[(α&β&c&c')|(c&c')] Hclose]".
    - rel_load_r ; rel_load_l...
      rel_store_l ; rel_store_r...
      rel_apply (refines_couple_flip_tape with "[-$β]").
      iIntros "!>" (b) "β"...
      rel_flipL_r...
  rel_apply_l baz...
  rel_apply_r qux...
  rel_bind_l (_ ^^ _)%E.
  rel_apply_l (refines_exp _ _ _ _ _ _ is_exp_eexp) => //.
  rel_apply_r (refines_exp' _ _ _ _ _ _ is_exp_eexp) => //.
  unfold evt, vvt. simpl...

      iApply (refines_na_close with "[- $Hclose]").
      iSplitL.
      { iRight. iModIntro. iFrame. }
      rel_apply compatibility.refines_pair.
      + iApply fundamental.refines_typed.
        constructor ; apply all_typed.
      + unshelve rel_apply compatibility.refines_app. 1: exact T.
        1: { unshelve rel_apply compatibility.refines_app ; [exact T|..].
             - replace (T → T → T)%lrel with (interp.interp (τ → τ → τ) []) => //.
               iApply fundamental.refines_typed. apply mult_typed.
             - rel_values.
        }
  rel_apply_l (refines_exp _ _ _ _ _ _ is_exp_eexp) => //.
  rel_apply_r (refines_exp' _ _ _ _ _ _ is_exp_eexp) => //.
  unfold evt, vvt. simpl...

      iApply fundamental.refines_typed.
      constructor ; apply all_typed.

    - rel_load_l ; rel_load_r...
      iApply (refines_na_close with "[- $Hclose]").
      iSplitL.
      { iRight ; iFrame. }
      iLöb as "H".
      rel_rec_l.
      iExact "H".
Qed.


(* Unfold the definitions and move sampling of "b" to the initialisation. Only
   equivalent because it "query" gets called only once. *)
Definition pk_ots_rnd_0 : expr :=
  let: "α" := allocB in
  let: "β" := allocB in
  let: "pk_sk" :=
    let: "sk" := rnd "α" in
    let: "pk" := ge ^^ "sk" in
    ("pk", "sk") in
  let: "A" := Fst "pk_sk" in
  let: "a" := Snd "pk_sk" in
  let: "b" := rnd "β" in
  let: "B" := ge^^"b" in
  let: "C" := "A"^^"b" in
  let: "count" := ref #0 in

  let: "getpk" := λ:<>, "A" in

  let: "query" := λ:"m",
      assert (!"count" = #0) ;;
      "count" <- #1 ;;
      ("B", "m" ** "C") in
  ("getpk", "query").

Lemma pk_ots_rnd_real_lbl_0 :
  ⊢ REL pk_ots_rnd_real_lbl << pk_ots_rnd_0 :
    lrel_prod (lrel_unit → T) (T → lrel_prod T T).
Proof with rel_pures_l ; rel_pures_r.
  rewrite /pk_ots_rnd_0 /pk_ots_rnd_real_lbl...
  rel_allocBtape_l α as "α"...
  rel_allocBtape_l β as "β"...
  rel_allocBtape_r α' as "α'"...
  rel_allocBtape_r β' as "β'"...
  rel_apply (refines_couple_bool_tape_tape with "[- $α $α']") => //.
  iIntros (sk) "[α' α]"...
  rel_flipL_l ; rel_flipL_r...

  rel_apply_l baz...
  rel_apply_r qux...
  rel_apply_r (refines_exp' _ _ _ _ _ _ is_exp_eexp) => //.
  rel_apply_l (refines_exp _ _ _ _ _ _ is_exp_eexp) => //.
  unfold evt, vvt. simpl...

  rel_apply (refines_couple_bool_tape_tape with "[- $β $β']") => //.
  iIntros (b) "[β' β]"...
  rel_flipL_r...
  rel_apply_r qux...
  rel_apply_r (refines_exp' _ _ _ _ _ _ is_exp_eexp) => //.
  unfold evt, vvt. simpl...
  rel_apply_r (refines_exp' _ _ _ _ _ _ is_exp_eexp) => //.
  unfold evt, vvt. simpl...

  rel_alloc_l c as "c".
  rel_alloc_r c' as "c'".
  do 8 rel_pure_l.
  do 8 rel_pure_r.
  rel_apply compatibility.refines_pair.
  1: { rel_arrow_val. iIntros (?? (-> & ->))...
       iApply fundamental.refines_typed.
       constructor ; apply all_typed. }

  set (P := (( (β ↪B [b] ∗ β' ↪ₛB [] ∗ c ↦ #0 ∗ c' ↦ₛ #0))
             ∨ (c ↦ #1 ∗ c' ↦ₛ #1))%I).
    iApply (refines_na_alloc P pkN).
    iSplitL.
    { iFrame. iLeft. iFrame. }
    iIntros "#Hinv".
    rel_arrow_val.
    iIntros (??) "#Hv1v2"...
    iApply (refines_na_inv with "[$Hinv]"); [done|].
    iIntros "[>[(β&β'&c&c')|(c&c')] Hclose]".
    - rel_load_r ; rel_load_l...
      rel_store_l ; rel_store_r...
      rel_flipL_l...
      rel_apply_l baz...
      rel_apply_l (refines_exp _ _ _ _ _ _ is_exp_eexp) => //.
      unfold evt, vvt. simpl...
      iApply (refines_na_close with "[- $Hclose]").
      iSplitL.
      { iRight. iModIntro. iFrame. }
      rel_apply compatibility.refines_pair.
      + iApply fundamental.refines_typed.
        constructor ; apply all_typed.
      + unshelve rel_apply compatibility.refines_app. 1: exact T.
        1: { unshelve rel_apply compatibility.refines_app ; [exact T|..].
             - replace (T → T → T)%lrel with (interp.interp (τ → τ → τ) []) => //.
               iApply fundamental.refines_typed. apply mult_typed.
             - rel_values.
        }
  rel_apply_l (refines_exp _ _ _ _ _ _ is_exp_eexp) => //.
  unfold evt, vvt. simpl...

      iApply fundamental.refines_typed.
      constructor ; apply all_typed.
    - rel_load_l ; rel_load_r...
      iApply (refines_na_close with "[- $Hclose]").
      iSplitL.
      { iRight ; iFrame. }
      iLöb as "H".
      rel_rec_l.
      iExact "H".
Qed.


(* Pull out DH_real. *)
Definition pk_ots_rnd_1 : expr :=
  let: "dhquery" :=
    let: "α" := allocB in
    let: "β" := allocB in
    λ:<>,
      let: "a" := rnd "α" in
      let: "b" := rnd "β" in
      (ge ^^ "a", (ge ^^ "b", ge ^^ ("a" * "b"))) in
  let: "ABC" := "dhquery" #() in
  let: "A" := Fst "ABC" in
  let: "B" := Fst (Snd "ABC") in
  let: "C" := Snd (Snd "ABC") in
  let: "count" := ref #0 in

  let: "getpk" := λ:<>, "A" in

  let: "query" := λ:"m",
      assert (!"count" = #0) ;;
      "count" <- #1 ;;
      ("B", "m" ** "C") in
  ("getpk", "query").

Lemma pk_ots_rnd_0_1 :
  ⊢ REL pk_ots_rnd_0 << pk_ots_rnd_1 : (() → T) * (T → T * T).
Proof with unfold evt, vvt ; rel_pures_l ; rel_pures_r.
  rewrite /pk_ots_rnd_0 /pk_ots_rnd_1...
  rel_allocBtape_l α as "α"...
  rel_allocBtape_l β as "β"...
  rel_allocBtape_r α' as "α'"...
  rel_allocBtape_r β' as "β'"...
  rel_apply (refines_couple_bool_tape_tape with "[- $α $α']") => //.
  iIntros (sk) "[α' α]"...
  rel_flipL_l ; rel_flipL_r...
  rel_apply_l baz ; rel_apply_r qux...
  rel_apply_l (refines_exp _ _ _ _ _ _ is_exp_eexp) => //...
  rel_apply (refines_couple_bool_tape_tape with "[- $β $β']") => //...
  iIntros (b) "[β' β]"...
  rel_flipL_l ; rel_flipL_r...
  rel_apply_l baz ; rel_apply_r qux...
  rel_apply_l (refines_exp _ _ _ _ _ _ is_exp_eexp) => //.
  rel_apply_r (refines_exp' _ _ _ _ _ _ is_exp_eexp) => //...
  rel_apply_l (refines_exp _ _ _ _ _ _ is_exp_eexp) => //.
  rel_apply_r (refines_exp' _ _ _ _ _ _ is_exp_eexp) => //...
  rel_apply_r (refines_exp' _ _ _ _ _ _ is_exp_eexp) => //...
  rel_alloc_l c as "c".
  rel_alloc_r c' as "c'".
  do 8 rel_pure_l.
  do 8 rel_pure_r.
  rel_apply compatibility.refines_pair.
  1: { rel_arrow_val. iIntros (?? (-> & ->))...
       iApply fundamental.refines_typed.
       constructor ; apply all_typed. }
  iApply (refines_na_alloc (∃ v, c ↦ #v ∗ c' ↦ₛ #v) pkN).
  iSplitL ; [ iExists _ ; iFrame|iIntros "#Hinv"].
  rel_arrow_val ; iIntros (??) "#Hv1v2"...
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "[>(%v&c&c') Hclose]".
  rel_load_l ; rel_load_r...
  destruct (bool_decide (#v = #0)%V)...
  - rel_store_l ; rel_store_r...
    iApply (refines_na_close with "[- $Hclose]").
    iSplitL ; [ iExists _ ; iFrame|].
    rel_apply compatibility.refines_pair.
    + iApply (fundamental.refines_typed _ _ _) ; constructor ; apply all_typed.
    + unshelve rel_apply compatibility.refines_app. 1: exact T.
        1: { unshelve rel_apply compatibility.refines_app ; [exact T|..].
             - replace (T → T → T)%lrel with (interp.interp (τ → τ → τ) []) => //.
               iApply fundamental.refines_typed. apply mult_typed.
             - rel_values.
        }
        (* We need to prove that (g^sk)^b = g^(sk*b). We should prove this in
        general as a lemma about exponentiation, but for now we'll simply
        compute by considering all 4 possible pairs (sk,b). *)
        replace
          (@exp _ G (@exp _ G g (if sk then 1%Z else 0%Z)) (if b then 1%Z else 0%Z))
          with
          (@exp _ G g ((if sk then 1%Z else 0%Z) * (if b then 1%Z else 0%Z))).
        1: iApply fundamental.refines_typed ; constructor ; apply all_typed.
        destruct G_group.
        destruct b,sk => // ; try by rewrite right_id.
        all: by compute.
  - iApply (refines_na_close with "[- $Hclose]").
    iSplitL ; [ iExists _ ; iFrame|].
    iLöb as "H".
    rel_rec_l.
    iExact "H".
Qed.

(* Swap in DH_rnd. *)
Definition pk_ots_rnd_2 : expr :=
  let: "dhquery" :=
    let: "α" := allocB in
    let: "β" := allocB in
    let: "γ" := allocB in
    λ:<>,
      let: "a" := rnd "α" in
      let: "b" := rnd "β" in
      let: "c" := rnd "γ" in
      (ge ^^ "a", (ge ^^ "b", ge ^^ "c")) in
  let: "ABC" := "dhquery" #() in
  let: "A" := Fst "ABC" in
  let: "B" := Fst (Snd "ABC") in
  let: "C" := Snd (Snd "ABC") in
  let: "count" := ref #0 in

  let: "getpk" := λ:<>, "A" in

  let: "query" := λ:"m",
      assert (!"count" = #0) ;;
      "count" <- #1 ;;
      ("B", "m" ** "C") in
  ("getpk", "query").

Lemma pk_ots_rnd_1_2 :
  ⊢ REL pk_ots_rnd_1 << pk_ots_rnd_2 : (() → T) * (T → T * T).
Proof
  with unfold evt, vvt ; rel_pures_l ; rel_pures_r
  using
  EG G_group all_typed eexp eexp_typed eexpb g g_gen g_typed ge
  is_exp_eexp is_spec_exp_eexp modulo mult_typed n p0 p1 clutchRGS0 Σ τ.
  rewrite /pk_ots_rnd_1 /pk_ots_rnd_2...
  fold DH_real_lbl.
  fold DH_rnd_lbl.
  rel_apply compatibility.refines_app.
  2: { iApply DDH_lbl. }
  replace ((() → T * (T * T)) → (() → T) * (T → T * T))%lrel
    with (interp.interp
            ((() → (τ * (τ * τ))) → (() → τ) * (τ → τ * τ))%ty []) by auto.
 iApply fundamental.refines_typed.
 repeat constructor.
 apply (App_typed _ _ _ (τ * (τ * τ))).
 - repeat constructor.
   eapply App_typed.
   2: { eapply Fst_typed. constructor. done. }
   constructor.
   eapply App_typed.
   2: { eapply Fst_typed, Snd_typed. constructor. done. }
   constructor.
   eapply App_typed.
   2: { eapply Snd_typed, Snd_typed. constructor. done. }
   constructor.
   eapply App_typed.
   2: { apply TAlloc. constructor. constructor. }
   constructor.
   eapply App_typed.
   2: { constructor. constructor. reflexivity. }
   constructor.
   eapply App_typed.
   2: { constructor.
        eapply App_typed.
        2: {
          unfold assert, abort.
          repeat constructor.
          econstructor.
          2: repeat constructor.
          constructor.
          eapply App_typed ; repeat constructor.
        }
        constructor.
        eapply (App_typed _ _ _ () (τ * τ)).
        - repeat constructor.
          do 2 econstructor.
          1: apply mult_typed.
          + constructor. done.
          + done.
        - eapply TStore; by repeat constructor.
   }
   repeat constructor.
 - eapply App_typed ; repeat constructor.
Qed.

(* inline DH_rnd *)
Definition pk_ots_rnd_3 : expr :=
  let: "α" := allocB in
  let: "β" := allocB in
  let: "γ" := allocB in
  let: "a" := rnd "α" in
  let: "b" := rnd "β" in
  let: "c" := rnd "γ" in
  let: "A" := ge ^^ "a" in
  let: "B" := ge ^^ "b" in
  let: "C" := ge ^^ "c" in
  let: "count" := ref #0 in

  let: "getpk" := λ:<>, "A" in

  let: "query" := λ:"m",
      assert (!"count" = #0) ;;
      "count" <- #1 ;;
      ("B", "m" ** "C") in
  ("getpk", "query").

Lemma pk_ots_rnd_2_3 :
  ⊢ REL pk_ots_rnd_2 << pk_ots_rnd_3 : (() → T) * (T → T * T).
Proof with unfold evt, vvt ; rel_pures_l ; rel_pures_r.
  rewrite /pk_ots_rnd_2 /pk_ots_rnd_3...
  rel_allocBtape_l α as "α"...
  rel_allocBtape_l β as "β"...
  rel_allocBtape_l γ as "γ"...
  rel_allocBtape_r α' as "α'"...
  rel_allocBtape_r β' as "β'"...
  rel_allocBtape_r γ' as "γ'"...
  rel_apply (refines_couple_bool_tape_tape with "[- $α $α']") => //.
  iIntros (sk) "[α' α]"...
  rel_flipL_l ; rel_flipL_r...
  rel_apply (refines_couple_bool_tape_tape with "[- $β $β']") => //.
  iIntros (b) "[β' β]"...
  rel_apply_l baz ; rel_apply_r qux...
  rel_flipL_l ; rel_flipL_r...
  rel_apply (refines_couple_bool_tape_tape with "[- $γ $γ']") => //.
  iIntros (c) "[γ' γ]"...
  rel_apply_l baz ; rel_apply_r qux...
  rel_flipL_l ; rel_flipL_r...
  rel_apply_l baz ; rel_apply_r qux...
  rel_apply_l (refines_exp _ _ _ _ _ _ is_exp_eexp) => //.
  rel_apply_r (refines_exp' _ _ _ _ _ _ is_exp_eexp) => //...
  rel_apply_l (refines_exp _ _ _ _ _ _ is_exp_eexp) => //.
  rel_apply_r (refines_exp' _ _ _ _ _ _ is_exp_eexp) => //...
  rel_apply_l (refines_exp _ _ _ _ _ _ is_exp_eexp) => //.
  rel_apply_r (refines_exp' _ _ _ _ _ _ is_exp_eexp) => //...
  rel_alloc_l cnt as "cnt".
  rel_alloc_r cnt' as "cnt'".
  do 8 rel_pure_l.
  do 8 rel_pure_r.
  rel_apply compatibility.refines_pair.
  1: { rel_arrow_val. iIntros (?? (-> & ->))...
       iApply fundamental.refines_typed.
       constructor ; apply all_typed. }
  (* copy-pasted proof *)
  iApply (refines_na_alloc (∃ v, cnt ↦ #v ∗ cnt' ↦ₛ #v) pkN).
  iSplitL ; [ iExists _ ; iFrame|iIntros "#Hinv"].
  rel_arrow_val ; iIntros (??) "#Hv1v2"...
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "[>(%v&c&c') Hclose]".
  rel_load_l ; rel_load_r...
  destruct (bool_decide (#v = #0)%V)...
  - rel_store_l ; rel_store_r...
    iApply (refines_na_close with "[- $Hclose]").
    iSplitL ; [ iExists _ ; iFrame|].
    rel_apply compatibility.refines_pair.
    + iApply (fundamental.refines_typed _ _ _) ; constructor ; apply all_typed.
    + unshelve rel_apply compatibility.refines_app. 1: exact T.
        1: { unshelve rel_apply compatibility.refines_app ; [exact T|..].
             - replace (T → T → T)%lrel with (interp.interp (τ → τ → τ) []) => //.
               iApply fundamental.refines_typed. apply mult_typed.
             - rel_values.
        }
        iApply fundamental.refines_typed.
        constructor ; apply all_typed.
  - iApply (refines_na_close with "[- $Hclose]").
    iSplitL ; [ iExists _ ; iFrame|].
    iLöb as "H".
    rel_rec_l.
    iExact "H".
Qed.


(* push the random sampling back down *)
Definition pk_ots_rnd_4 : expr :=
  let: "α" := allocB in
  let: "β" := allocB in
  let: "γ" := allocB in
  let: "a" := rnd "α" in
  let: "A" := ge ^^ "a" in
  let: "count" := ref #0 in

  let: "getpk" := λ:<>, "A" in

  let: "query" := λ:"m",
      assert (!"count" = #0) ;;
      "count" <- #1 ;;
      let: "b" := rnd "β" in
      let: "c" := rnd "γ" in
      let: "B" := ge ^^ "b" in
      let: "C" := ge ^^ "c" in
      ("B", "m" ** "C") in
  ("getpk", "query").

Lemma pk_ots_rnd_3_4 :
  ⊢ REL pk_ots_rnd_3 << pk_ots_rnd_4 : (() → T) * (T → T * T).
Proof with unfold evt, vvt ; rel_pures_l ; rel_pures_r.
  rewrite /pk_ots_rnd_3 /pk_ots_rnd_4...
  rel_allocBtape_l α as "α"...
  rel_allocBtape_l β as "β"...
  rel_allocBtape_l γ as "γ"...
  rel_allocBtape_r α' as "α'"...
  rel_allocBtape_r β' as "β'"...
  rel_allocBtape_r γ' as "γ'"...
  rel_apply (refines_couple_bool_tape_tape with "[- $α $α']") => //.
  iIntros (sk) "[α' α]"...
  rel_flipL_l ; rel_flipL_r...
  rel_apply (refines_couple_bool_tape_tape with "[- $β $β']") => //.
  iIntros (b) "[β' β]"...
  rel_apply_l baz ; rel_apply_r qux...
  rel_flipL_l...
  rel_apply (refines_couple_bool_tape_tape with "[- $γ $γ']") => //.
  iIntros (c) "[γ' γ]"...
  rel_apply_l baz...
  rel_flipL_l...
  rel_apply_l baz...
  rel_apply_l (refines_exp _ _ _ _ _ _ is_exp_eexp) => //.
  rel_apply_r (refines_exp' _ _ _ _ _ _ is_exp_eexp) => //...
  rel_apply_l (refines_exp _ _ _ _ _ _ is_exp_eexp) => //...
  rel_apply_l (refines_exp _ _ _ _ _ _ is_exp_eexp) => //...
  rel_alloc_l cnt as "cnt".
  rel_alloc_r cnt' as "cnt'".
  do 8 rel_pure_l.
  do 8 rel_pure_r.
  rel_apply compatibility.refines_pair.
  1: { rel_arrow_val. iIntros (?? (-> & ->))...
       iApply fundamental.refines_typed.
       constructor ; apply all_typed. }

  set (P := (( (β ↪B [] ∗ β' ↪ₛB [b] ∗ γ ↪B [] ∗ γ' ↪ₛB [c] ∗ cnt ↦ #0 ∗ cnt' ↦ₛ #0))
             ∨ (cnt ↦ #1 ∗ cnt' ↦ₛ #1))%I).
    iApply (refines_na_alloc P pkN).
    iSplitL.
    { iLeft. iModIntro. iFrame. }
    iIntros "#Hinv".
    rel_arrow_val ; iIntros (??) "#Hv1v2"...
    iApply (refines_na_inv with "[$Hinv]"); [done|].
    iIntros "[>[(β&β'&γ&γ'&cnt&cnt')|(cnt&cnt')] Hclose]".
    - rel_load_r ; rel_load_l...
      rel_store_l ; rel_store_r...
      rel_flipL_r...
      rel_apply_r qux...
      rel_flipL_r...
      rel_apply_r qux...
      rel_apply_r (refines_exp' _ _ _ _ _ _ is_exp_eexp) => //...
      rel_apply_r (refines_exp' _ _ _ _ _ _ is_exp_eexp) => //...
      iApply (refines_na_close with "[- $Hclose]").
      iSplitL.
      { iRight. iModIntro. iFrame. }
      rel_apply compatibility.refines_pair.
      + iApply fundamental.refines_typed.
        constructor ; apply all_typed.
      + unshelve rel_apply compatibility.refines_app. 1: exact T.
        1: { unshelve rel_apply compatibility.refines_app ; [exact T|..].
             - replace (T → T → T)%lrel with (interp.interp (τ → τ → τ) []) => //.
               iApply fundamental.refines_typed. apply mult_typed.
             - rel_values.
        }
        iApply fundamental.refines_typed.
        constructor ; apply all_typed.
    - rel_load_l ; rel_load_r...
      iApply (refines_na_close with "[- $Hclose]").
      iSplitL.
      { iRight ; iFrame. }
      iLöb as "H".
      rel_rec_l.
      iExact "H".
Qed.

(* How do we show that we get a random group element when multiplying by m? *)
(* If m is a generator then m*— is a bijection with inverse (-m)*— . *)
(* But we're not multiplying by a random element, we're raising the generator
   to a randomly sampled power between 0 and n-1. *)
Definition pk_ots_rnd_5 : expr :=
  let: "α" := allocB in
  let: "β" := allocB in
  let: "γ" := allocB in
  let: "a" := rnd "α" in
  let: "A" := ge ^^ "a" in
  let: "count" := ref #0 in

  let: "getpk" := λ:<>, "A" in

  let: "query" := λ:"m",
      assert (!"count" = #0) ;;
      "count" <- #1 ;;
      let: "b" := rnd "β" in
      let: "x" := rnd "γ" in
      let: "B" := ge ^^ "b" in
      let: "X" := ge ^^ "x" in
      ("B", "X") in
  ("getpk", "query").

Lemma pk_ots_rnd_4_5 :
  ⊢ REL pk_ots_rnd_4 << pk_ots_rnd_5 : (() → T) * (T → T * T).
Proof with unfold evt, vvt ; rel_pures_l ; rel_pures_r.
  rewrite /pk_ots_rnd_4 /pk_ots_rnd_5...
  rel_allocBtape_l α as "α"...
  rel_allocBtape_l β as "β"...
  rel_allocBtape_l γ as "γ"...
  rel_allocBtape_r α' as "α'"...
  rel_allocBtape_r β' as "β'"...
  rel_allocBtape_r γ' as "γ'"...
  rel_apply (refines_couple_bool_tape_tape with "[- $α $α']") => //.
  iIntros (sk) "[α' α]"...
  rel_flipL_l ; rel_flipL_r...
  (* rel_apply (refines_couple_bool_tape_tape with "[- $β $β']") => //. *)
  (* iIntros (b) "[β' β]"... *)
  rel_apply_l baz ; rel_apply_r qux...
  rel_apply_l (refines_exp _ _ _ _ _ _ is_exp_eexp) => //.
  rel_apply_r (refines_exp' _ _ _ _ _ _ is_exp_eexp) => //...
  rel_alloc_l cnt as "cnt".
  rel_alloc_r cnt' as "cnt'".
  do 8 rel_pure_l.
  do 8 rel_pure_r.
  rel_apply compatibility.refines_pair.
  1: { rel_arrow_val. iIntros (?? (-> & ->))...
       iApply fundamental.refines_typed.
       constructor ; apply all_typed. }
  set (P := (( (β ↪B [] ∗ β' ↪ₛB [] ∗ γ ↪B [] ∗ γ' ↪ₛB [] ∗ cnt ↦ #0 ∗ cnt' ↦ₛ #0))
             ∨ (cnt ↦ #1 ∗ cnt' ↦ₛ #1))%I).
    iApply (refines_na_alloc P pkN).
    iSplitL.
    { iLeft. iModIntro. iFrame. }
    iIntros "#Hinv".
    rel_arrow_val.
    iIntros (??) "Hv1v2"...
    iApply (refines_na_inv with "[$Hinv]"); [done|].
    iIntros "[>[(β&β'&γ&γ'&cnt&cnt')|(cnt&cnt')] Hclose]".
    - rel_load_r ; rel_load_l...
      rel_store_l ; rel_store_r...
      rel_apply (refines_couple_bool_tape_tape with "[- $β $β']") => //.
      iIntros (b) "[β' β]"...
      rel_flipL_l ; rel_flipL_r...
      rel_apply (refines_couple_bool_tape_tape negb with "[- $γ $γ']") => //.
      iIntros (c) "[γ' γ]"...
      rel_apply_l baz ; rel_apply_r qux...
      rel_flipL_l ; rel_flipL_r...
      rel_apply_l baz ; rel_apply_r qux...
      iApply (refines_na_close with "[- $Hclose]").
      iSplitL.
      { iRight. iModIntro. iFrame. }
      rel_apply_l (refines_exp _ _ _ _ _ _ is_exp_eexp) => //.
      rel_apply_r (refines_exp' _ _ _ _ _ _ is_exp_eexp) => //...
      rel_apply_l (refines_exp _ _ _ _ _ _ is_exp_eexp) => //.
      rel_apply_r (refines_exp' _ _ _ _ _ _ is_exp_eexp) => //.
      unfold evt,vvt. rel_pures_l.
      do 2 rel_pure_r.
      rel_apply compatibility.refines_pair.
      + iApply fundamental.refines_typed.
        constructor ; apply all_typed.
      +
        (* TODO: In fact we have the wrong coupling here; instead of negb we
        should use the (exponent generating the) inverse to v1, but the current
        injection of booleans into exponents is too limited. Update this once
        this file is ported to the uniform branch. *)
        admit.
    - rel_load_l ; rel_load_r...
      iApply (refines_na_close with "[- $Hclose]").
      iSplitL.
      { iRight ; iFrame. }
      iLöb as "H".
      rel_rec_l.
      iExact "H".
Admitted.

(* Fold the definitions and erase tapes. *)
Definition pk_ots_rnd_rnd : expr :=
  (* "a" and "b" should be rnd n instead of flip #() *)
  let: "pk_sk" := keygen #() in
  let: "pk" := Fst "pk_sk" in
  let: "sk" := Snd "pk_sk" in
  let: "count" := ref #0 in

  let: "getpk" := λ:<>, "pk" in

  let: "query" := λ:"m",
      assert (!"count" = #0) ;;
      "count" <- #1 ;;
      let: "b" := rnd #() in
      let: "x" := rnd #() in
      let: "B" := ge^^"b" in
      let: "X" := ge^^"x" in
      ("B", "X") in
  ("getpk", "query").

Lemma pk_ots_rnd_5_rnd :
  ⊢ REL pk_ots_rnd_5 << pk_ots_rnd_rnd : (() → T) * (T → T * T).
Proof with unfold evt, vvt ; rel_pures_l ; rel_pures_r.
  rewrite /pk_ots_rnd_5 /pk_ots_rnd_rnd.
  rewrite /keygen /enc /rnd...
  rel_allocBtape_l α as "α"...
  rel_allocBtape_l β as "β"...
  rel_allocBtape_l γ as "γ"...
  rel_apply (refines_couple_tape_flip with "[- $α]") => //.
  iIntros (sk) "α"...
  rel_flipL_l...
  rel_apply_l baz ; rel_apply_r qux...
  rel_apply_l (refines_exp _ _ _ _ _ _ is_exp_eexp) => //.
  rel_apply_r (refines_exp' _ _ _ _ _ _ is_exp_eexp) => //...

  rel_alloc_l cnt as "cnt".
  rel_alloc_r cnt' as "cnt'".
  do 8 rel_pure_l.
  do 8 rel_pure_r.
  rel_apply compatibility.refines_pair.
  1: { rel_arrow_val. iIntros (?? (-> & ->))...
       iApply fundamental.refines_typed.
       constructor ; apply all_typed. }
  set (P := (α ↪B [] ∗ β ↪B [] ∗ γ ↪B [] ∗ (cnt ↦ #0 ∗ cnt' ↦ₛ #0)
             ∨ (cnt ↦ #1 ∗ cnt' ↦ₛ #1) )%I).
    iApply (refines_na_alloc P pkN).
    iSplitL.
    { iFrame. iLeft. iFrame. }
    iIntros "#Hinv".
    rel_arrow_val.
    iIntros (??) "Hv1v2"...
    iApply (refines_na_inv with "[$Hinv]"); [done|].
    iIntros "[>[(α&β&γ&cnt&cnt')|(cnt&cnt')] Hclose]".
    - rel_load_r ; rel_load_l...
      rel_store_l ; rel_store_r...
      rel_apply (refines_couple_tape_flip with "[-$β]") => //.
      iIntros (b) "β"...
      rel_flipL_l...
      rel_apply_l baz ; rel_apply_r qux...
      rel_apply (refines_couple_tape_flip with "[-$γ]") => //.
      iIntros (c) "γ"...
      rel_flipL_l...
      rel_apply_l baz ; rel_apply_r qux...
      iApply (refines_na_close with "[- $Hclose]").
      iSplitL.
      { iRight. iModIntro. iFrame. }
      rel_apply_l (refines_exp _ _ _ _ _ _ is_exp_eexp) => //.
      rel_apply_r (refines_exp' _ _ _ _ _ _ is_exp_eexp) => //...
      rel_apply_l (refines_exp _ _ _ _ _ _ is_exp_eexp) => //.
      rel_apply_r (refines_exp' _ _ _ _ _ _ is_exp_eexp) => //.
      unfold evt, vvt.
      do 2 (rel_pure_l ; rel_pure_r).
      rel_apply compatibility.refines_pair.
      + iApply fundamental.refines_typed ; constructor ; apply all_typed.
      + iApply fundamental.refines_typed ; constructor ; apply all_typed.
    - rel_load_l ; rel_load_r...
      iApply (refines_na_close with "[- $Hclose]").
      iSplitL.
      { iRight ; iFrame. }
      iLöb as "H".
      rel_rec_l.
      iExact "H".
Qed.


Definition pk_ots_rnd_real_dh : expr :=
  (* "a" and "b" should be rnd n instead of flip #() *)
  let: "a" := flip #() in
  let: "A" := ge^^"a" in
  let: "count" := ref #0 in

  let: "getpk" := λ:<>, "A" in

  let: "query" := λ:"m",
      assert (!"count" = #0) ;;
      "count" <- #1 ;;
      let: "b" := flip #() in
      let: "B" := "ge"^^"b" in
      let: "X" := "m" ** "A"^^"b" in
      ("B", "X") in
  ("getpk", "query").

Definition pk_ots_rnd_rnd_dh : expr :=
  (* "a" and "b" should be rnd n instead of flip #() *)
  let: "a" := flip #() in
  let: "A" := ge^^"a" in
  let: "count" := ref #0 in

  let: "getpk" := λ:<>, "A" in

  let: "query" := λ:"m",
      assert (!"count" = #0) ;;
      "count" <- #1 ;;
      let: "b" := flip #() in
      let: "x" := flip #() in
      let: "B" := "ge"^^"b" in
      let: "X" := "ge"^^"x" in
      ("B", "X") in
  ("getpk", "query").















Definition F_AUTH : expr := λ:<>,
  let: "l" := ref NONE in
  let: "flag" := ref #false in
  let: "read" := (λ:<>, if: (!"flag") then !"l" else NONE) in
  let: "write" := (λ:"v", if: (!"l" = NONE) then "l" <- SOME "v" else #()) in
  let: "enable" := (λ:"f", if: "f" !"l" then "flag" <- #true else #()) in
  ("read", "write", "enable").

(* let (recvA, sendA, enableA) = F_AUTH () in *)
(* let (recvB, sendB, enableB) = F_AUTH () in *)

(* a concrete abstract prime for the order *)
Parameter p : expr.

Definition alice (sendA recvB : expr) : expr :=
  λ:<>,
  let: "a" := flip #() in
  let: "A" := modulo (ge ^^ "a") p in
  sendA "A" ;;
  λ:<>,
    let: "B" := recvB #() in
    match: "B" with
    | NONE => #()
    | SOME "B" =>
        let: "s_a" := modulo ("B" ^^ "a") p in
        "s_a"
    end.

Definition bob (recvA sendB : expr) : expr :=
  λ:<>,
    let: "A" := recvA #() in
    match: "A" with
    | NONE => #()
    | SOME "A" =>
        let: "b" := flip #() in
        let: "B" := (ge ^^ "b") p in
        sendB "B";;
        let: "s_b" := modulo ("A" ^^ "b") p in
        "s_b"
    end.

(* (Alice, Bob, enableA, enableB) *)

End ElGamal.
