From Autosubst Require Import Autosubst.
From clutch.prob_eff_lang.probblaze Require Import syntax semantics notation logic.
From clutch.prob_eff_lang.probblaze.examples Require Import scheduler_typed
  valgroup valgroup_Zpx fin_val_type fin_val_type_prod.
From clutch.prob_eff_lang.probblaze.typing Require Import types tychk.

(** * Regression tests for the driver [tychk] (PLAN.md, C3 acceptance and
      section 4 targets)

    Each lemma is a primed copy of an existing syntactic typing lemma,
    proved by [tychk] (after [change] to an annotated copy where the
    program needs annotations, PLAN.md section 4). *)

(* ================================================================== *)
(** * The scheduler (examples/secure_add3/scheduler_typed.v:140)       *)
(* ================================================================== *)

Section zsched.

Local Notation ρZ := (RCons (SAbs "w") RNil).
Local Notation RunT := (() ⇾ St)%ty.
Local Notation StepT := (St ⇾ St)%ty.

(* Three annotations: the type of each let-bound function ([run] is typed
   with [Z]'s absent label in its row and then coerced to [RunT], which
   erases it), and the signature handled by the deep handler. *)
Definition Zsched_ann : val :=
  λ: "R",
    effect "w"
    let: "run" := tyann RunT (tyann (() -{ ρZ }-> St)%ty (λ: <>,
      sigann "w" TUnit TUnit
      (handle: "R" (λ: <>, do: "w" #()%V) with
      | effect "w" <>, rec "k" => InjR "k"
      | return <> => InjL #()%V
      end))) in
    let: "step" := tyann StepT (λ: "s",
      match: rec_unfold "s" with
        InjL <> => InjL #()%V
      | InjR "k" => "k" #()%V
      end) in
    let: "s1" := "run" #()%V in
    let: "s2" := "run" #()%V in
    let: "s1" := "step" "s1" in
    let: "s2" := "step" "s2" in
    #true.

Lemma Zsched_typed' : ⊢ᵥ Zsched : (T ⇾ 𝔹).
Proof. change Zsched with Zsched_ann. tychk. Qed.

End zsched.

(* ================================================================== *)
(** * An adversary at a syntactic interface (PLAN.md section 4)       *)
(* ================================================================== *)

(* An interface shaped like [T_SCHAN] (advantage_sec_channel.v:81): a
   row-polymorphic client is turned into a row-polymorphic leak handler
   whose row mentions one-shot row variables. *)
Definition T_adv : type :=
  (∀R:
    (∀R: ((() -{ RVar 0 }-> ()) -{ RVar 0 ∪ᵣ RVar 1 }-∘ ())) ⇾
    (∀R: ∀R: ((() -{ RVar 1 }-> ()) * (() -{ RVar 0 }-> ()))
               -{ RFlip OS (RVar 1) ∪ᵣ (RFlip OS (RVar 0) ∪ᵣ RVar 2) }-∘ ()))%ty.

(* The adversary obtains the interface, passes a client whose body calls
   its operation through the row variable [RVar 0], and then calls the
   leak handler at the instantiated rows. *)
Definition A_adv : val :=
  λ: "f",
    let: "t" := "f" #()%V in
    let: "l" := "t" (λ: "op", "op" #()%V) in
    "l" ((λ: <>, #()%V), (λ: <>, #()%V)) ;;
    #true.

Lemma A_adv_typed : ⊢ᵥ A_adv : ((() -∘ T_adv) ⇾ 𝔹).
Proof. tychk. Qed.

(* ================================================================== *)
(** * Groups (examples/valgroup/valgroup.v:109)                        *)
(* ================================================================== *)

Section vexp.
  Context {cg : clutch_group_struct}.
  #[local] Hint Resolve vunit_typed vmult_typed : tychk_val.
  #[local] Hint Resolve τG_multi : tychk.

  Lemma vexp_typed' : val_typed (@vexp cg) ((@τG cg) ⇾ TInt ⇾ (@τG cg))%ty.
  Proof. unfold vexp, vexp'. tychk. Qed.
End vexp.

(* [vexp'] for any unit and multiplication, used for [vinv_p] below. *)
Lemma vexp'_typed u m τ :
  ⊢ᵥ u : τ → ⊢ᵥ m : (τ ⇾ τ ⇾ τ) → le.MultiT τ → ⊢ᵥ vexp' u m : (τ ⇾ ℤ ⇾ τ).
Proof. intros Hu Hm Hτ. unfold vexp'. tychk. Qed.

(* ================================================================== *)
(** * The Zpˣ instance (examples/valgroup/valgroup_Zpx.v)               *)
(* ================================================================== *)

Section Zpx_tests.
  Context (p''' : nat).

  Lemma vunit_p_typed' : ⊢ᵥ vunit_p p''' : ℤ.
  Proof. tychk. Qed.

  Lemma vmult_p_typed' : ⊢ᵥ vmult_p p''' : (ℤ ⇾ ℤ ⇾ ℤ).
  Proof. tychk. Qed.

  #[local] Hint Resolve vexp'_typed vunit_p_typed' vmult_p_typed' : tychk_val.

  Lemma vinv_p_typed' : ⊢ᵥ vinv_p p''' : (ℤ ⇾ ℤ).
  Proof. tychk. Qed.

  Lemma veq_p_typed' : ⊢ᵥ veq_p : (ℤ ⇾ ℤ ⇾ 𝔹).
  Proof. tychk. Qed.

  Lemma int_of_vg_p_typed' : ⊢ᵥ int_of_vg_p : (ℤ ⇾ ℤ).
  Proof. tychk. Qed.

  Lemma vg_of_int_p_typed' : ⊢ᵥ vg_of_int_p p''' : (ℤ ⇾ () + ℤ).
  Proof. tychk. Qed.

  Lemma vgval_p_typed' (x : fingroup.FinGroup.sort (@vgG (vg_p p'''))) : ⊢ᵥ @vgval (vg_p p''') x : @τG (cgs_p p''').
  Proof. tychk. Qed.
End Zpx_tests.

(* ================================================================== *)
(** * Products of finite value types                                    *)
(*     (examples/fin_val_type/fin_val_type_prod.v)                      *)
(* ================================================================== *)

Section fvt_prod.
  Context {t1 t2 : fin_val_type} {s1 : @fin_val_type_struct t1} {s2 : @fin_val_type_struct t2}.
  #[local] Hint Resolve int_of_fvt_typed fvt_of_int_typed : tychk_val.
  #[local] Hint Resolve τFT_multi : tychk.

  Lemma int_of_prod_typed' :
    val_typed (@int_of_prod t1 t2 s1 s2) ((s1.(τFT) * s2.(τFT)) ⇾ TInt)%ty.
  Proof. unfold int_of_prod. tychk. Qed.

  Lemma prod_of_int_typed' :
    val_typed (@prod_of_int t1 t2 s1 s2) (TInt ⇾ () + (s1.(τFT) * s2.(τFT)))%ty.
  Proof. unfold prod_of_int. tychk. Qed.
End fvt_prod.

Section fvt_prod_val.
  Context `{!probblazeRGS Σ}.
  Context {t1 t2 : fin_val_type} {s1 : @fin_val_type_struct t1} {s2 : @fin_val_type_struct t2}.
  Context (fv1 : @fin_val Σ _ t1 s1) (fv2 : @fin_val Σ _ t2 s2).
  #[local] Hint Resolve fvtval_typed : tychk_val.

  Lemma fvtval_prod_typed' (xy : fintype.Finite.sort (@fvT (@prod_fvt t1 t2))) :
    val_typed (fvtval (fin_val_type := @prod_fvt t1 t2) xy) (s1.(τFT) * s2.(τFT))%ty.
  Proof using All. tychk. Qed.
End fvt_prod_val.

(* ================================================================== *)
(** * Diffie-Hellman triples (examples/dhke/dhke_common.v:240-343)      *)
(* ================================================================== *)

(* [dhke_common.v] sits behind the UC modules, which are compiled against
   the types of the main build; the two programs are copied from
   [dhke_def.v:20] and [:415]. *)
Section dh.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Import valgroup_notation.
  #[local] Notation n := (S n'').

  Definition sample' : expr := λ: <>, rand #n.

  Definition DH_real' : val :=
    λ: <>,
    let: "a" := sample' #()%V in
    let: "b" := sample' #()%V in
    (g^"a", g^"b", g^("a"*"b")).

  #[local] Hint Resolve vgval_typed vexp_typed' : tychk_val.

  Lemma sample_typed' Γ : ∅ .| Γ ⊢ₜ sample' #()%V : RNil : ℕ ⊣ Γ.
  Proof using All. tychk. Qed.

  Lemma DH_real_typed' : ⊢ᵥ DH_real' : (() -∘ τG * τG * τG).
  Proof using All. tychk. Qed.
End dh.
