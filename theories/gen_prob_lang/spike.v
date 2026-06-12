(** SPIKE (throwaway): confirm that the operational semantics of a probabilistic
    language can be made parametric in a *signature* [S : Sig] of sampling
    distributions, that [gen_lang S] is a [language] (so [irisGS]/[clutchWpGS]
    attach to it), and that the Option-A [SampleIn] mechanics resolve. *)
From Stdlib Require Import Reals Psatz ZArith.
From stdpp Require Import gmap fin countable.
From clutch.prob Require Import distribution.
From clutch.common Require Import language locations.
From iris.prelude Require Import options.

Module gen_spike.
#[local] Open Scope R.

(* ------------------------------------------------------------------ *)
(* Minimal syntax (no heap, no Rand/Laplace — just the generic Sample) *)
(* ------------------------------------------------------------------ *)
Inductive base_lit := LitInt (n : Z) | LitUnit | LitLbl (l : loc).
Inductive val := LitV (l : base_lit).
Inductive expr :=
  | Val (v : val)
  | Sample (i : nat) (e1 e2 : expr)
  | AllocSampleTape (i : nat) (e1 : expr).

Definition of_val : val → expr := Val.
Definition to_val (e : expr) : option val :=
  match e with Val v => Some v | _ => None end.
Definition def_val : val := LitV LitUnit.

(* --- decidable equality / countability of the syntax --- *)
Global Instance base_lit_eqdec : EqDecision base_lit. Proof. solve_decision. Defined.
Global Instance val_eqdec : EqDecision val. Proof. solve_decision. Defined.
Global Instance expr_eqdec : EqDecision expr. Proof. solve_decision. Defined.

Global Instance base_lit_countable : Countable base_lit.
Proof.
  refine (inj_countable'
    (λ l, match l with
          | LitInt n => inl n | LitUnit => inr (inl ()) | LitLbl l => inr (inr l) end)
    (λ x, match x with
          | inl n => LitInt n | inr (inl _) => LitUnit | inr (inr l) => LitLbl l end) _).
  by intros [].
Qed.

Global Instance val_countable : Countable val.
Proof.
  refine (inj_countable' (λ v, match v with LitV l => l end) (λ l, LitV l) _).
  by intros [].
Qed.

Global Instance expr_countable : Countable expr.
Proof.
  refine (inj_countable'
    (fix go e := match e with
      | Val v => GenLeaf (inr v)
      | Sample i e1 e2 => GenNode 0 [GenLeaf (inl i); go e1; go e2]
      | AllocSampleTape i e1 => GenNode 1 [GenLeaf (inl i); go e1]
      end)
    (fix dec t := match t with
      | GenLeaf (inr v) => Val v
      | GenNode 0 [GenLeaf (inl i); t1; t2] => Sample i (dec t1) (dec t2)
      | GenNode 1 [GenLeaf (inl i); t1] => AllocSampleTape i (dec t1)
      | _ => Val def_val
      end) _).
  fix IH 1. intros [v|i e1 e2|i e1]; simpl; f_equal; auto.
Qed.

(* --- state: one monomorphic tape map [(family index, params value, samples)] --- *)
Definition stape : Type := (nat * val * list val)%type.
Record state := mkState { stapes : gmap loc stape }.

Global Instance state_eqdec : EqDecision state.
Proof. solve_decision. Defined.
Global Instance state_countable : Countable state.
Proof. refine (inj_countable' stapes mkState _). by intros []. Qed.
Global Instance state_inhabited : Inhabited state := populate (mkState ∅).

(* ------------------------------------------------------------------ *)
(* The sampling signature                                             *)
(* ------------------------------------------------------------------ *)
Record SampleFamily := {
  sf_param : Type;
  sf_param_eqdec :: EqDecision sf_param;
  sf_param_count :: Countable sf_param;
  sf_out : Type;
  sf_out_eqdec :: EqDecision sf_out;
  sf_out_count :: Countable sf_out;
  sf_inj : sf_out → val;
  sf_inj_inj :: Inj (=) (=) sf_inj;
  sf_param_of_val : val → option sf_param;
  sf_param_to_val : sf_param → val;
  sf_roundtrip : ∀ p, sf_param_of_val (sf_param_to_val p) = Some p;
  sf_sample : sf_param → distr sf_out;
  sf_mass : ∀ p, SeriesC (sf_sample p) = 1;
}.

Definition Sig := list SampleFamily.

(* Option A: identity is positional; [sample_idx] is recovered from membership. *)
Class SampleIn (D : SampleFamily) (S : Sig) := {
  sample_idx : nat;
  sample_idx_S : S !! sample_idx = Some D;
}.

(* Dispatch: index the signature, decode params, push outcomes into [val]. *)
Definition sig_sample (S : Sig) (i : nat) (pv : val) : option (distr val) :=
  match S !! i with
  | Some D => (λ μ : distr (sf_out D), dmap (sf_inj D) μ) <$> (sf_sample D <$> sf_param_of_val D pv)
  | None => None
  end.

(* The agreement lemma every per-family rule rests on. *)
Lemma sig_sample_at (D : SampleFamily) (S : Sig) `{!SampleIn D S} (p : sf_param D) :
  sig_sample S sample_idx (sf_param_to_val D p)
    = Some (dmap (sf_inj D) (sf_sample D p)).
Proof.
  unfold sig_sample. rewrite sample_idx_S /=. rewrite sf_roundtrip /=. reflexivity.
Qed.

Lemma sig_sample_mass S i pv μ : sig_sample S i pv = Some μ → SeriesC μ = 1.
Proof.
  unfold sig_sample. destruct (S !! i) as [D|]; [|done].
  destruct (sf_param_of_val D pv) as [p|]; simpl; [|done].
  intros [= <-]. rewrite dmap_mass. apply sf_mass.
Qed.

(* ------------------------------------------------------------------ *)
(* Operational semantics, parametric in S                             *)
(* ------------------------------------------------------------------ *)
Definition head_step (S : Sig) (e : expr) (σ : state) : distr (expr * state) :=
  match e with
  | Sample i (Val pv) (Val (LitV LitUnit)) =>
      match sig_sample S i pv with
      | Some μ => dmap (λ v, (Val v, σ)) μ
      | None => dzero
      end
  | AllocSampleTape i (Val pv) =>
      dret (Val (LitV (LitLbl (fresh_loc σ.(stapes)))),
            mkState (<[fresh_loc σ.(stapes) := (i, pv, [])]> σ.(stapes)))
  | _ => dzero
  end.

Definition gen_state_step (σ : state) (α : loc) : distr state := dzero.
Definition get_active (σ : state) : list loc := [].

(* ------------------------------------------------------------------ *)
(* The language mixin (mass-1 obligations use sf_mass)                *)
(* ------------------------------------------------------------------ *)
Lemma gen_to_of_val v : to_val (of_val v) = Some v.
Proof. done. Qed.

Lemma gen_of_to_val e v : to_val e = Some v → of_val v = e.
Proof. destruct e as [v0| |]; cbn; intros [=]; subst; done. Qed.

Lemma gen_val_stuck S e σ ρ : head_step S e σ ρ > 0 → to_val e = None.
Proof.
  destruct ρ as [e' σ'], e as [v|i ep et|i ep]; cbn [head_step]; intros Hρ; try done.
  exfalso. rewrite dzero_0 in Hρ. lra.
Qed.

Lemma gen_state_step_not_stuck S e σ σ' α :
  gen_state_step σ α σ' > 0 →
  (∃ ρ, head_step S e σ ρ > 0) ↔ (∃ ρ', head_step S e σ' ρ' > 0).
Proof. intros H. exfalso. rewrite /gen_state_step dzero_0 in H. lra. Qed.

Lemma gen_state_step_mass σ α :
  α ∈ get_active σ → SeriesC (gen_state_step σ α) = 1.
Proof. unfold get_active. set_solver. Qed.

Lemma gen_head_step_mass S e σ :
  (∃ ρ, head_step S e σ ρ > 0) → SeriesC (head_step S e σ) = 1.
Proof.
  intros [[e' σ'] Hρ]. revert Hρ.
  destruct e as [v|i ep et|i ep]; cbn [head_step]; intros Hρ.
  - exfalso. rewrite dzero_0 in Hρ. lra.
  - destruct ep as [pv| |]; cbn [head_step] in Hρ |- *;
      try (exfalso; rewrite dzero_0 in Hρ; lra).
    destruct et as [tv| |]; cbn [head_step] in Hρ |- *;
      try (exfalso; rewrite dzero_0 in Hρ; lra).
    destruct tv as [[n| |l]]; cbn [head_step] in Hρ |- *;
      try (exfalso; rewrite dzero_0 in Hρ; lra).
    destruct (sig_sample S i pv) as [μ|] eqn:Hss; cbn [head_step] in Hρ |- *.
    + rewrite dmap_mass. by eapply sig_sample_mass.
    + exfalso. rewrite dzero_0 in Hρ. lra.
  - destruct ep as [pv| |]; cbn [head_step] in Hρ |- *;
      try (exfalso; rewrite dzero_0 in Hρ; lra).
    apply dret_mass.
Qed.

Lemma gen_lang_mixin (S : Sig) :
  LanguageMixin of_val to_val (head_step S) gen_state_step get_active.
Proof.
  split.
  - exact gen_to_of_val.
  - exact gen_of_to_val.
  - exact (gen_val_stuck S).
  - exact (gen_state_step_not_stuck S).
  - exact gen_state_step_mass.
  - exact (gen_head_step_mass S).
Qed.

(* The language, parametric in the signature S. *)
Definition gen_lang (S : Sig) : language :=
  @Language expr val state loc
    _ _ _ _ _ _ _ _
    of_val to_val def_val (head_step S) gen_state_step get_active
    (gen_lang_mixin S).

(* Sanity: the [language] projections compute to our concrete types, so any
   irisGS/clutchWpGS class (parametric over [Λ : language]) attaches cleanly. *)
Definition check_state_proj (S : Sig) (σ : language.state (gen_lang S)) : state := σ.
Definition check_val_proj   (S : Sig) (v : language.val (gen_lang S)) : val := v.
Definition check_expr_proj  (S : Sig) (e : language.expr (gen_lang S)) : expr := e.

(* ------------------------------------------------------------------ *)
(* Two concrete families and a signature; Option-A resolution by refl  *)
(* ------------------------------------------------------------------ *)
Definition uniform_family : SampleFamily.
Proof.
  refine {| sf_param := nat; sf_param_eqdec := _; sf_param_count := _;
            sf_out := Z; sf_out_eqdec := _; sf_out_count := _;
            sf_inj := (λ z, LitV (LitInt z)); sf_inj_inj := _;
            sf_param_of_val :=
              (λ v, match v with LitV (LitInt n) => Some (Z.to_nat n) | _ => None end);
            sf_param_to_val := (λ N, LitV (LitInt (Z.of_nat N))); sf_roundtrip := _;
            sf_sample :=
              (λ N, dmap (λ n : fin (S N), Z.of_nat (fin_to_nat n)) (dunifP N));
            sf_mass := _ |}; try exact _.
  - by intros ?? [= ->].
  - intros N. by rewrite Nat2Z.id.
  - intros N. rewrite dmap_mass. apply dunifP_mass.
Defined.

Definition laplace_family : SampleFamily.
Proof.
  refine {| sf_param := Z; sf_param_eqdec := _; sf_param_count := _;
            sf_out := Z; sf_out_eqdec := _; sf_out_count := _;
            sf_inj := (λ z, LitV (LitInt z)); sf_inj_inj := _;
            sf_param_of_val :=
              (λ v, match v with LitV (LitInt n) => Some n | _ => None end);
            sf_param_to_val := (λ z, LitV (LitInt z)); sf_roundtrip := _;
            sf_sample := (λ num, laplace_rat num 1 0);
            sf_mass := _ |}; try exact _.
  - by intros ?? [= ->].
  - done.
  - intros num. apply laplace_rat_mass.
Defined.

Definition my_sig : Sig := [uniform_family; laplace_family].

#[local] Program Instance SampleIn_uniform : SampleIn uniform_family my_sig :=
  {| sample_idx := 0 |}.
Next Obligation. reflexivity. Qed.

#[local] Program Instance SampleIn_laplace : SampleIn laplace_family my_sig :=
  {| sample_idx := 1 |}.
Next Obligation. reflexivity. Qed.

(* Both instances coexist; resolution picks by the named family D. *)
Example uniform_idx_is_0 : sample_idx (D := uniform_family) (S := my_sig) = 0%nat.
Proof. reflexivity. Qed.
Example laplace_idx_is_1 : sample_idx (D := laplace_family) (S := my_sig) = 1%nat.
Proof. reflexivity. Qed.

(* The agreement lemma fires for a concrete family in the concrete signature. *)
Example sig_sample_uniform (N : nat) :
  sig_sample my_sig (sample_idx (D := uniform_family)) (sf_param_to_val uniform_family N)
    = Some (dmap (sf_inj uniform_family) (sf_sample uniform_family N)).
Proof. apply (sig_sample_at uniform_family my_sig). Qed.

End gen_spike.
