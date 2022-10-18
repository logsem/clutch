From Coq Require Import Reals Psatz.
From stdpp Require Import gmap.
From self.prob Require Export distribution.
From self.program_logic Require Export language.

Inductive action (Λ : language) :=
  (* prim_step *)
  | PRIM
  (* state_step *)
  | STATE (α : state_idx Λ).

Global Arguments PRIM {Λ}.
Global Arguments STATE {Λ} _.

Definition scheduler_fn (Λ : language) := gmap (cfg Λ) (action Λ).
Definition scheduler (Λ : language) := list (scheduler_fn Λ).

Section distribution.
  Context {Λ : language}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.
  Implicit Types α : state_idx Λ.
  Implicit Types ξ : scheduler Λ.

  Definition exec_fn_pmf '(e, σ) (f : scheduler_fn Λ) ρ : R :=
    match f !! (e, σ) with
    | Some PRIM => prim_step e σ ρ
    | Some (STATE α) => strength_l e (state_step σ α) ρ
    | None => 0%R
    end.
  Program Definition exec_fn (ρ : cfg Λ) (f : scheduler_fn Λ) : distr (cfg Λ) :=
    MkDistr (exec_fn_pmf ρ f) _ _ _.
  Next Obligation. intros [] f ρ. rewrite /exec_fn_pmf. destruct (f !! _) as [[]|]; [done|done|done]. Qed.
  Next Obligation.
    intros [e σ] f. rewrite /exec_fn_pmf.
    destruct (f !! _) as [[]|]; [done|done|]. apply ex_seriesC_0.
  Qed.
  Next Obligation.
    intros [e σ] f. rewrite /exec_fn_pmf.
    destruct (f !! _) as [[]|]; [done|done|]. rewrite SeriesC_0 //; lra.
  Qed.

  Lemma exec_fn_pmf_unfold f ρ ρ' :
    exec_fn ρ f ρ' =
      match f !! ρ with
      | Some PRIM => prim_step ρ.1 ρ.2 ρ'
      | Some (STATE α) => strength_l ρ.1 (state_step ρ.2 α) ρ'
      | _ => 0%R
      end.
  Proof.
    destruct ρ as [e σ].
    rewrite /exec_fn {1}/pmf /= /exec_fn_pmf /=.
    by destruct (f !! _) as [[]|].
  Qed.

  Lemma exec_fn_unfold f ρ :
    exec_fn ρ f =
      match f !! ρ with
      | Some PRIM => prim_step ρ.1 ρ.2
      | Some (STATE α) => strength_l ρ.1 (state_step ρ.2 α)
      | _ => dzero
      end.
  Proof.
    apply distr_ext=>?. rewrite exec_fn_pmf_unfold. by repeat case_match.
  Qed.

  Definition exec (ξ : scheduler Λ) (ρ : cfg Λ) : distr (cfg Λ) :=
    foldlM exec_fn ρ ξ.

  Lemma exec_nil ρ :
    exec [] ρ = dret ρ.
  Proof. done. Qed.

  Lemma exec_cons ρ f ξ :
    exec (f :: ξ) ρ = dbind (λ ρ'', exec ξ ρ'') (exec_fn ρ f).
  Proof. done. Qed.

End distribution.

Global Arguments exec_fn {_} _ _ : simpl never.
Global Arguments exec {_} _ _ : simpl never.
