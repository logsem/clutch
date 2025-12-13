From clutch.eris.examples.math Require Import prelude continuity2 iverson sets.
From clutch.eris Require Import infinite_tape.
Import Hierarchy.
Set Default Proof Using "Type*".
#[local] Open Scope R.

(** Piecewise continuous 1D functions *)

(* A function on a rectangle *)
Definition IntervalFun_R : ((R → R) * R * R) → (R → R) :=
  fun '(f, xa, xb) x => Iverson (Ioo xa xb) x * f x.

Definition IntervalFun_continuity : ((R → R) * R * R) → Prop :=
  fun '(f, xa, xb) => ∀ x, Ioo xa xb x → Continuity.continuous f x.

Definition fsum {T : Type} (L : list (T → R)) : T → R := fun t => foldr (fun f s => f t + s) 0 L.

(* Generalized: f is a finite sum of rectangle functions *)
Definition PCts (f : R → R) (xa xb : R) : Prop :=
  ∃ L, (∀ x, Ioo xa xb x → f x = fsum (IntervalFun_R <$> L) x) ∧ Forall IntervalFun_continuity L.

Lemma IntervalFun_RInt {f xa xb} {a b} :
  IntervalFun_continuity (f, xa, xb) →
  ex_RInt (IntervalFun_R (f, xa, xb)) a b.
Proof.
  rewrite //=.
  intros H.
  (* Chasles *)
Admitted.

Lemma PCts_RInt {f xa xb} (HP : PCts f xa xb) :
  ex_RInt f xa xb.
Proof.
Admitted.

Lemma PCts_cts {f xa xb} : (∀ x, Ioo xa xb x → Continuity.continuous f x) → PCts f xa xb.
Proof.
  exists [(f, xa, xb)].
  split.
  { rewrite /fsum//=.
    intros ??.
    rewrite Iverson_True; try done.
    lra.
  }
  rewrite Forall_singleton //=.
Qed.

Lemma PCts_plus {f g xa xb} : PCts f xa xb → PCts g xa xb → PCts (fun x => f x + g x) xa xb.
Proof. Admitted.

Lemma PCts_mult {f g xa xb} : PCts f xa xb → PCts g xa xb → PCts (fun x => f x + g x) xa xb.
Proof. Admitted.

(** Piecewise continuity over the enture real line *)

(* Generalized: f is a finite sum of rectangle functions *)
Definition IPCts (f : R → R) : Prop :=
  ∃ L, f = fsum (IntervalFun_R <$> L) ∧ Forall IntervalFun_continuity L.

Lemma IPCts_PCts (f : R → R) : IPCts f → ∀ a b, PCts f a b.
Proof.
  intros [L[??]] ??. exists L; split; try done.
  intros ??. rewrite H //=.
Qed.

Lemma IPCts_RInt {f xa xb} (HP : IPCts f ) : ex_RInt f xa xb.
Proof. by apply PCts_RInt, IPCts_PCts. Qed.

Lemma IPCts_cts {f} : (∀ x, Continuity.continuous f x) → IPCts f.
Proof. Admitted.

Lemma IPCts_plus {f g} : IPCts f → IPCts g → IPCts (fun x => f x + g x).
Proof. Admitted.

Lemma IPCts_mult {f g} : IPCts f → IPCts g → IPCts (fun x => f x * g x).
Proof. Admitted.

Lemma IPCts_scal_mult {c : R} {G : R → R} :
  IPCts G → IPCts (fun x => c * G x).
Proof. Admitted.

(** Piecewise continuous 2D functions *)

Definition fsum2 {T U : Type} (L : list (T → U → R)) : T → U → R :=
  fun t u => foldr (fun f s => f t u + s) 0 L.

Definition RectFun_RR : ((R → R → R) * R * R * R * R) → (R → R → R) :=
  fun '(f, xa, xb, ya, yb) x y => Iverson (Ioo xa xb) x * Iverson (Ioo ya yb) y * f x y.

Definition RectFun_continuity : ((R → R → R) * R * R * R * R) → Prop :=
  fun '(f, xa, xb, ya, yb) => ∀ x y, Icc xa xb x → Icc ya yb y → Continuity2 (uncurry f) x y.

(* f is a finite sum of rectangle functions on the rectangle [xa xb] [ya yb] *)
Definition PCts2 (f : R → R → R) (xa xb ya yb : R) : Prop :=
  ∃ L,
    ∀ x y, (Ioo xa xb x → Ioo ya yb y → f x y = fsum2 (RectFun_RR <$> L) x y) ∧
    Forall RectFun_continuity L.

Lemma PCts2_continuous {f : R → R → R} {xa xb ya yb} :
  (∀ x y, Continuity2 (uncurry f) x y) →
  PCts2 f xa xb ya yb.
Proof. Admitted.

Lemma fsum2_app {T U : Type} (L1 L2 : list (T → U → R)) (t : T) (u : U) :
  fsum2 (L1 ++ L2) t u = fsum2 L1 t u + fsum2 L2 t u.
Proof.
  unfold fsum2.
  induction L1 as [| f L1 IH].
  { simpl. lra. }
  { simpl. rewrite IH. lra. }
Qed.

Lemma PCts2_plus {f g : R → R → R} {xa xb ya yb} :
  PCts2 f xa xb ya yb → PCts2 g xa xb ya yb → PCts2 (fun (x y : R) => f x y + g x y) xa xb ya yb.
Proof.
  intros [Lf Hf] [Lg Hg].
  unfold PCts2.
  exists (Lf ++ Lg).
  intros x y.
  split.
  {
    intros Hx Hy.
    destruct (Hf x y) as [Hfeq _].
    destruct (Hg x y) as [Hgeq _].
    rewrite (Hfeq Hx Hy).
    rewrite (Hgeq Hx Hy).
    rewrite fmap_app.
    rewrite fsum2_app.
    reflexivity.
  }
  {
    apply Forall_app.
    split.
    { destruct (Hf xa ya) as [_ HLf]. exact HLf. }
    { destruct (Hg xa ya) as [_ HLg]. exact HLg. }
  }
Qed.

Lemma PCts2_mult {f g : R → R → R} {xa xb ya yb} :
  PCts2 f xa xb ya yb → PCts2 g xa xb ya yb → PCts2 (fun (x y : R) => f x y * g x y) xa xb ya yb.
Proof.
Admitted.

Lemma PCts_const_x {f xa xb ya yb} : PCts f xa xb → PCts2 (fun x _ => f x) xa xb ya yb.
Proof.
Admitted.

Lemma PCts_const_y {f xa xb ya yb} : PCts f ya yb → PCts2 (fun _ y => f y) xa xb ya yb.
Proof.
Admitted.
