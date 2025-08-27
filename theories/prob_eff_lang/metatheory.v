From Coq Require Import Reals Psatz.
From clutch.common Require Import locations.
From clutch.prob_eff_lang Require Export lang notation.

(** Some useful lemmas to reason about language properties  *)

Inductive det_head_step_rel : expr → state → expr → state → Prop :=
| RecDS f x e σ :
  det_head_step_rel (Rec f x e) σ (Val $ RecV f x e) σ
| PairDS v1 v2 σ :
  det_head_step_rel (Pair (Val v1) (Val v2)) σ (Val $ PairV v1 v2) σ
| InjLDS v σ :
  det_head_step_rel (InjL $ Val v) σ (Val $ InjLV v) σ
| InjRDS v σ :
  det_head_step_rel (InjR $ Val v) σ (Val $ InjRV v) σ
| BetaDS f x e1 v2 e' σ :
  e' = subst' x v2 (subst' f (RecV f x e1) e1) →
  det_head_step_rel (App (Val $ RecV f x e1) (Val v2)) σ e' σ
| UnOpDS op v v' σ :
  un_op_eval op v = Some v' →
  det_head_step_rel (UnOp op (Val v)) σ (Val v') σ
| BinOpDS op v1 v2 v' σ :
  bin_op_eval op v1 v2 = Some v' →
  det_head_step_rel (BinOp op (Val v1) (Val v2)) σ (Val v') σ
| IfTrueDS e1 e2 σ :
  det_head_step_rel (If (Val $ LitV $ LitBool true) e1 e2) σ e1 σ
| IfFalseDS e1 e2 σ :
  det_head_step_rel (If (Val $ LitV $ LitBool false) e1 e2) σ e2 σ
| FstDS v1 v2 σ :
  det_head_step_rel (Fst (Val $ PairV v1 v2)) σ (Val v1) σ
| SndDS v1 v2 σ :
  det_head_step_rel (Snd (Val $ PairV v1 v2)) σ (Val v2) σ
| CaseLDS v e1 e2 σ :
  det_head_step_rel (Case (Val $ InjLV v) e1 e2) σ (App e1 (Val v)) σ
| CaseRDS v e1 e2 σ :
  det_head_step_rel (Case (Val $ InjRV v) e1 e2) σ (App e2 (Val v)) σ
| AllocNDS z N v σ l :
  l = fresh_loc σ.(heap) →
  N = Z.to_nat z →
  (0 < N)%nat ->
  det_head_step_rel (AllocN (Val (LitV (LitInt z))) (Val v)) σ
    (Val $ LitV $ LitLoc l) (state_upd_heap_N l N v σ)
| LoadDS l v σ :
  σ.(heap) !! l = Some v →
  det_head_step_rel (Load (Val $ LitV $ LitLoc l)) σ (of_val v) σ
| StoreDS l v w σ :
  σ.(heap) !! l = Some v →
  det_head_step_rel (Store (Val $ LitV $ LitLoc l) (Val w)) σ
    (Val $ LitV LitUnit) (state_upd_heap <[l:=w]> σ)
| TickDS z σ :
  det_head_step_rel (Tick (Val $ LitV $ LitInt z)) σ (Val $ LitV $ LitUnit) σ
| DoDS v σ :
  det_head_step_rel (Do (Val v)) σ (Eff v []) σ
| TryWithEffDS v k e2 e3 σ :
  det_head_step_rel (TryWith (Eff v k) e2 e3)             σ
    (App (App e2 (Val v)) (Val (Cont k))) σ
| TryWithRetDS v e2 e3 σ :
  det_head_step_rel (TryWith (Val v) e2 e3) σ (App e3 (Val v)) σ
| ContDS k v σ :
  det_head_step_rel (App (Val (Cont k)) (Val v)) σ (fill k (Val v)) σ
(* AppLCtx. *)
| AppLEffDS v1 k v2 σ :
  det_head_step_rel (App (Eff v1 k) (Val v2))    σ
    (Eff v1 (k ++ [(AppLCtx v2)])) σ
(* AppRCtx. *)
| AppREffDS e1 v1 k σ :
  det_head_step_rel (App e1 (Eff v1 k))          σ
    (Eff v1 (k ++ [(AppRCtx e1)])) σ
(* UnOpCtx. *)
| UnOpEffDS op v k σ :
  det_head_step_rel (UnOp op (Eff v k))         σ
    (Eff v (k ++ [(UnOpCtx op)])) σ
(* BinOpLCtx. *)
| BinOpLEffDS op v1 k v2 σ :
  det_head_step_rel (BinOp op (Eff v1 k) (Val v2))    σ
    (Eff v1 (k ++ [(BinOpLCtx op v2)])) σ
(* BinOpRCtx. *)
| BinOpREffDS op e1 v2 k σ :
  det_head_step_rel (BinOp op e1 (Eff v2 k))          σ
    (Eff v2 (k ++ [(BinOpRCtx op e1)])) σ
(* IfCtx. *)
| IfEffDS v k e1 e2 σ :
  det_head_step_rel (If (Eff v k) e1 e2)         σ
    (Eff v (k ++ [(IfCtx e1 e2)])) σ
(* PairLCtx. *)
| PairLEffDS v1 k v2 σ :
  det_head_step_rel (Pair (Eff v1 k) (Val v2))    σ
    (Eff v1 (k ++ [(PairLCtx v2)])) σ
(* PairRCtx. *)
| PairREffDS e1 v2 k σ :
  det_head_step_rel (Pair e1 (Eff v2 k))          σ
    (Eff v2 (k ++ [(PairRCtx e1)])) σ
(* FstCtx. *)
| FstEffDS v k σ :
  det_head_step_rel (Fst (Eff v k))       σ
    (Eff v (k ++ [FstCtx])) σ
(* SndCtx. *)
| SndEffDS v k σ :
  det_head_step_rel (Snd (Eff v k))       σ
    (Eff v (k ++ [SndCtx])) σ
(* InjLCtx. *)
| InjLEffDS v k σ :
  det_head_step_rel (InjL (Eff v k))       σ
    (Eff v (k ++ [InjLCtx])) σ
(* InjRCtx. *)
| InjREffDS v k σ :
  det_head_step_rel (InjR (Eff v k))       σ
    (Eff v (k ++ [InjRCtx])) σ
(* CaseCtx. *)
| CaseEffDS v k e1 e2 σ :
  det_head_step_rel (Case (Eff v k) e1 e2)         σ
    (Eff v (k++ [(CaseCtx e1 e2)])) σ
(* AllocNLCtx. *)
| AllocNLEffDS v1 k v2 σ :
  det_head_step_rel (AllocN (Eff v1 k) (Val v2))      σ
    (Eff v1 (k ++ [(AllocNLCtx v2)])) σ
(* AllocNRCtx. *)
| AllocNREffDS v k e σ :
  det_head_step_rel (AllocN e (Eff v k))      σ
    (Eff v (k ++ [(AllocNRCtx e)])) σ
(* LoadCtx. *)
| LoadEffDS v k σ :
  det_head_step_rel (Load (Eff v k))       σ
    (Eff v (k ++ [LoadCtx])) σ
(* StoreLCtx. *)
| StoreLEffDS v1 k v2 σ :
  det_head_step_rel (Store (Eff v1 k) (Val v2))    σ
    (Eff v1 (k ++ [(StoreLCtx v2)])) σ
(* StoreRCtx. *)
| StoreREffDS e1 v2 k σ :
  det_head_step_rel (Store e1 (Eff v2 k))          σ
    (Eff v2 (k ++ [(StoreRCtx e1)])) σ
(* AllocTapeCtx *)
| AllocTapeEffDS v k σ :
  det_head_step_rel (AllocTape (Eff v k)) σ (Eff v (k ++ [AllocTapeCtx])) σ
(* RandLCtx *)
| RandLEffDS v1 k v2 σ :
  det_head_step_rel (Rand (Eff v1 k) (Val v2)) σ (Eff v1 (k ++ [(RandLCtx v2)])) σ
(* RandRCtx *)
| RandREffDS e v k σ :
  det_head_step_rel (Rand e (Eff v k)) σ (Eff v (k ++ [(RandRCtx e)])) σ
(* TickCtx *)
| TickEffDS v k σ :
  det_head_step_rel (Tick (Eff v k)) σ (Eff v (k ++ [TickCtx])) σ
(* DoCtx. *)
| DoEffDS v k σ :
  det_head_step_rel (Do (Eff v k))         σ
    (Eff v (k ++ [DoCtx])) σ.

Inductive det_head_step_pred : expr → state → Prop :=
| RecDSP f x e σ :
  det_head_step_pred (Rec f x e) σ
| PairDSP v1 v2 σ :
  det_head_step_pred (Pair (Val v1) (Val v2)) σ
| InjLDSP v σ :
  det_head_step_pred (InjL $ Val v) σ
| InjRDSP v σ :
  det_head_step_pred (InjR $ Val v) σ
| BetaDSP f x e1 v2 σ :
  det_head_step_pred (App (Val $ RecV f x e1) (Val v2)) σ
| UnOpDSP op v σ v' :
  un_op_eval op v = Some v' →
  det_head_step_pred (UnOp op (Val v)) σ
| BinOpDSP op v1 v2 σ v' :
  bin_op_eval op v1 v2 = Some v' →
  det_head_step_pred (BinOp op (Val v1) (Val v2)) σ
| IfTrueDSP e1 e2 σ :
  det_head_step_pred (If (Val $ LitV $ LitBool true) e1 e2) σ
| IfFalseDSP e1 e2 σ :
  det_head_step_pred (If (Val $ LitV $ LitBool false) e1 e2) σ
| FstDSP v1 v2 σ :
  det_head_step_pred (Fst (Val $ PairV v1 v2)) σ
| SndDSP v1 v2 σ :
  det_head_step_pred (Snd (Val $ PairV v1 v2)) σ
| CaseLDSP v e1 e2 σ :
  det_head_step_pred (Case (Val $ InjLV v) e1 e2) σ
| CaseRDSP v e1 e2 σ :
  det_head_step_pred (Case (Val $ InjRV v) e1 e2) σ
| AllocNDSP z N v σ l :
  l = fresh_loc σ.(heap) →
  N = Z.to_nat z →
  (0 < N)%nat ->
  det_head_step_pred (AllocN (Val (LitV (LitInt z))) (Val v)) σ
| LoadDSP l v σ :
  σ.(heap) !! l = Some v →
  det_head_step_pred (Load (Val $ LitV $ LitLoc l)) σ
| StoreDSP l v w σ :
  σ.(heap) !! l = Some v →
  det_head_step_pred (Store (Val $ LitV $ LitLoc l) (Val w)) σ
| TickDSP z σ :
  det_head_step_pred (Tick (Val $ LitV $ LitInt z)) σ
| DoDSP v σ :
  det_head_step_pred (Do (Val v)) σ
| TryWithEffDSP v k e2 e3 σ :
  det_head_step_pred (TryWith (Eff v k) e2 e3) σ
| TryWithRetDSP v e2 e3 σ :
  det_head_step_pred (TryWith (Val v) e2 e3) σ
| ContDSP k v σ :
  det_head_step_pred (App (Val (Cont k)) (Val v)) σ
(* AppLCtx. *)
| AppLEffDSp v1 k v2 σ :
  det_head_step_pred (App (Eff v1 k) (Val v2))    σ
(* AppRCtx. *)
| AppREffDSP e1 v1 k σ :
  det_head_step_pred (App e1 (Eff v1 k))          σ
(* UnOpCtx. *)
| UnOpEffDSP op v k σ :
  det_head_step_pred (UnOp op (Eff v k))         σ
(* BinOpLCtx. *)
| BinOpLEffDSP op v1 k v2 σ :
  det_head_step_pred (BinOp op (Eff v1 k) (Val v2))    σ
(* BinOpRCtx. *)
| BinOpREffDSP op e1 v2 k σ :
  det_head_step_pred (BinOp op e1 (Eff v2 k))          σ
(* IfCtx. *)
| IfEffDSP v k e1 e2 σ :
  det_head_step_pred (If (Eff v k) e1 e2)         σ
(* PairLCtx. *)
| PairLEffDSP v1 k v2 σ :
  det_head_step_pred (Pair (Eff v1 k) (Val v2))    σ
(* PairRCtx. *)
| PairREffDSP e1 v2 k σ :
  det_head_step_pred (Pair e1 (Eff v2 k))          σ
(* FstCtx. *)
| FstEffDSP v k σ :
  det_head_step_pred (Fst (Eff v k))       σ
(* SndCtx. *)
| SndEffDSP v k σ :
  det_head_step_pred (Snd (Eff v k))       σ
(* InjLCtx. *)
| InjLEffDSP v k σ :
  det_head_step_pred (InjL (Eff v k))       σ
(* InjRCtx. *)
| InjREffDSP v k σ :
  det_head_step_pred (InjR (Eff v k))       σ
(* CaseCtx. *)
| CaseEffDSP v k e1 e2 σ :
  det_head_step_pred (Case (Eff v k) e1 e2)         σ
(* AllocNLCtx. *)
| AllocNLEffDSP v1 k v2 σ :
  det_head_step_pred (AllocN (Eff v1 k) (Val v2))      σ
(* AllocNRCtx. *)
| AllocNREffDSP v k e σ :
  det_head_step_pred (AllocN e (Eff v k))      σ
(* LoadCtx. *)
| LoadEffDSP v k σ :
  det_head_step_pred (Load (Eff v k))       σ
(* StoreLCtx. *)
| StoreLEffDSP v1 k v2 σ :
  det_head_step_pred (Store (Eff v1 k) (Val v2))    σ
(* StoreRCtx. *)
| StoreREffDSP e1 v2 k σ :
  det_head_step_pred (Store e1 (Eff v2 k))          σ
(* AllocTapeCtx *)
| AllocTapeEffDSP v k σ :
  det_head_step_pred (AllocTape (Eff v k)) σ
(* RandLCtx *)
| RandLEffDSP v1 k v2 σ :
  det_head_step_pred (Rand (Eff v1 k) (Val v2)) σ
(* RandRCtx *)
| RandREffDSP e v k σ :
  det_head_step_pred (Rand e (Eff v k)) σ
(* TickCtx *)
| TickEffDSP v k σ :
  det_head_step_pred (Tick (Eff v k)) σ
(* DoCtx. *)
| DoEffDSP v k σ :
  det_head_step_pred (Do (Eff v k))         σ.


Definition is_det_head_step (e1 : expr) (σ1 : state)  : bool :=
  match e1 with
  | Rec f x e => true
  | Pair (Val v1) (Val v2) => true
  | InjL (Val v) => true
  | InjR (Val v) => true
  | App (Val (RecV f x e1)) (Val v2) => true
  | UnOp op (Val v)  => bool_decide(is_Some(un_op_eval op v))
  | BinOp op (Val v1) (Val v2) => bool_decide (is_Some(bin_op_eval op v1 v2))
  | If (Val (LitV (LitBool true))) e1 e2 => true
  | If (Val (LitV (LitBool false))) e1 e2 => true
  | Fst (Val (PairV v1 v2)) => true
  | Snd (Val (PairV v1 v2)) => true
  | Case (Val (InjLV v)) e1 e2 => true
  | Case (Val (InjRV v)) e1 e2 => true
  | AllocN (Val (LitV (LitInt z))) (Val v) => bool_decide (0 < Z.to_nat z)%nat
  | Load (Val (LitV (LitLoc l)))  =>
      bool_decide (is_Some (σ1.(heap) !! l))
  | Store (Val (LitV (LitLoc l))) (Val w) =>
      bool_decide (is_Some (σ1.(heap) !! l))
  | Tick (Val (LitV (LitInt z))) => true
  | Do (Val v) => true
  | TryWith (Eff v k) e1 e2 => true
  | TryWith (Val v) e1 e2 => true
  | App (Val (Cont k)) (Val v) => true
  | App (Eff v1 k) (Val v2) => true
  | App e (Eff v1 k) => true
  | UnOp op (Eff v k) => true
  | BinOp op (Eff v1 k) (Val v2) => true
  | BinOp op e (Eff v2 k) => true
  | If (Eff v k) e1 e2 => true
  | Pair (Eff v1 k) (Val v2) => true
  | Pair e (Eff v2 k) => true
  | Fst (Eff v k) => true
  | Snd (Eff v k) => true
  | InjL (Eff v k) => true
  | InjR (Eff v k) => true
  | Case (Eff v k) e1 e2 => true
  | AllocN (Eff v1 k) (Val v2) => true
  | AllocN e (Eff v k) => true
  | Load (Eff v k) => true
  | Store (Eff v1 k) (Val v2) => true
  | Store e (Eff v2 k) => true
  | AllocTape (Eff v k) => true
  | Rand (Eff v1 k) (Val v2) => true
  | Rand e (Eff v k) => true
  | Tick (Eff v k) => true
  | Do (Eff v k) => true
  | _ => false
  end.

Lemma det_step_eq_tapes e1 σ1 e2 σ2 :
  det_head_step_rel e1 σ1 e2 σ2 → σ1.(tapes) = σ2.(tapes).
Proof. inversion 1; auto. Qed.

Inductive prob_head_step_pred : expr -> state -> Prop :=
| AllocTapePSP σ N z :
  N = Z.to_nat z →
  prob_head_step_pred (alloc #z) σ
| RandTapePSP α σ N n ns z :
  N = Z.to_nat z →
  σ.(tapes) !! α = Some ((N; n :: ns) : tape) →
  prob_head_step_pred (rand(#lbl:α) #z) σ
| RandEmptyPSP N α σ z :
  N = Z.to_nat z →
  σ.(tapes) !! α = Some ((N; []) : tape) →
  prob_head_step_pred (rand(#lbl:α)  #z) σ
| RandTapeOtherPSP N M α σ ns z :
  N ≠ M →
  M = Z.to_nat z →
  σ.(tapes) !! α = Some ((N; ns) : tape) →
  prob_head_step_pred (rand(#lbl:α) #z) σ
| RandNoTapePSP (N : nat) σ z :
  N = Z.to_nat z →
  prob_head_step_pred (rand #z) σ.

Definition head_step_pred e1 σ1 :=
  det_head_step_pred e1 σ1 ∨ prob_head_step_pred e1 σ1.

Lemma det_step_is_unique e1 σ1 e2 σ2 e3 σ3 :
  det_head_step_rel e1 σ1 e2 σ2 →
  det_head_step_rel e1 σ1 e3 σ3 →
  e2 = e3 ∧ σ2 = σ3.
Proof.
  intros H1 H2.
  inversion H1; inversion H2; simplify_eq; auto.
Qed.

Lemma det_step_pred_ex_rel e1 σ1 :
  det_head_step_pred e1 σ1 ↔ ∃ e2 σ2, det_head_step_rel e1 σ1 e2 σ2.
Proof.
  split.
  - intro H; inversion H; simplify_eq; eexists; eexists; econstructor; eauto.
  - intros (e2 & (σ2 & H)); inversion H ; econstructor; eauto.
Qed.

Local Ltac solve_step_det :=
  rewrite /pmf /=;
    repeat (rewrite bool_decide_eq_true_2 // || case_match);
  try (lra || lia || done).

Local Ltac inv_det_head_step :=
  repeat
    match goal with
    | H : to_val _ = Some _ |- _ => apply of_to_val in H
    | H : is_det_head_step _ _ = true |- _ =>
        rewrite /is_det_head_step in H;
        repeat (case_match in H; simplify_eq)
    | H : is_Some _ |- _ => destruct H
    | H : bool_decide  _ = true |- _ => rewrite bool_decide_eq_true in H; destruct_and?
    | _ => progress simplify_map_eq/=
    end.

Lemma is_det_head_step_true e1 σ1 :
  is_det_head_step e1 σ1 = true ↔ det_head_step_pred e1 σ1.
Proof.
  split; intro H.
  - destruct e1; inv_det_head_step; by econstructor.
  - inversion H; solve_step_det.
Qed.

Lemma det_head_step_singleton e1 σ1 e2 σ2 :
  det_head_step_rel e1 σ1 e2 σ2 → head_step e1 σ1 = dret (e2, σ2).
Proof.
  intros Hdet.
  apply pmf_1_eq_dret.
  inversion Hdet; simplify_eq/=; try case_match;
    simplify_option_eq; try repeat destruct_match; rewrite ?dret_1_1 //.
Qed.

Lemma val_not_head_step e1 σ1 :
  is_Some (to_val e1) → ¬ head_step_pred e1 σ1.
Proof.
  intros [] [Hs | Hs]; inversion Hs; simplify_eq.
Qed.

Lemma head_step_pred_ex_rel e1 σ1 :
  head_step_pred e1 σ1 ↔ ∃ e2 σ2, head_step_rel e1 σ1 e2 σ2.
Proof.
  split.
  - intros [Hdet | Hdet];
      inversion Hdet; simplify_eq; do 2 eexists; try (by econstructor).
    Unshelve. all : apply 0%fin.
  - intros (?&?& H). inversion H; simplify_eq;
      (try by (left; econstructor));
      (try by (right; econstructor)).
    right. by eapply RandTapeOtherPSP; [|done|done].
Qed.

Lemma not_head_step_pred_dzero e1 σ1:
  ¬ head_step_pred e1 σ1 ↔ head_step e1 σ1 = dzero.
Proof.
  split.
  - intro Hnstep.
    apply dzero_ext.
    intros (e2 & σ2).
    destruct (Rlt_le_dec 0 (head_step e1 σ1 (e2, σ2))) as [H1%Rgt_lt | H2]; last first.
    { pose proof (pmf_pos (head_step e1 σ1) (e2, σ2)). destruct H2; lra. }
    apply head_step_support_equiv_rel in H1.
    assert (∃ e2 σ2, head_step_rel e1 σ1 e2 σ2) as Hex; eauto.
    by apply head_step_pred_ex_rel in Hex.
  - intros Hhead (e2 & σ2 & Hstep)%head_step_pred_ex_rel.
    apply head_step_support_equiv_rel in Hstep.
    assert (head_step e1 σ1 (e2, σ2) = 0); [|lra].
    rewrite Hhead //.
Qed.

Lemma det_or_prob_or_dzero e1 σ1 :
  det_head_step_pred e1 σ1
  ∨ prob_head_step_pred e1 σ1
  ∨ head_step e1 σ1 = dzero.
Proof.
  destruct (Rlt_le_dec 0 (SeriesC (head_step e1 σ1))) as [H1%Rlt_gt | [HZ | HZ]].
  - pose proof (SeriesC_gtz_ex (head_step e1 σ1) (pmf_pos (head_step e1 σ1)) H1) as [[e2 σ2] Hρ].
    pose proof (head_step_support_equiv_rel e1 e2 σ1 σ2) as [H3 H4].
    specialize (H3 Hρ).
    assert (head_step_pred e1 σ1) as []; [|auto|auto].
    apply head_step_pred_ex_rel; eauto.
  - by pose proof (pmf_SeriesC_ge_0 (head_step e1 σ1))
      as ?%Rle_not_lt.
  - apply SeriesC_zero_dzero in HZ. eauto.
Qed.

Lemma head_step_dzero_upd_tapes α e σ N zs z  :
  α ∈ dom σ.(tapes) →
  head_step e σ = dzero →
  head_step e (state_upd_tapes <[α:=(N; zs ++ [z]) : tape]> σ) = dzero.
Proof.
  intros Hdom Hz.
  destruct e; simpl in *;
    repeat case_match; done || inv_dzero; simplify_map_eq.
  (* TODO: [simplify_map_eq] should solve this? *)
  - destruct (decide (α = l1)).
    + simplify_eq.
      by apply not_elem_of_dom_2 in H5.
    + rewrite lookup_insert_ne // in H6.
      rewrite H5 in H6. done.
  - destruct (decide (α = l1)).
    + simplify_eq.
      by apply not_elem_of_dom_2 in H5.
    + rewrite lookup_insert_ne // in H6.
      rewrite H5 in H6. done.
  - destruct (decide (α = l1)).
    + simplify_eq.
      by apply not_elem_of_dom_2 in H5.
    + rewrite lookup_insert_ne // in H6.
      rewrite H5 in H6. done.
Qed.

Lemma det_head_step_upd_tapes N e1 σ1 e2 σ2 α z zs :
  det_head_step_rel e1 σ1 e2 σ2 →
  tapes σ1 !! α = Some (N; zs) →
  det_head_step_rel
    e1 (state_upd_tapes <[α := (N; zs ++ [z])]> σ1)
    e2 (state_upd_tapes <[α := (N; zs ++ [z])]> σ2).
Proof.
  inversion 1; try econstructor; eauto.
  (* Unsolved case *)
  intros. rewrite state_upd_tapes_heap. econstructor; eauto.
Qed.

Lemma upd_tape_some σ α N n ns :
  tapes σ !! α = Some (N; ns) →
  tapes (state_upd_tapes <[α:= (N; ns ++ [n])]> σ) !! α = Some (N; ns ++ [n]).
Proof.
  intros H. rewrite /state_upd_tapes /=. rewrite lookup_insert //.
Qed.

Lemma upd_tape_some_trivial σ α bs:
  tapes σ !! α = Some bs →
  state_upd_tapes <[α:=tapes σ !!! α]> σ = σ.
Proof.
  destruct σ. simpl.
  intros H.
  rewrite (lookup_total_correct _ _ _ H).
  f_equal.
  by apply insert_id.
Qed.

Lemma upd_diff_tape_comm σ α β bs bs':
  α ≠ β →
  state_upd_tapes <[β:= bs]> (state_upd_tapes <[α := bs']> σ) =
    state_upd_tapes <[α:= bs']> (state_upd_tapes <[β := bs]> σ).
Proof.
  intros. rewrite /state_upd_tapes /=. rewrite insert_commute //.
Qed.

Lemma upd_diff_tape_tot σ α β bs:
  α ≠ β →
  tapes σ !!! α = tapes (state_upd_tapes <[β:=bs]> σ) !!! α.
Proof. symmetry ; by rewrite lookup_total_insert_ne. Qed.

Lemma upd_tape_twice σ β bs bs' :
  state_upd_tapes <[β:= bs]> (state_upd_tapes <[β:= bs']> σ) = state_upd_tapes <[β:= bs]> σ.
Proof. rewrite /state_upd_tapes insert_insert //. Qed.

Lemma fresh_loc_upd_some σ α bs bs' :
  (tapes σ) !! α = Some bs →
  fresh_loc (tapes σ) = (fresh_loc (<[α:= bs']> (tapes σ))).
Proof.
  intros Hα.
  apply fresh_loc_eq_dom.
  by rewrite dom_insert_lookup_L.
Qed.

Lemma elem_fresh_ne {V} (ls : gmap loc V) k v :
  ls !! k = Some v → fresh_loc ls ≠ k.
Proof.
  intros; assert (is_Some (ls !! k)) as Hk by auto.
  pose proof (fresh_loc_is_fresh ls).
  rewrite -elem_of_dom in Hk.
  set_solver.
Qed.

Lemma fresh_loc_upd_swap σ α bs bs' bs'' :
  (tapes σ) !! α = Some bs →
  state_upd_tapes <[fresh_loc (tapes σ):=bs']> (state_upd_tapes <[α:=bs'']> σ)
  = state_upd_tapes <[α:=bs'']> (state_upd_tapes <[fresh_loc (tapes σ):=bs']> σ).
Proof.
  intros H.
  apply elem_fresh_ne in H.
  unfold state_upd_tapes.
  by rewrite insert_commute.
Qed.

Lemma fresh_loc_lookup σ α bs bs' :
  (tapes σ) !! α = Some bs →
  (tapes (state_upd_tapes <[fresh_loc (tapes σ):=bs']> σ)) !! α = Some bs.
Proof.
  intros H.
  pose proof (elem_fresh_ne _ _ _ H).
  by rewrite lookup_insert_ne.
Qed.

Lemma head_step_support_eq e1 e2 σ1 σ2 r :
  r > 0 → head_step e1 σ1 (e2, σ2) = r → head_step_rel e1 σ1 e2 σ2.
Proof. intros ? <-. by eapply head_step_support_equiv_rel. Qed.

Lemma prim_step_empty_tape σ α (z:Z) K N :
  (tapes σ) !! α = Some (N; []) -> prim_step (fill K (rand(#lbl:α) #z)) σ = prim_step (fill K (rand #z)) σ.
Proof.
  intros H.
  rewrite !fill_dmap; [|done|done|done|done].
  rewrite /dmap.
  f_equal.
  simpl. apply distr_ext; intros [e s].
  erewrite !head_prim_step_eq; simpl; last first.
  (** type classes dont work? *)
  { destruct (decide (Z.to_nat z=N)) as [<-|?] eqn:Heqn.
    all: eexists (_, σ); eapply head_step_support_equiv_rel;
      eapply head_step_support_eq; simpl; last first.
    - rewrite H. rewrite bool_decide_eq_true_2; last lia.
      eapply dmap_unif_nonzero; last done.
      intros ???. simplify_eq. done.
    - apply Rinv_pos. pose proof pos_INR_S (Z.to_nat z). lra.
    - rewrite H. case_bool_decide as H0; first lia.
      eapply dmap_unif_nonzero; last done.
      intros ???. by simplify_eq.
    - apply Rinv_pos. pose proof pos_INR_S (Z.to_nat z). lra.
  }
  { eexists (_, σ); eapply head_step_support_equiv_rel;
      eapply head_step_support_eq; simpl; last first.
    - eapply dmap_unif_nonzero; last done.
      intros ???. simplify_eq. done.
    - apply Rinv_pos. pose proof pos_INR_S (Z.to_nat z). lra.
  } rewrite H.
  case_bool_decide; last done.
  subst. done.
  Unshelve.
  all: exact (0%fin).
Qed.
  
