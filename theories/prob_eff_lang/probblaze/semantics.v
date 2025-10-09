From clutch.prob_eff_lang.probblaze Require Import syntax.
From Coq Require Import Reals Psatz.
From stdpp Require Export binders strings.
From stdpp Require Import gmap fin_maps countable fin.
From iris.algebra Require Export ofe.
From clutch.prelude Require Export stdpp_ext.
From clutch.prob Require Export distribution.
From clutch.common Require Export locations.
From iris.prelude Require Import options.

Set Default Proof Using "Type".

(* ========================================================================= *)
(** * Preliminary Definitions. *)

(* ------------------------------------------------------------------------- *)
(** Values. *)

Notation of_val := Val (only parsing).
Definition to_val (e : expr) : option val :=
  match e with Val v => Some v | _ => None end.


(* ------------------------------------------------------------------------- *)
(** Frames & Evaluation Contexts. *)

Definition fill_frame (f : frame) (e : expr) : expr :=
  match f with
  | AppLCtx v2 =>
      App e (of_val v2)
  | AppRCtx e1 =>
      App e1 e
  | DoCtx l =>
      Do (EffLabel l) e
  | HandleCtx l e2 e3 =>
      Handle (EffLabel l) e e2 e3
  | UnOpCtx op =>
      UnOp op e
  | BinOpLCtx op v2 =>
      BinOp op e (of_val v2)
  | BinOpRCtx op e1 =>
      BinOp op e1 e
  | IfCtx e1 e2 =>
      If e e1 e2
  | PairLCtx v2 =>
      Pair e (of_val v2)
  | PairRCtx e1 =>
      Pair e1 e
  | FstCtx =>
      Fst e
  | SndCtx =>
      Snd e
  | InjLCtx =>
      InjL e
  | InjRCtx =>
      InjR e
  | CaseCtx e1 e2 =>
      Case e e1 e2
  | AllocNLCtx v2 =>
      AllocN e (of_val v2)
  | AllocNRCtx e1 =>
      AllocN e1 e
  | LoadCtx =>
      Load e
  | StoreLCtx v2 =>
      Store e (of_val v2)
  | StoreRCtx e1 =>
      Store e1 e
  | AllocTapeCtx =>
      AllocTape e
  | RandLCtx v =>
      Rand e (of_val v) 
  | RandRCtx e1 =>
      Rand e1 e
  end.

Fixpoint fill (k : ectx) (e : expr) : expr :=
  match k with [] => e | f :: k => fill_frame f (fill k e) end. (* Consider what happens here *)

Definition get_frame (e : expr) : option (frame * expr) :=
  match e with
  | Var _ | Val _ | Rec _ _ _ | Effect _ _
  | Do (EffName _) _
  | Handle (EffName _) _ _ _ => None

  | App e1 e2 =>
      match to_val e2 with
      | None    => Some (AppRCtx e1, e2)
      | Some v2 => Some (AppLCtx v2, e1)
      end

  | Do (EffLabel l') e' =>
      Some (DoCtx l', e')

  | Handle (EffLabel l') e1 e2 e3 =>
      Some (HandleCtx l' e2 e3, e1)

  | UnOp op e =>
      Some (UnOpCtx op, e)

  | BinOp op e1 e2 =>
      match to_val e2 with
      | None    => Some (BinOpRCtx op e1, e2)
      | Some v2 => Some (BinOpLCtx op v2, e1)
      end

  | If e0 e1 e2 =>
      Some (IfCtx e1 e2, e0)

  | Pair e1 e2 =>
      match to_val e2 with
      | None    => Some (PairRCtx e1, e2)
      | Some v2 => Some (PairLCtx v2, e1)
      end

  | Fst e =>
      Some (FstCtx, e)

  | Snd e =>
      Some (SndCtx, e)

  | InjL e =>
      Some (InjLCtx, e)

  | InjR e =>
      Some (InjRCtx, e)

  | Case e0 e1 e2 =>
      Some (CaseCtx e1 e2, e0)

  | AllocN e1 e2 =>
      match to_val e2 with
      | None    => Some (AllocNRCtx e1, e2)
      | Some v2 => Some (AllocNLCtx v2, e1)
      end

  | Load e =>
      Some (LoadCtx, e)

  | Store e1 e2 =>
      match to_val e2 with
      | None    => Some (StoreRCtx e1, e2)
      | Some v2 => Some (StoreLCtx v2, e1)
      end

  | AllocTape e =>
      Some (AllocTapeCtx, e)

  | Rand e1 e2 =>
      match to_val e2 with
      | None    => Some (RandRCtx e1, e2)
      | Some v2 => Some (RandLCtx v2, e1)
      end

  end.

Definition sub_expr e e' := ∃ f, Some (f, e) = get_frame e'.

Lemma sub_expr_wf : well_founded sub_expr.
Proof.
  intros e.
  induction e; apply Acc_intro=>y [f' HSome]; simpl in HSome;
                                by (repeat match goal with
                                      | _ : Some _ = match ?e with | _ => _ end |- _ => destruct e
                                      | H : Some _ = Some _ |- _ => injection H as -> ->
                                      end).
Qed.

Definition sub_expr_intro f e e' : Some (f, e) = get_frame e' → sub_expr e e' :=
  λ H, @ex_intro frame (λ f, Some (f, e) = get_frame e') f H.

Fixpoint get_ectx (e : expr) : ectx * expr :=
  match e with
  | Var _ | Val _ | Rec _ _ _ | Effect _ _
  | Do (EffName _) _
  | Handle (EffName _) _ _ _ => ([], e)

  | App e1 e2 =>
      match to_val e2 with
      | None    => let (k, e') := get_ectx e2 in (AppRCtx e1 :: k, e')
      | Some v2 => let (k, e') := get_ectx e1 in (AppLCtx v2 :: k, e')
      end

  | Do (EffLabel l') e =>
      let (k, e') := get_ectx e in (DoCtx l' :: k, e')

  | Handle (EffLabel l') e1 e2 e3 =>
      let (k, e') := get_ectx e1 in (HandleCtx l' e2 e3 :: k, e')

  | UnOp op e =>
      let (k, e') := get_ectx e in (UnOpCtx op :: k, e')

  | BinOp op e1 e2 =>
      match to_val e2 with
      | None    => let (k, e') := get_ectx e2 in (BinOpRCtx op e1 :: k, e')
      | Some v2 => let (k, e') := get_ectx e1 in (BinOpLCtx op v2 :: k, e')
      end

  | If e0 e1 e2 =>
      let (k, e') := get_ectx e0 in (IfCtx e1 e2 :: k, e')

  | Pair e1 e2 =>
      match to_val e2 with
      | None    => let (k, e') := get_ectx e2 in (PairRCtx e1 :: k, e')
      | Some v2 => let (k, e') := get_ectx e1 in (PairLCtx v2 :: k, e')
      end

  | Fst e =>
      let (k, e') := get_ectx e in (FstCtx :: k, e')

  | Snd e =>
      let (k, e') := get_ectx e in (SndCtx :: k, e')

  | InjL e =>
      let (k, e') := get_ectx e in (InjLCtx :: k, e')

  | InjR e =>
      let (k, e') := get_ectx e in (InjRCtx :: k, e')

  | Case e0 e1 e2 =>
      let (k, e') := get_ectx e0 in (CaseCtx e1 e2 :: k, e')

  | AllocN e1 e2 =>
      match to_val e2 with
      | None    => let (k, e') := get_ectx e2 in (AllocNRCtx e1 :: k, e')
      | Some v2 => let (k, e') := get_ectx e1 in (AllocNLCtx v2 :: k, e')
      end

  | Load e =>
      let (k, e') := get_ectx e in (LoadCtx :: k, e')

  | Store e1 e2 =>
      match to_val e2 with
      | None    => let (k, e') := get_ectx e2 in (StoreRCtx e1 :: k, e')
      | Some v2 => let (k, e') := get_ectx e1 in (StoreLCtx v2 :: k, e')
      end

  | AllocTape e =>
      let (k, e') := get_ectx e in (AllocTapeCtx :: k, e')

  | Rand e1 e2 =>
      match to_val e2 with
      | None    => let (k, e') := get_ectx e2 in (RandRCtx e1 :: k, e')
      | Some v2 => let (k, e') := get_ectx e1 in (RandLCtx v2 :: k, e')
      end
  
  end.


(* ------------------------------------------------------------------------- *)
(** Neutral Contexts. *)

Definition frame_label (f : frame) : option label :=
  match f with HandleCtx l _ _ => Some l | _ => None end.

Definition ectx_labels (k : ectx) : list label :=
  omap frame_label k.

Lemma ectx_labels_app k k' : ectx_labels (k ++ k') = ectx_labels k ++ ectx_labels k'.
Proof. by apply omap_app. Qed.

Lemma ectx_labels_cons f k :
  ectx_labels (f :: k) =
  (option_rect (λ _, list label) (λ l, [l]) [] (frame_label f)) ++ ectx_labels k.
Proof. rewrite (ectx_labels_app [f]). f_equiv. by destruct f=>//. Qed.

Lemma Permutation_ectx_labels k k' : k ≡ₚ k' → ectx_labels k ≡ₚ ectx_labels k'.
Proof. by apply omap_Permutation. Qed.

Class NeutralFrame (ls : list label) (f : frame) := {
  neutral_frame : option_rect (λ _, Prop) (λ l, l ∉ ls) True (frame_label f)
}.

Class NeutralEctx (ls : list label) (k : ectx) := {
  neutral_ectx : ∀ l, l ∈ ls → l ∉ ectx_labels k
}.

Instance NeutralEctx_nil ls : NeutralEctx ls [].
Proof. constructor. intros ? _. by apply not_elem_of_nil. Qed.

Lemma NeutralEctx_cons ls f k :
  NeutralFrame ls f →
  NeutralEctx ls k →
  NeutralEctx ls (f :: k).
Proof.
  intros Hf Hk. constructor. intros l Hin_ls. simpl.
  destruct f=>//=; try (by apply Hk);
  rewrite not_elem_of_cons; split; try (by apply Hk).
  specialize neutral_frame; simpl. set_solver.
Qed.


Instance AppRCtx_NeutralEctx ls (e1 : expr) k :
  NeutralEctx ls k → NeutralEctx ls (AppRCtx e1 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance AppLCtx_NeutralEctx ls (v2 : val) k :
  NeutralEctx ls k → NeutralEctx ls (AppLCtx v2 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance DoCtx_NeutralEctx (ls : list label) (l' : label) k :
  NeutralEctx ls k →  NeutralEctx ls (DoCtx l' :: k).
Proof. by intros ?; apply NeutralEctx_cons. Qed.

Instance HandleCtx_NeutralEctx (ls : list label) (l' : label) (e2 e3 : expr) k :
  l' ∉ ls →
  NeutralEctx ls k → 
  NeutralEctx ls (HandleCtx l' e2 e3 :: k).
Proof. by intros ?; apply NeutralEctx_cons. Qed.

Instance UnOpCtx_NeutralEctx ls op k : NeutralEctx ls k → NeutralEctx ls (UnOpCtx op :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance BinOpLCtx_NeutralEctx ls op v2 k : NeutralEctx ls k → NeutralEctx ls (BinOpLCtx op v2 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance BinOpRCtx_NeutralEctx ls op e1 k : NeutralEctx ls k → NeutralEctx ls (BinOpRCtx op e1 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance IfCtx_NeutralEctx ls e1 e2 k : NeutralEctx ls k → NeutralEctx ls (IfCtx e1 e2 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance PairLCtx_NeutralEctx ls v2 k : NeutralEctx ls k → NeutralEctx ls (PairLCtx v2 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance PairRCtx_NeutralEctx ls e1 k : NeutralEctx ls k → NeutralEctx ls (PairRCtx e1 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance FstCtx_NeutralEctx ls k : NeutralEctx ls k → NeutralEctx ls (FstCtx :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance SndCtx_NeutralEctx ls k : NeutralEctx ls k → NeutralEctx ls (SndCtx :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance InjLCtx_NeutralEctx ls k : NeutralEctx ls k → NeutralEctx ls (InjLCtx :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance InjRCtx_NeutralEctx ls k : NeutralEctx ls k → NeutralEctx ls (InjRCtx :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance CaseCtx_NeutralEctx ls e1 e2 k : NeutralEctx ls k → NeutralEctx ls (CaseCtx e1 e2 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance AllocNLCtx_NeutralEctx ls v2 k : NeutralEctx ls k → NeutralEctx ls (AllocNLCtx v2 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance AllocNRCtx_NeutralEctx ls e1 k : NeutralEctx ls k → NeutralEctx ls (AllocNRCtx e1 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance LoadCtx_NeutralEctx ls k : NeutralEctx ls k → NeutralEctx ls (LoadCtx :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance StoreLCtx_NeutralEctx ls v2 k : NeutralEctx ls k → NeutralEctx ls (StoreLCtx v2 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance StoreRCtx_NeutralEctx ls e1 k : NeutralEctx ls k → NeutralEctx ls (StoreRCtx e1 :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance AllocTapeCtx_NeutralEctx ls k : NeutralEctx ls k → NeutralEctx ls (AllocTapeCtx :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance RandLCtx_NeutralEctx ls v k : NeutralEctx ls k → NeutralEctx ls (RandLCtx v :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance RandRCtx_NeutralEctx ls e k : NeutralEctx ls k → NeutralEctx ls (RandRCtx e :: k).
Proof. by apply NeutralEctx_cons. Qed.

Instance NeutralEctx_dec ls k : Decision (NeutralEctx ls k).
Proof.
  ecase (stdpp.list.Forall_dec (λ l, l ∉ ectx_labels k)); [left|right].
  - constructor. by apply stdpp.list.Forall_forall. 
  - intros Habsurd. apply n. rewrite stdpp.list.Forall_forall. by apply neutral_ectx.
Qed.

Lemma Permutation_NeutralEctx ls k k' :
  k ≡ₚ k' →
  NeutralEctx ls k →
  NeutralEctx ls k'.
Proof.
  intros Hperm Hneutral. constructor; intros ? Hin_ls Hin_k.
  apply (neutral_ectx l Hin_ls).
  apply (elem_of_Permutation_proper _ (ectx_labels k) (ectx_labels k')); [|done].
  by apply Permutation_ectx_labels.
Qed.

Lemma NeutralEctx_app ls k k' :
  NeutralEctx ls k → NeutralEctx ls k' → NeutralEctx ls (k ++ k').
Proof.
  intros??; constructor; intros l Hin_ls Hin_app.
  rewrite ectx_labels_app in Hin_app.
  rewrite elem_of_app in Hin_app.
  destruct Hin_app as [Hin_k|Hin_k'].
  - by apply (neutral_ectx l Hin_ls Hin_k).
  - by apply (neutral_ectx l Hin_ls Hin_k').
Qed.

Lemma NeutralEctx_app_l ls k k' : NeutralEctx ls (k ++ k') → NeutralEctx ls k.
Proof.
  intros ?Hneutral. constructor. intros l Hin_ls Hin_k.
  apply (neutral_ectx l Hin_ls). rewrite ectx_labels_app elem_of_app. by left.
Qed.

Lemma NeutralEctx_app_r ls k k' : NeutralEctx ls (k ++ k') → NeutralEctx ls k'.
Proof.
  intros ?Hneutral. constructor. intros l Hin_ls Hin_k.
  apply (neutral_ectx l Hin_ls). rewrite ectx_labels_app elem_of_app. by right.
Qed.

Lemma NeutralEctx_cons_inv ls f k :
  NeutralEctx ls (f :: k) → NeutralFrame ls f ∧ NeutralEctx ls k.
Proof.
  intros Hneutral. split; [|by apply (NeutralEctx_app_r _ [f])].
  specialize (NeutralEctx_app_l _ [f] _ Hneutral) as Hf.
  destruct f=>//=; simpl; constructor; intros Hin_ls. clear Hneutral.
  by apply (neutral_ectx l Hin_ls), elem_of_list_singleton.
Qed.

Lemma NeutralEctx_ectx_labels_iff ls k :
  NeutralEctx ls k ↔ (∀ l, l ∈ ls → l ∈ ectx_labels k → False).
Proof. by split; intros ?; [apply neutral_ectx|constructor]. Qed.

Lemma NeutralEctx_ectx_labels_singleton l k : NeutralEctx [l] k ↔ l ∉ ectx_labels k.
Proof. by rewrite NeutralEctx_ectx_labels_iff; set_solver. Qed.

Instance NeutralFrame_label_cons_inv_1 l ls f :
  NeutralFrame (l :: ls) f → NeutralFrame [l] f.
Proof.
  intros Hk. constructor. specialize neutral_frame.
  destruct (frame_label f); set_solver.
Qed.

Instance NeutralFrame_label_cons_inv_2 l ls f :
  NeutralFrame (l :: ls) f → NeutralFrame ls f.
Proof.
  intros Hk. constructor. specialize neutral_frame.
  destruct (frame_label f); set_solver.
Qed.

Instance NeutralEctx_label_cons_inv_1 l ls k :
  NeutralEctx (l :: ls) k → NeutralEctx [l] k.
Proof.
  intros Hk. constructor. intros l'.
  rewrite elem_of_list_singleton. intros ->.
  apply neutral_ectx. rewrite elem_of_cons. by left.
Qed.

Instance NeutralEctx_label_cons_inv_2 l ls k :
  NeutralEctx (l :: ls) k → NeutralEctx ls k.
Proof.
  intros Hk. constructor. intros l' Hin_ls.
  apply neutral_ectx. rewrite elem_of_cons. by right.
Qed.

(* ------------------------------------------------------------------------- *)
(** Effects. *)

Definition to_eff (e : expr) : option (label * val * ectx) :=
  match get_ectx e with
  | (k, Val v) =>
      match reverse k with
      | DoCtx l :: k' => Some (l, v, reverse k')
      | _ => None
      end
  | _ =>
      None
  end.

Definition of_eff (l : label) (v : val) (k : ectx) :=
  fill k (Do (EffLabel l) (Val v)).

Definition not_eff (e : expr) : Prop :=
  to_eff e = None ∨ ∃ l v k, to_eff e = Some (l, v, k) ∧ l ∈ ectx_labels k.

Global Instance not_eff_dec e : Decision (not_eff e).
Proof.
  destruct (to_eff e) as [((l, v), k)|] eqn:He; [|by left; left].
  case (decide (l ∈ ectx_labels k)); [intro Hin|intro Hnot_in]; [left|right].
  - right; rewrite He //=. by eauto.
  - intros [He'|[? [? [? [He' ?]]]]]; rewrite He' in He; [done|].
    by injection He as -> -> ->.
Qed.

(* ------------------------------------------------------------------------- *)
(** Properties. *)

(* -------------------------------------------------------------------------- *)
(* [to_val]. *)

Lemma of_to_val e v : to_val e = Some v → e = of_val v.
Proof. destruct e=>//=. by intros [= <-]. Qed.

Instance of_val_inj : Inj (=) (=) of_val.
Proof. by intros ?? [=]. Qed.

(* ------------------------------------------------------------------------- *)
(* [fill_frame]. *)

Instance fill_frame_inj f : Inj (=) (=) (fill_frame f).
Proof. induction f; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_frame_val f e : to_val (fill_frame f e) = None.
Proof. induction f; simplify_option_eq; eauto. Qed.

Lemma fill_frame_no_val_inj f1 f2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_frame f1 e1 = fill_frame f2 e2 → f1 = f2.
Proof. revert f1. induction f2, f1; naive_solver eauto with f_equal. Qed.

(* ------------------------------------------------------------------------- *)
(* [fill]. *)

Instance fill_inj k : Inj (=) (=) (fill k).
Proof. induction k; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_app k k' e : fill (k ++ k') e = fill k (fill k' e).
Proof. by induction k as [|f k]; simpl; [|rewrite IHk]. Qed.

Lemma fill_val k e v : to_val (fill k e) = Some v → k = [] ∧ e = Val v.
Proof.
  destruct k as [|f k].
  - by intro H; rewrite -(of_to_val _ _ H).
  - by destruct f; naive_solver.
Qed.

Lemma fill_inv k e : get_frame (fill k e) = None → k = [].
Proof.
  induction k as [|f k] =>//=.
  destruct f =>//=; by repeat destruct (to_val _).
Qed.

Lemma fill_inv' k e e' : fill k e = e' → get_frame e' = None → k = [] ∧ e = e'.
Proof. intros <- Hget_frame. by rewrite (fill_inv _ _ Hget_frame). Qed.

Lemma fill_val_inv k e v : fill k e = Val v → k = [] ∧ e = Val v.
Proof. intros ?. by apply fill_inv'. Qed.

Lemma fill_not_val k e : to_val e = None → to_val (fill k e) = None.
Proof. induction k as [|f k]; eauto. intros ?; by apply fill_frame_val. Qed.


(* ------------------------------------------------------------------------- *)
(* [get_frame & get_ectx]. *)

Lemma get_ectx_alt (e : expr) :
  get_ectx e = match get_frame e with None => ([], e) | Some (f, e) =>
                 let (k, e') := get_ectx e in (f :: k, e')
               end.
Proof.
  destruct e=>//=;
    try solve [
      (* Solve the cases where we have a L and R context *)
      by repeat destruct (to_val _)
    ].
  - (* Do*) destruct n=>//=; injection 1 as Hf He; by rewrite Hf He.
  - (* Handle *) destruct n=>//=; injection 1 as Hf He; by rewrite Hf He.
Qed.

Lemma get_frame_Some e f e' :
  get_frame e = Some (f , e') → e = fill_frame f e'.
Proof.
  destruct e=>//=;
    try solve [
      (* Solve the simple cases like [Fst] *)
      by inversion 1 |
      (* Solve the cases where we have a L and R context *)
      repeat (destruct (to_val _) eqn:H; [apply of_to_val in H as ->|]); by inv 1
    ].
  - (* Do *) destruct n=>//. by inversion 1.
  - (* Handle *) destruct n=>//. by inversion 1.
Qed.

Lemma get_ectx_spec e e' k : get_ectx e = (k, e') → e = fill k e'.
Proof.
  revert e' k.
  induction (sub_expr_wf e).
  intros e' k'.
  rename x into e, H0 into IH, H into Hacc.
  rewrite get_ectx_alt.
  destruct (get_frame e) as [(f, e'')|] eqn:Hget_frame; last
  by injection 1 as <- <-.
  destruct (get_ectx e'') as (k'', e''') eqn:He''.
  injection 1 as <- <-. simpl. rewrite -(IH e''); last done.
  - by apply get_frame_Some.
  - by exists f.
Qed.

Lemma get_frame_fill_frame f e :
  to_val e = None →
  get_frame (fill_frame f e) = Some (f, e).
Proof. by intros He; destruct f=>//=; rewrite He. Qed.

Lemma get_ectx_fill_frame e e' f k :
  to_val e = None →
  (k, e') = get_ectx e →
  get_ectx (fill_frame f e) = (f :: k, e').
Proof.
  intros Hval He.
  rewrite get_ectx_alt get_frame_fill_frame; [|done].
  by rewrite -He.
Qed.

Lemma get_ectx_fill e e' k k' :
  to_val e = None →
  (k, e') = get_ectx e →
  get_ectx (fill k' e) = (k' ++ k, e').
Proof.
  revert e e' k; induction k'; intros ??? Hval Hget_ectx.
  - by rewrite -Hget_ectx.
  - simpl. rewrite (get_ectx_fill_frame _ e' _ (k' ++ k)); first done.
    + by apply fill_not_val.
    + symmetry. by apply IHk'.
Qed.

Lemma get_ectx_fill' e1 e1' e2 k k' :
  to_val e1 = None →
  e2 = fill k' e1 →
  (k, e1') = get_ectx e1 →
  get_ectx e2 = (k' ++ k, e1').
Proof. intros ? ->. by apply get_ectx_fill. Qed.

(* ------------------------------------------------------------------------- *)
(* [to_eff]. *)

Lemma to_eff_eff l v : to_eff (Do (EffLabel l) (Val v)) = Some (l, v, []).
Proof. by rewrite /to_eff //= reverse_nil. Qed.

Lemma to_eff_get_ectx e l v k :
  to_eff e = Some (l, v, k) → get_ectx e = (k ++ [DoCtx l], Val v).
Proof.
  rewrite /to_eff.
  destruct (get_ectx e) as [k' e'] eqn:Hget_ectx.
  destruct (to_val e') as [v'|] eqn:Hval.
  - rewrite (of_to_val _ _ Hval).
    destruct k' as [|f k'' _] eqn:Hk using rev_ind; [done|].
    rewrite reverse_app //= reverse_involutive.
    destruct f=>//=. by injection 1 as -> -> ->.
  - by destruct e'=>//.
Qed.

Lemma to_eff_get_ectx' e l v k :
  get_ectx e = (k ++ [DoCtx l], Val v) → to_eff e = Some (l, v, k).
Proof. intros He. by rewrite /to_eff He reverse_app //= reverse_involutive. Qed.

Lemma to_eff_get_ectx_iff e l v k :
  to_eff e = Some (l, v, k) ↔ get_ectx e = (k ++ [DoCtx l], Val v).
Proof. by split; [apply to_eff_get_ectx|apply to_eff_get_ectx']. Qed.

Lemma of_to_eff e l v k : to_eff e = Some (l, v, k) → of_eff l v k = e.
Proof.
  intros He. rewrite to_eff_get_ectx_iff in He.
  by rewrite (get_ectx_spec _ _ _ He) fill_app //=.
Qed.

Lemma to_eff_not_val e : is_Some (to_eff e) → to_val e = None.
Proof.
  intros [((l, v), k) He]. rewrite -(of_to_eff _ _ _ _ He).
  destruct k as [|f k]; [done|].
  by destruct f=>//=.
Qed.

Lemma of_eff_inj l1 v1 k1 l2 v2 k2 :
  of_eff l1 v1 k1 = of_eff l2 v2 k2 → l1 = l2 ∧ v1 = v2 ∧ k1 = k2.
Proof.
  revert k1 k2; induction k1; intros k2.
  - unfold of_eff. simpl.
    destruct k2=>//=.
    + inversion 1. by auto.
    + destruct f=>//=; inversion 1.
      destruct k2=>//=; destruct f=>//=.
  - destruct a=>//=; destruct k2=>//=;
    try destruct f=>//=;
    rewrite /of_eff //=; inv 1;
      try solve [
        match goal with
        | H : fill _ _ = fill _ _ |- _ => by apply IHk1 in H as (-> & -> & ->)
        | H : fill _ _ = Val _ |- _ => apply fill_val_inv in H as [_ [=]]
        | H : Val _ = fill _ _ |- _ => apply sym_eq, fill_val_inv in H as [_ [=]]
        end
      ].
Qed.

(* ------------------------------------------------------------------------- *)
(* [fill] & [to_eff]. *)

Lemma to_eff_fill_frame l f k e v :
  to_eff e = Some (l, v, k) →
  to_eff (fill_frame f e) = Some (l, v, f :: k).
Proof.
  intros He. rewrite /to_eff.
  rewrite to_eff_get_ectx_iff in He.
  rewrite (get_ectx_fill_frame _ (Val v) _ (k ++ [DoCtx l])); last done.
  - by rewrite reverse_cons reverse_app //= reverse_app reverse_involutive //=. 
  - apply to_eff_not_val. exists (l, v, k).
    by rewrite to_eff_get_ectx_iff.
Qed.

Lemma to_eff_fill l k k' e v :
  to_eff e = Some (l, v, k') → to_eff (fill k e) = Some (l, v, k ++ k').
Proof.
  induction k as [|f k]; [done|].
  intros He; simpl.
  apply to_eff_fill_frame.
  by apply IHk.
Qed.

Lemma fill_not_eff k e :
  to_val e = None →
  to_eff e = None →
  to_eff (fill k e) = None.
Proof.
  intros He.
  rewrite /to_eff.
  destruct (get_ectx e) as (k', e') eqn:Hget_ectx.
  rewrite (get_ectx_fill _ e' k'); try done.
  destruct k' as [|f k'] using rev_ind.
  - destruct e'=>//. exfalso.
    specialize (get_ectx_spec _ _ _ Hget_ectx).
    by destruct e=>//.
  - rewrite !reverse_app //=.
    destruct e'=>//. by destruct f=>//.
Qed.

Lemma to_of_eff l v k : to_eff (of_eff l v k) = Some (l, v, k).
Proof.
  specialize (to_eff_fill l k [] (Do (EffLabel l) (Val v)) v) as Heq.
  rewrite app_nil_r in Heq.
  by apply Heq.
Qed.

Lemma of_eff_not_val l v k : to_val (of_eff l v k) = None.
Proof. apply to_eff_not_val. by rewrite to_of_eff. Qed.

Lemma to_eff_of_eff' l k v :
  l ∉ ectx_labels k →
  to_eff (of_eff l v k) = Some (l, v, k).
Proof. intros Hnot_in_k. by apply to_of_eff. Qed.

(* -------------------------------------------------------------------------- *)
(** Substitution. *)

Fixpoint val_subst (x : string) (v : val) (e : expr) : expr :=
  match e with
  | Val _ =>
      e
  | Var y =>
      if decide (x = y) then Val v else Var y
  | Effect s e =>
      Effect s (val_subst x v e)
  | Do n e =>
      Do n (val_subst x v e)
  | Handle n e1 e2 e3 =>
      Handle n (val_subst x v e1) (val_subst x v e2) (val_subst x v e3)
  | Rec f y e =>
      Rec f y $ if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then val_subst x v e else e
  | App e1 e2 =>
      App (val_subst x v e1) (val_subst x v e2)
  | UnOp op e =>
      UnOp op (val_subst x v e)
  | BinOp op e1 e2 =>
      BinOp op (val_subst x v e1) (val_subst x v e2)
  | If e0 e1 e2 =>
      If (val_subst x v e0) (val_subst x v e1) (val_subst x v e2)
  | Pair e1 e2 =>
      Pair (val_subst x v e1) (val_subst x v e2)
  | Fst e =>
      Fst (val_subst x v e)
  | Snd e =>
      Snd (val_subst x v e)
  | InjL e =>
      InjL (val_subst x v e)
  | InjR e =>
      InjR (val_subst x v e)
  | Case e0 e1 e2 =>
      Case (val_subst x v e0) (val_subst x v e1) (val_subst x v e2)
  | AllocN e1 e2 =>
      AllocN (val_subst x v e1) (val_subst x v e2)
  | Load e =>
      Load (val_subst x v e)
  | Store e1 e2 =>
      Store (val_subst x v e1) (val_subst x v e2)
  | AllocTape e =>
      AllocTape (val_subst x v e)
  | Rand e1 e2 =>
      Rand (val_subst x v e1) (val_subst x v e2)
  end.

Definition val_subst' (b : binder) (v : val) : expr → expr :=
  match b with BNamed x => val_subst x v | BAnon => Datatypes.id end.

Fixpoint lbl_subst (s : string) (l : label) (e : expr) : expr :=
  match e with
  | Val _ | Var _ =>
      e
  | Effect s' e' =>
      if decide (s = s') then e else Effect s' (lbl_subst s l e')

  | Do (EffLabel _ as n') e' =>
      Do n' (lbl_subst s l e')
  | Do (EffName s' as n') e' =>
      Do (if decide (s = s') then (EffLabel l) else n') (lbl_subst s l e')

  | Handle (EffLabel _ as n') e1 e2 e3 =>
      Handle n' (lbl_subst s l e1) (lbl_subst s l e2) (lbl_subst s l e3)
  | Handle (EffName s' as n') e1 e2 e3 =>
      Handle (if decide (s = s') then (EffLabel l) else n')
        (lbl_subst s l e1) (lbl_subst s l e2) (lbl_subst s l e3)

  | Rec f y e =>
      Rec f y $ lbl_subst s l e
  | App e1 e2 =>
      App (lbl_subst s l e1) (lbl_subst s l e2)
  | UnOp op e =>
      UnOp op (lbl_subst s l e)
  | BinOp op e1 e2 =>
      BinOp op (lbl_subst s l e1) (lbl_subst s l e2)
  | If e0 e1 e2 =>
      If (lbl_subst s l e0) (lbl_subst s l e1) (lbl_subst s l e2)
  | Pair e1 e2 =>
      Pair (lbl_subst s l e1) (lbl_subst s l e2)
  | Fst e =>
      Fst (lbl_subst s l e)
  | Snd e =>
      Snd (lbl_subst s l e)
  | InjL e =>
      InjL (lbl_subst s l e)
  | InjR e =>
      InjR (lbl_subst s l e)
  | Case e0 e1 e2 =>
      Case (lbl_subst s l e0) (lbl_subst s l e1) (lbl_subst s l e2)
  | AllocN e1 e2 =>
      AllocN (lbl_subst s l e1) (lbl_subst s l e2)
  | Load e =>
      Load (lbl_subst s l e)
  | Store e1 e2 =>
      Store (lbl_subst s l e1) (lbl_subst s l e2)
  | AllocTape e =>
      AllocTape (lbl_subst s l e)
  | Rand e1 e2 =>
      Rand (lbl_subst s l e1) (lbl_subst s l e2)
  end.

(* -------------------------------------------------------------------------- *)
(** Unboxed values. *)

Definition val_is_unboxed (v : val) : Prop :=
  match v with
  | LitV l => True
  | InjLV (LitV l) => True
  | InjRV (LitV l) => True
  | _ => False
  end.

Global Instance val_is_unboxed_dec v : Decision (val_is_unboxed v).
Proof. destruct v as [ | | | | [] | [] ]; simpl; exact (decide _). Defined.

(** We just compare the word-sized representation of two values, without looking
into boxed data.  This works out fine if at least one of the to-be-compared
values is unboxed (exploiting the fact that an unboxed and a boxed value can
never be equal because these are disjoint sets). *)
Definition vals_compare_safe (vl v1 : val) : Prop :=
  val_is_unboxed vl ∨ val_is_unboxed v1.
Global Arguments vals_compare_safe !_ !_ /.

(* ========================================================================== *)
(** * Reduction Relation. *)

(* Operations *)
Definition un_op_eval (op : un_op) (v : val) : option val :=
  match op, v with
  | NegOp, LitV (LitBool b) => Some $ LitV $ LitBool (negb b)
  | NegOp, LitV (LitInt n) => Some $ LitV $ LitInt (Z.lnot n)
  | MinusUnOp, LitV (LitInt n) => Some $ LitV $ LitInt (- n)
  | _, _ => None
  end.

Definition bin_op_eval_int (op : bin_op) (n1 n2 : Z) : option base_lit :=
  match op with
  | PlusOp => Some $ LitInt (n1 + n2)
  | MinusOp => Some $ LitInt (n1 - n2)
  | MultOp => Some $ LitInt (n1 * n2)
  | QuotOp => Some $ LitInt (n1 `quot` n2)
  | RemOp => Some $ LitInt (n1 `rem` n2)
  | AndOp => Some $ LitInt (Z.land n1 n2)
  | OrOp => Some $ LitInt (Z.lor n1 n2)
  | XorOp => Some $ LitInt (Z.lxor n1 n2)
  | ShiftLOp => Some $ LitInt (n1 ≪ n2)
  | ShiftROp => Some $ LitInt (n1 ≫ n2)
  | LeOp => Some $ LitBool (bool_decide (n1 ≤ n2))
  | LtOp => Some $ LitBool (bool_decide (n1 < n2))
  | EqOp => Some $ LitBool (bool_decide (n1 = n2))
  | OffsetOp => None (* Pointer arithmetic *)
  end%Z.

Definition bin_op_eval_bool (op : bin_op) (b1 b2 : bool) : option base_lit :=
  match op with
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp => None (* Arithmetic *)
  | AndOp => Some (LitBool (b1 && b2))
  | OrOp => Some (LitBool (b1 || b2))
  | XorOp => Some (LitBool (xorb b1 b2))
  | ShiftLOp | ShiftROp => None (* Shifts *)
  | LeOp | LtOp => None (* InEquality *)
  | EqOp => Some (LitBool (bool_decide (b1 = b2)))
  | OffsetOp => None (* Pointer arithmetic *)
  end.

Definition bin_op_eval_loc (op : bin_op) (l1 : loc) (v2 : base_lit) : option base_lit :=
  match op, v2 with
  | OffsetOp, LitInt off => Some $ LitLoc (l1 +ₗ off)
  | LeOp, LitLoc l2 => Some $ LitBool (bool_decide (l1 ≤ₗ l2))
  | LtOp, LitLoc l2 => Some $ LitBool (bool_decide (l1 <ₗ l2))
  | _, _ => None
  end.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  if decide (op = EqOp) then
    if decide (vals_compare_safe v1 v2) then
      Some $ LitV $ LitBool $ bool_decide (v1 = v2)
    else
      None
  else
    match v1, v2 with
    | LitV (LitInt n1), LitV (LitInt n2) => LitV <$> bin_op_eval_int op n1 n2
    | LitV (LitBool b1), LitV (LitBool b2) => LitV <$> bin_op_eval_bool op b1 b2
    | LitV (LitLoc l1), LitV v2 => LitV <$> bin_op_eval_loc op l1 v2
    | _, _ => None
    end.

(* Compute next label. *)
Definition label_succ : label → label := λ l,
                                           Label (S (label_car l))%nat.

Definition state_upd_next_label (f : label → label) (σ : state) : state :=
  {| next_label := f σ.(next_label); heap := σ.(heap); tapes := σ.(tapes) |}.
Global Arguments state_upd_next_label _ !_ /.

Definition state_upd_heap (f: gmap loc (option val) → gmap loc (option val)) (σ: state) : state :=
  {| heap := f σ.(heap); next_label := σ.(next_label); tapes := σ.(tapes) |}.
Global Arguments state_upd_heap _ !_ /.

Definition state_upd_tapes (f : gmap loc tape → gmap loc tape) (σ : state) : state :=
  {| next_label := σ.(next_label); heap := σ.(heap); tapes := f σ.(tapes) |}.
Global Arguments state_upd_tapes _ !_ /.

Lemma state_upd_tapes_twice σ l n xs ys :
  state_upd_tapes <[l:=(n; ys)]> (state_upd_tapes <[l:=(n; xs)]> σ) = state_upd_tapes <[l:=(n; ys)]> σ.
Proof. rewrite /state_upd_tapes /=. f_equal. apply insert_insert. Qed.

Lemma state_upd_tapes_same σ σ' l n xs ys :
  state_upd_tapes <[l:=(n; ys)]> σ = state_upd_tapes <[l:=(n; xs)]> σ' -> xs = ys.
Proof. rewrite /state_upd_tapes /=. intros K. simplify_eq.
       rewrite map_eq_iff in H0.
       specialize (H0 l).
       rewrite !lookup_insert in H0.
       by simplify_eq.
Qed.

Lemma state_upd_tapes_no_change σ l n ys :
  tapes σ !! l = Some (n; ys)-> 
  state_upd_tapes <[l:=(n; ys)]> σ = σ .
Proof.
  destruct σ as [? t]. simpl.
  intros Ht.
  f_equal.
  apply insert_id. done.
Qed.

Lemma state_upd_tapes_same' σ σ' l n xs (x y : fin (S n)) :
  state_upd_tapes <[l:=(n; xs++[x])]> σ = state_upd_tapes <[l:=(n; xs++[y])]> σ' -> x = y.
Proof. intros H. apply state_upd_tapes_same in H.
       by simplify_eq.
Qed.

Lemma state_upd_tapes_neq' σ σ' l n xs (x y : fin (S n)) :
  x≠y -> state_upd_tapes <[l:=(n; xs++[x])]> σ ≠ state_upd_tapes <[l:=(n; xs++[y])]> σ'.
Proof. move => H /state_upd_tapes_same ?. simplify_eq.
Qed.

Fixpoint heap_array (l : loc) (vs : list val) : gmap loc (option val) :=
  match vs with
  | [] => ∅
  | v :: vs' => {[l := Some v]} ∪ heap_array (l +ₗ 1) vs'
  end.

Lemma heap_array_singleton l v : heap_array l [v] = {[l := Some v]}.
Proof. by rewrite /heap_array right_id. Qed.

Lemma heap_array_lookup l vs ow k :
  heap_array l vs !! k = Some ow ↔
  ∃ j w, (0 ≤ j)%Z ∧ k = l +ₗ j ∧ ow = Some w ∧ vs !! (Z.to_nat j) = Some w.
Proof.
  revert k l; induction vs as [|v' vs IH]=> l' l /=.
  { rewrite lookup_empty. naive_solver lia. }
  rewrite -insert_union_singleton_l lookup_insert_Some IH. split.
  - intros [[-> ?] | (Hl & j & w & ? & -> & -> & ?)].
    { eexists 0, _. rewrite loc_add_0. naive_solver lia. }
    eexists (1 + j)%Z, _. rewrite loc_add_assoc !Z.add_1_l Z2Nat.inj_succ; auto with lia.
  - intros (j & w & ? & -> & -> & Hil). destruct (decide (j = 0)); simplify_eq/=.
    { rewrite loc_add_0; eauto. }
    right. split.
    { rewrite -{1}(loc_add_0 l). intros ?%(inj (loc_add _)); lia. }
    assert (Z.to_nat j = S (Z.to_nat (j - 1))) as Hj.
    { rewrite -Z2Nat.inj_succ; last lia. f_equal; lia. }
    rewrite Hj /= in Hil.
    eexists (j - 1)%Z, _. rewrite loc_add_assoc Z.add_sub_assoc Z.add_simpl_l.
    auto with lia.
Qed.

Lemma heap_array_map_disjoint (h : gmap loc (option val)) (l : loc) (vs : list val) :
  (∀ i, (0 ≤ i)%Z → (i < length vs)%Z → h !! (l +ₗ i) = None) →
  (heap_array l vs) ##ₘ h.
Proof.
  intros Hdisj. apply map_disjoint_spec=> l' v1 v2.
  intros (j&w&?&->&?&Hj%lookup_lt_Some%inj_lt)%heap_array_lookup.
  move: Hj. rewrite Z2Nat.id // => ?. by rewrite Hdisj.
Qed.

(* [h] is added on the right here to make [state_init_heap_singleton] true. *)
Definition state_init_heap (l : loc) (n : Z) (v : val) (σ : state) : state :=
  state_upd_heap (λ h, heap_array l (replicate (Z.to_nat n) v) ∪ h) σ.

Lemma state_init_heap_singleton l v σ :
  state_init_heap l 1 v σ = state_upd_heap <[l:=Some v]> σ.
Proof.
  destruct σ as [h p]. rewrite /state_init_heap /=. f_equiv.
  rewrite right_id insert_union_singleton_l. done.
Qed.

Lemma state_upd_tapes_heap σ l1 l2 n xs m v :
  state_upd_tapes <[l2:=(n; xs)]> (state_init_heap l1 m v σ) =
  state_init_heap l1 m v (state_upd_tapes <[l2:=(n; xs)]> σ).
Proof.
  by rewrite /state_upd_tapes /state_init_heap /=.
Qed.


(* Heap-reduction relation. *)
Inductive base_step : expr → state → expr → state → Prop :=
(* Lambda. *)
| RecS f x e σ :
  base_step (Rec f x e) σ (Val $ RecV f x e) σ

(* Beta reduction. *)
| BetaS f x e1 v2 e' σ :
  e' = val_subst' x v2 (val_subst' f (RecV f x e1) e1) →
  base_step (App (Val $ RecV f x e1) (Val v2)) σ e' σ

(* Invoking a multi-shot continuation. *)
| KontS k w e' σ :
  e' = fill k (Val w) →
  base_step (App (Val (KontV k)) (Val w)) σ e' σ

(* Effect. *)
| EffectS s e e' σ σ' :
  σ' = state_upd_next_label label_succ σ →
  e' = lbl_subst s σ.(next_label) e →
  base_step (Effect s e) σ e' σ'

(* Capturing a multi-shot continuation. *)
| HandleEffS l v k e1 e2 e3 σ :
  let k' := (HandleCtx l e2 e3 :: k) in
  l ∉ ectx_labels k →
  to_eff e1 = Some (l, v, k) →
  base_step (Handle (EffLabel l) e1 e2 e3)    σ
    (App (App e2 (Val v)) (Val $ KontV k')) σ

(* Handle - Return branch. *)
| HandleRetS l v e2 e3 σ :
  base_step (Handle (EffLabel l) (Val v) e2 e3) σ (App e3 (Val v)) σ

(* Operations *)
| UnOpS op v v' σ :
  un_op_eval op v = Some v' →
  base_step (UnOp op (Val v)) σ (Val v') σ
| BinOpS op v1 v2 v' σ :
  bin_op_eval op v1 v2 = Some v' →
  base_step (BinOp op (Val v1) (Val v2)) σ (Val v') σ
| IfTrueS e1 e2 σ :
  base_step (If (Val $ LitV $ LitBool true) e1 e2) σ e1 σ
| IfFalseS e1 e2 σ :
  base_step (If (Val $ LitV $ LitBool false) e1 e2) σ e2 σ

(* Products*)
| PairS v1 v2 σ :
  base_step (Pair (Val v1) (Val v2)) σ (Val $ PairV v1 v2) σ
| FstS v1 v2 σ :
  base_step (Fst (Val $ PairV v1 v2)) σ (Val v1) σ
| SndS v1 v2 σ :
  base_step (Snd (Val $ PairV v1 v2)) σ (Val v2) σ

(* Sums *)
| InjLS v σ :
  base_step (InjL $ Val v) σ (Val $ InjLV v) σ
| InjRS v σ :
  base_step (InjR $ Val v) σ (Val $ InjRV v) σ
| CaseLS v e1 e2 σ :
  base_step (Case (Val $ InjLV v) e1 e2) σ (App e1 (Val v)) σ
| CaseRS v e1 e2 σ :
  base_step (Case (Val $ InjRV v) e1 e2) σ (App e2 (Val v)) σ

(* Heap *)
| AllocNS z N v σ l :
  l = fresh_loc σ.(heap) →
  N = Z.to_nat z →
  (0 < N)%nat →
  base_step (AllocN (Val $ LitV $ LitInt z) (Val v)) σ
    (Val $ LitV $ LitLoc l) (state_init_heap l N v σ)

| LoadS l v σ :
  σ.(heap) !! l = Some $ Some v →
  base_step (Load (Val $ LitV $ LitLoc l)) σ (of_val v) σ
| StoreS o l w σ :
  σ.(heap) !! l = Some $ o →
  base_step (Store (Val $ LitV $ LitLoc l) (Val w)) σ
    (Val $ LitV LitUnit) (state_upd_heap <[l:=Some w]> σ)
(* Probabilistic choice *)
| RandNoTapeS z N (n : fin (S N)) σ:
  N = Z.to_nat z →
  base_step (Rand (Val $ LitV $ LitInt z) (Val $ LitV LitUnit)) σ (Val $ LitV $ LitInt n) σ
| AllocTapeS z N σ l :
  l = fresh_loc σ.(tapes) →
  N = Z.to_nat z →
  base_step (AllocTape (Val (LitV (LitInt z)))) σ
    (Val $ LitV $ LitLbl l) (state_upd_tapes <[l := (N; []) : tape]> σ)
| RandTapeS l z N n ns σ :
  N = Z.to_nat z →
  σ.(tapes) !! l = Some ((N; n :: ns) : tape)  →
  base_step (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl l)))) σ
    (Val $ LitV $ LitInt $ n) (state_upd_tapes <[l := (N; ns) : tape]> σ)
| RandTapeEmptyS l z N (n : fin (S N)) σ :
  N = Z.to_nat z →
  σ.(tapes) !! l = Some ((N; []) : tape) →
  base_step (Rand (Val (LitV (LitInt z))) (Val $ LitV $ LitLbl l)) σ (Val $ LitV $ LitInt n) σ
| RandTapeOtherS l z M N ms (n : fin (S N)) σ :
  N = Z.to_nat z →
  σ.(tapes) !! l = Some ((M; ms) : tape) →
  N ≠ M →
  base_step (Rand (Val (LitV (LitInt z))) (Val $ LitV $ LitLbl l)) σ (Val $ LitV $ LitInt n) σ.


Global Instance eq_dec_state : EqDecision state.
Proof. solve_decision. Qed. 

Global Instance state_countable : Countable state.
Proof. Admitted.

(*   {| encode σ := encode (σ.(next_label), σ.(heap), σ.(tapes));
        decode p := '(l, h, t) ← decode p; mret {|next_label := l; heap:=h; tapes:=t|} |}.
   Next Obligation. intros [h t]. rewrite decode_encode //=. Qed. *)


Definition state_step (σ1 : state) (α : loc) : distr state :=
  if bool_decide (α ∈ dom σ1.(tapes)) then
    let: (N; ns) := (σ1.(tapes) !!! α) in
    dmap (λ n, state_upd_tapes (<[α := (N; ns ++ [n])]>) σ1) (dunifP N)
  else dzero.

Lemma state_step_unfold σ α N ns:
  tapes σ !! α = Some (N; ns) ->
  state_step σ α = dmap (λ n, state_upd_tapes (<[α := (N; ns ++ [n])]>) σ) (dunifP N).
Proof.
  intros H.
  rewrite /state_step.
  rewrite bool_decide_eq_true_2; last first.
  { by apply elem_of_dom. }
  by rewrite (lookup_total_correct (tapes σ) α (N; ns)); last done.
Qed.

#[local] Open Scope R.

Definition head_step (e1 : expr) (σ1 : state) : distr (expr * state) :=
  match e1 with
  | Rec f x e =>
      dret (Val $ RecV f x e, σ1)
  | Pair (Val v1) (Val v2) =>
      dret (Val $ PairV v1 v2, σ1)
  | InjL (Val v) =>
      dret (Val $ InjLV v, σ1)
  | InjR (Val v) =>
      dret (Val $ InjRV v, σ1)
  | App (Val (RecV f x e1)) (Val v2) =>
      dret (val_subst' x v2 (val_subst' f (RecV f x e1) e1) , σ1)
  | UnOp op (Val v) =>
      match un_op_eval op v with
        | Some w => dret (Val w, σ1)
        | _ => dzero
      end
  | BinOp op (Val v1) (Val v2) =>
      match bin_op_eval op v1 v2 with
        | Some w => dret (Val w, σ1)
        | _ => dzero
      end
  | If (Val (LitV (LitBool true))) e1 e2  =>
      dret (e1 , σ1)
  | If (Val (LitV (LitBool false))) e1 e2 =>
      dret (e2 , σ1)
  | Fst (Val (PairV v1 v2)) =>
      dret (Val v1, σ1)
  | Snd (Val (PairV v1 v2)) =>
      dret (Val v2, σ1)
  | Case (Val (InjLV v)) e1 e2 =>
      dret (App e1 (Val v), σ1)
  | Case (Val (InjRV v)) e1 e2 =>
      dret (App e2 (Val v), σ1)
  | AllocN (Val (LitV (LitInt N))) (Val v) =>
      let ℓ := fresh_loc σ1.(heap) in
      if bool_decide (0 < Z.to_nat N)%nat
        then dret (Val $ LitV $ LitLoc ℓ, state_init_heap ℓ (Z.to_nat N) v σ1)
        else dzero
  | Load (Val (LitV (LitLoc l))) =>
      match σ1.(heap) !! l with
      | Some (Some v) => dret (Val v, σ1)
      | _ => dzero
      end
  | Store (Val (LitV (LitLoc l))) (Val w) =>
      match σ1.(heap) !! l with
      | Some v => dret (Val $ LitV LitUnit, state_upd_heap <[l:= (Some w)]> σ1)
      | None => dzero
      end
  (* Since our language only has integers, we use Z.to_nat, which maps positive
     integers to the corresponding nat, and the rest to 0. We sample from
     [dunifP N = dunif (1 + N)] to avoid the case [dunif 0 = dzero]. *)
  (* Uniform sampling from [0, 1 , ..., N] *)
  | Rand (Val (LitV (LitInt N))) (Val (LitV LitUnit)) =>
      dmap (λ n : fin _, (Val $ LitV $ LitInt n, σ1)) (dunifP (Z.to_nat N))
  | AllocTape (Val (LitV (LitInt z))) =>
      let ι := fresh_loc σ1.(tapes) in
      dret (Val $ LitV $ LitLbl ι, state_upd_tapes <[ι := (Z.to_nat z; []) ]> σ1)
  (* Labelled sampling, conditional on tape contents *)
  | Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))) =>
      match σ1.(tapes) !! l with
      | Some (M; ns) =>
          if bool_decide (M = Z.to_nat N) then
            match ns  with
            | n :: ns =>
                (* the tape is non-empty so we consume the first number *)
                dret (Val $ LitV $ LitInt $ fin_to_nat n, state_upd_tapes <[l:=(M; ns)]> σ1)
            | [] =>
                (* the tape is allocated but empty, so we sample from [0, 1, ..., M] uniformly *)
                dmap (λ n : fin _, (Val $ LitV $ LitInt n, σ1)) (dunifP M)
            end
          else
            (* bound did not match the bound of the tape *)
            dmap (λ n : fin _, (Val $ LitV $ LitInt n, σ1)) (dunifP (Z.to_nat N))
      | None => dzero
      end
  | (App (Val (KontV k)) (Val w))  => dret (fill k (Val w), σ1)
  | Effect s e => dret (lbl_subst s σ1.(next_label) e, state_upd_next_label label_succ σ1)
  | Handle (EffLabel l) e1 e2 e3 =>
      match to_eff e1 with
      | None => match to_val e1 with
                | None => dzero
                | Some v => dret (App e3 (Val v), σ1)
                end
      | Some (l', v, k) => 
          let k' := (HandleCtx l e2 e3 :: k) in
          if decide (l' ∉ (ectx_labels k)) then
            if decide (l = l') then
            dret (App (App e2 (Val v)) (Val $ KontV k'), σ1)
            else dzero
          else dzero
           
      end
  | _ => dzero
end.

Create HintDb head_step.
Global Hint Constructors base_step : head_step.
(* 0%fin always has non-zero mass, so propose this choice if the reduct is
   unconstrained. *)
Global Hint Extern 1
  (base_step (Rand (Val (LitV _)) (Val (LitV LitUnit))) _ _ _) =>
         eapply (RandNoTapeS _ _ 0%fin) : head_step.
Global Hint Extern 1
  (base_step (Rand (Val (LitV _)) (Val (LitV (LitLbl _)))) _ _ _) =>
         eapply (RandTapeEmptyS _ _ _ 0%fin) : head_step.
Global Hint Extern 1
  (base_step (Rand (Val (LitV _)) (Val (LitV (LitLbl _)))) _ _ _) =>
         eapply (RandTapeOtherS _ _ _ _ _ 0%fin) : head_step.


Ltac inv_head_step :=
  repeat
    match goal with
    | H : context [@bool_decide ?P ?dec] |- _ =>
        try (rewrite bool_decide_eq_true_2 in H; [|done]);
        try (rewrite bool_decide_eq_false_2 in H; [|done]);
        destruct_decide (@bool_decide_reflect P dec); simplify_eq
    | _ => progress simplify_map_eq; simpl in *; inv_distr; repeat case_match; inv_distr
    | H : to_val _ = Some _ |- _ => apply of_to_val in H
    | H : is_Some (_ !! _) |- _ => destruct H
    end.

Lemma head_step_support_equiv_rel e1 e2 σ1 σ2 :
  head_step e1 σ1 (e2, σ2) > 0 ↔ base_step e1 σ1 e2 σ2.
Proof.
  split.
  - intros ?. destruct e1; inv_head_step; eauto with head_step.
  - inversion 1; simplify_map_eq/=; try case_bool_decide; simplify_eq; solve_distr; try real_solver.
Qed.
