(** We define the resources required to interpret the implementation and
    specification configuration.

    In particular, we build an instance of [weakestpre.irisGS] by defining a
    state- and spec-interpretation. *)

From iris.algebra Require Import auth excl frac agree gmap.
From iris.base_logic Require Import gen_heap invariants ghost_map.
From iris.prelude Require Import options.
From iris.program_logic Require Import ectx_lifting.
From iris.proofmode Require Import proofmode.

From self Require Import weakestpre lang.

Definition specN := nroot .@ "spec".

(** The CMRA for the state of the implementation. This is linked to the
    physical state. *)
Class stateIG Σ := StateIG {
  stateI_invG : invGS_gen HasNoLc Σ;
  stateI_gen_heapG :> gen_heapGS loc val Σ;
  stateI_gen_tapesG :> gen_heapGS loc tape Σ;
}.

(** The CMRA for the state of the specification. *)

(* NB: we use option here to make specUR unital. For instance, we want to be
   able to own a resource mentioning a spec-heap mapsto without also owning the
   spec program; we'd use None for the spec program in this case. *)
Definition specUR : cmra := option (exclR exprO).
Definition heapUR : ucmra :=
  gmapUR loc (prodR fracR (agreeR (leibnizO val))).
Definition tapeUR : ucmra :=
  gmapUR loc (prodR fracR (agreeR (leibnizO tape))).

Definition cfgUR : cmra := prodR specUR (prodUR heapUR tapeUR).

(** The CMRA for the spec [cfg]. *)
Class cfgSG Σ := CFGSG { cfg_inG :> inG Σ (authR cfgUR); cfg_name : gname }.

Definition spec_cfg_interp '(e, σ) : cfgUR :=
  (Some (Excl e), ( (λ v , (1%Qp, to_agree v)) <$> σ.(heap),
                    (λ bs , (1%Qp, to_agree bs)) <$> σ.(tapes)) ).

(* Construct an instance of [program_logic.weakestpre.irisGS] for the WP. *)
Global Instance stateIG_irisG `{!stateIG Σ} `{!cfgSG Σ} : irisGS prob_lang Σ := {
  iris_invGS := stateI_invG ;
  state_interp σ :=
      (gen_heap_interp σ.(heap) ∗ gen_heap_interp σ.(tapes))%I ;
  spec_interp ρ := own cfg_name (● (spec_cfg_interp ρ)) ;
}.

Notation "l ↦ᵢ{ dq } v" := (mapsto (L:=loc) (V:=val) l dq v)
  (at level 20, format "l  ↦ᵢ{ dq }  v") : bi_scope.
Notation "l ↦ᵢ□ v" := (mapsto (L:=loc) (V:=val) l DfracDiscarded v)
  (at level 20, format "l  ↦ᵢ□  v") : bi_scope.
Notation "l ↦ᵢ{# q } v" := (mapsto (L:=loc) (V:=val) l (DfracOwn q) v)
  (at level 20, format "l  ↦ᵢ{# q }  v") : bi_scope.
Notation "l ↦ᵢ v" := (mapsto (L:=loc) (V:=val) l (DfracOwn 1) v)
  (at level 20, format "l  ↦ᵢ  v") : bi_scope.

Notation "l ↦ᵢₜ{ dq } b" := (mapsto (L:=loc) (V:=tape) l dq b)
  (at level 20, format "l  ↦ᵢₜ{ dq }  b") : bi_scope.
Notation "l ↦ᵢₜ□ b" := (mapsto (L:=loc) (V:=tape) l DfracDiscarded b)
  (at level 20, format "l  ↦ᵢₜ□  b") : bi_scope.
Notation "l ↦ᵢₜ{# q } b" := (mapsto (L:=loc) (V:=tape) l (DfracOwn q) b)
  (at level 20, format "l  ↦ᵢₜ{# q }  b") : bi_scope.
Notation "l ↦ᵢₜ b" := (mapsto (L:=loc) (V:=tape) l (DfracOwn 1) b)
  (at level 20, format "l  ↦ᵢₜ  b") : bi_scope.

Section definitionsS.
  Context `{stateIG Σ, cfgSG Σ}.
  Definition heapS_mapsto (l : loc) (q : Qp) (v: val) : iProp Σ :=
    own cfg_name (◯ (ε, ({[ l := (q, to_agree v) ]}, ε))).

  Definition spec_mapsto (e: expr) : iProp Σ :=
    own cfg_name (◯ (Some (Excl e), (∅, ∅))).

  Definition to_spec (e : expr) : specUR := Some (Excl e).

  Definition to_heap : gmap loc val → heapUR :=
    fmap (λ v, (1%Qp, to_agree (v : leibnizO val))).

  Definition to_tape : gmap loc tape → tapeUR :=
    fmap (λ v, (1%Qp, to_agree (v : leibnizO tape))).

  Definition spec_inv (ρ : cfg prob_lang) : iProp Σ :=
    (let '(e, σ) := ρ in
     own cfg_name (● (to_spec e, (to_heap σ.(heap), to_tape σ.(tapes)))))%I.

  (* PGH: TODO: generalise so that we can pure-step ahead in the spec? *)
  (* Definition spec_inv (ρ : cfg prob_lang) : iProp Σ := *)
  (*   (∃ e σ, own cfg_name (● (to_spec e, to_heap σ)) *)
  (*                ∗ ⌜rtc prim_step ρ (e,σ)⌝)%I. *)
  Definition spec_ctx : iProp Σ :=
    (∃ ρ, inv specN (spec_inv ρ))%I.

  Global Instance heapS_mapsto_timeless l q v : Timeless (heapS_mapsto l q v).
  Proof. apply _. Qed.
  Global Instance spec_ctx_persistent : Persistent spec_ctx.
  Proof. apply _. Qed.
End definitionsS.
Global Typeclasses Opaque heapS_mapsto spec_mapsto.

Notation "l ↦ₛ{ q } v" := (heapS_mapsto l q v)
  (at level 20, q at level 50, format "l  ↦ₛ{ q }  v") : bi_scope.
Notation "l ↦ₛ v" := (heapS_mapsto l 1 v) (at level 20) : bi_scope.
Notation " ⤇ e" := (spec_mapsto e) (at level 20) : bi_scope.

(* PGH: originally used with autosubst; might be undeeded. *)
Ltac iAsimpl :=
  repeat match goal with
  | |- context [ (⤇ ?e)%I ] => progress (
    let e' := fresh in evar (e':expr);
    assert (e = e') as ->; [unfold e'; reflexivity|];
    unfold e'; clear e')
  | |- context [ WP ?e @ _ {{ _ }}%I ] => progress (
    let e' := fresh in evar (e':expr);
    assert (e = e') as ->; [unfold e'; reflexivity|];
    unfold e'; clear e')
  end.

Section to_heap.
  Implicit Types σ : gmap loc val.

  Lemma lookup_to_heap_None σ l : σ !! l = None → to_heap σ !! l = None.
  Proof. by rewrite /to_heap lookup_fmap=> ->. Qed.
  Lemma to_heap_insert l v σ :
    to_heap (<[l:=v]> σ) = <[l:=(1%Qp, to_agree (v:leibnizO val))]> (to_heap σ).
  Proof. by rewrite /to_heap fmap_insert. Qed.

  Lemma heap_singleton_included σ l q v :
    {[l := (q, to_agree v)]} ≼ to_heap σ → σ !! l = Some v.
  Proof.
    rewrite singleton_included_l=> -[[q' av] []].
    rewrite /to_heap lookup_fmap fmap_Some_equiv => -[v' [Hl [/= -> ->]]].
    move=> /Some_pair_included_total_2 [_] /to_agree_included /leibniz_equiv_iff -> //.
  Qed.

End to_heap.

(* Section cfg. *)
(*   Context `{heapIG Σ, cfgSG Σ}. *)
(*   Implicit Types P Q : iProp Σ. *)
(*   Implicit Types Φ : val → iProp Σ. *)
(*   Implicit Types σ : state. *)
(*   Implicit Types e : expr. *)
(*   Implicit Types v : val. *)

  (* Local Hint Resolve tpool_lookup : core. *)
  (* Local Hint Resolve tpool_lookup_Some : core. *)
  (* Local Hint Resolve to_tpool_insert : core. *)
  (* Local Hint Resolve to_tpool_insert' : core. *)
  (* Local Hint Resolve tpool_singleton_included : core. *)

  (* Lemma mapstoS_agree l q1 q2 v1 v2 : l ↦ₛ{q1} v1 -∗ l ↦ₛ{q2} v2 -∗ ⌜v1 = v2⌝. *)
  (* Proof. *)
  (*   apply bi.wand_intro_r. *)
  (*   rewrite /heapS_mapsto -own_op own_valid uPred.discrete_valid. f_equiv. *)
  (*   rewrite auth_frag_op_valid -pair_op. *)
  (*   rewrite singleton_op. *)
  (*   rewrite -pair_op. *)
  (*   rewrite pair_valid singleton_valid pair_valid to_agree_op_valid_L. *)
  (*   by intros [_ [_ [=]]]. *)
  (* Qed. *)
  (* Lemma mapstoS_combine l q1 q2 v1 v2 : *)
  (*   l ↦ₛ{q1} v1 -∗ l ↦ₛ{q2} v2 -∗ l ↦ₛ{q1 + q2} v1 ∗ ⌜v1 = v2⌝. *)
  (* Proof. *)
  (*   iIntros "Hl1 Hl2". iDestruct (mapstoS_agree with "Hl1 Hl2") as %->. *)
  (*   rewrite /heapS_mapsto. iCombine "Hl1 Hl2" as "Hl". eauto with iFrame. *)
  (* Qed. *)
  (* Lemma mapstoS_valid l q v : l ↦ₛ{q} v -∗ ✓ q. *)
  (* Proof. *)
  (*   rewrite /heapS_mapsto own_valid !discrete_valid auth_frag_valid. *)
  (*   by apply pure_mono=> -[_] /singleton_valid [??]. *)
  (* Qed. *)
  (* Lemma mapstoS_valid_2 l q1 q2 v1 v2 : *)
  (*   l ↦ₛ{q1} v1 -∗ l ↦ₛ{q2} v2 -∗ ✓ (q1 + q2)%Qp. *)
  (* Proof. *)
  (*   iIntros "H1 H2". iDestruct (mapstoS_combine with "H1 H2") as "[? ->]". *)
  (*   by iApply (mapstoS_valid l _ v2). *)
  (* Qed. *)
