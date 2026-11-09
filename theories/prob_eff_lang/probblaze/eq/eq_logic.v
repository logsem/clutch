(* A logic for equivalences: one proof for both refinements.

   Most of our relational results are equivalences, proved as two
   refinements whose scripts mirror each other.  Here propositions are
   predicates over a direction [d ∈ {Fwd, Bwd}] (Iris's [monPred] over a
   discrete index), and

     EQ el ≈ er @ E <|X|> {{ R }}

   is, at [Fwd], the refinement [BREL el ≤ er] and, at [Bwd], the refinement
   [BREL er ≤ el].  The two programs are called [l] and [r]: [l] runs on the
   left in direction [Fwd] and on the right in [Bwd].  State is described per
   program: [ℓ ↦ₗ v] is a physical points-to where [l] runs on the left and a
   specification points-to otherwise, [ℓ ↦ᵣ v] is the same for [r], and
   similarly for tapes ([α ↪ₗN (N; ns)], [α ↪ᵣN (N; ns)]).

   All connectives of [monPred] act pointwise, so a proof of [⊢ EQ el ≈ er]
   that uses only the rules below proves both refinements, and per-run
   choices (allocated locations, values supplied by the environment) are
   simply universally or existentially quantified variables.  Facts that do
   not depend on the direction are embedded with [⎡ ⎤].

   A semantic type [τ], which relates a left and a right value, is lifted to
   [⟪ τ ⟫ vl vr], relating a value of [l] and a value of [r]; the [eq_lift_*]
   lemmas take lifted types apart and put them together.  [EQ_sem_typed]
   turns an equivalence into the two typing judgements.

   [eq_rel] and [eq_lift] are sealed: a proof that has to look at one
   direction unfolds them with [eq_rel_at], [eq_rel_at_elim] and [eq_lift_at].

   What the rules cannot provide: the [▷] that a left step gives (it would
   be needed for Löb induction over steps, or for opening invariants with
   non-timeless contents).  There, a proof has to reason per index. *)

From iris.bi Require Import monpred.
From iris.proofmode Require Import base proofmode classes environments coq_tactics ltac_tactics reduction monpred.
From clutch.prelude Require Import fin.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode tactics.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances notation.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_judgement.

(* ------------------------------------------------------------------ *)
(* The index.                                                         *)
(* ------------------------------------------------------------------ *)

Inductive dir := Fwd | Bwd.

Global Instance dir_inhabited : Inhabited dir := populate Fwd.
Global Instance dir_sqsubseteq : SqSubsetEq dir := (=).
Global Instance dir_sqsubseteq_preorder : PreOrder (⊑@{dir}) := _.

Canonical Structure dirI : biIndex := BiIndex dir _ _ _.

Notation iPropD Σ := (monPred dirI (iPropI Σ)).

(* Every predicate over the (discrete) index is monotone. *)
Global Instance dir_mono {PROP : bi} (f : dir → PROP) : Proper ((⊑) ==> (⊢)) f.
Proof. by intros ?? ->. Qed.

(* The component that runs on the left in direction [d]. *)
Definition pick {A} (d : dir) (a b : A) : A := match d with Fwd => a | Bwd => b end.

Lemma pick_same {A} d (a : A) : pick d a a = a.
Proof. by destruct d. Qed.
Lemma pick_pick_l {A} d (a b : A) : pick d (pick d a b) (pick d b a) = a.
Proof. by destruct d. Qed.
Lemma pick_pick_r {A} d (a b : A) : pick d (pick d b a) (pick d a b) = b.
Proof. by destruct d. Qed.

Section eq_logic.
  Context `{!probblazeRGS Σ}.
  Implicit Types (el er : expr) (vl vr : val).

  (* ---------------------------------------------------------------- *)
  (* The relation, the resources, lifted types.                         *)
  (* ---------------------------------------------------------------- *)

  (* Label theories may depend on the direction: a theory created during a
     proof is written for [l] on the left and flipped at [Bwd].  An ordinary
     theory is coerced to a constant one. *)
  Record eqThy := EqThy { eq_thy_at : dir → iLblThy Σ }.
  Definition eq_thy_const (L : iLblThy Σ) : eqThy := EqThy (λ _, L).

  Local Definition eq_rel_def (E : coPset) el er (X : eqThy) (R : val → val → iPropD Σ) : iPropD Σ :=
    MonPred (λ d, brel E (pick d el er) (pick d er el) (eq_thy_at X d) (λ v1 v2, R (pick d v1 v2) (pick d v2 v1) d)) _.
  Local Definition eq_rel_aux : seal (@eq_rel_def). Proof. by eexists. Qed.
  Definition eq_rel := eq_rel_aux.(unseal).
  Local Definition eq_rel_unseal : @eq_rel = @eq_rel_def := eq_rel_aux.(seal_eq).

  Definition eq_pt_l (ℓ : loc) (dq : dfrac) (v : val) : iPropD Σ :=
    MonPred (λ d, match d with Fwd => ℓ ↦{dq} v | Bwd => ℓ ↦ₛ{dq} v end)%I _.
  Definition eq_pt_r (ℓ : loc) (dq : dfrac) (v : val) : iPropD Σ :=
    MonPred (λ d, match d with Fwd => ℓ ↦ₛ{dq} v | Bwd => ℓ ↦{dq} v end)%I _.

  Definition eq_tp_l (α : loc) (dq : dfrac) (N : nat) (ns : list nat) : iPropD Σ :=
    MonPred (λ d, match d with Fwd => α ↪{dq}N (N; ns) | Bwd => α ↪ₛ{dq}N (N; ns) end)%I _.
  Definition eq_tp_r (α : loc) (dq : dfrac) (N : nat) (ns : list nat) : iPropD Σ :=
    MonPred (λ d, match d with Fwd => α ↪ₛ{dq}N (N; ns) | Bwd => α ↪{dq}N (N; ns) end)%I _.

  (* A semantic type, relating a value of [l] and a value of [r]. *)
  Local Definition eq_lift_def (τ : sem_ty Σ) vl vr : iPropD Σ := MonPred (λ d, τ (pick d vl vr) (pick d vr vl)) _.
  Local Definition eq_lift_aux : seal (@eq_lift_def). Proof. by eexists. Qed.
  Definition eq_lift := eq_lift_aux.(unseal).
  Local Definition eq_lift_unseal : @eq_lift = @eq_lift_def := eq_lift_aux.(seal_eq).

  (* Non-atomic invariants with contents depending on the direction. *)
  Definition eq_na_inv (N : namespace) (P : iPropD Σ) : iPropD Σ := MonPred (λ d, na_invP N (P d)) _.
  Definition eq_na_close (P : iPropD Σ) (N : namespace) (E : coPset) : iPropD Σ :=
    MonPred (λ d, na_closeP (P d) N E) _.

End eq_logic.

Global Arguments eqThy : clear implicits.
Global Arguments EqThy {_} _.
Global Arguments eq_thy_at {_} _ _.
Global Arguments eq_thy_const {_} _.
Coercion eq_thy_const : iLblThy >-> eqThy.

Notation "'EQ' e1 ≈ e2 @ E <| X | > {{ R } }" := (eq_rel E e1%E e2%E X%I R%I)
  (at level 20, E, e1, e2, X, R at next level, only parsing) : bi_scope.
Notation "'EQ' e1 ≈ e2 <| X | > {{ R } }" := (eq_rel ⊤ e1%E e2%E X%I R%I)
  (at level 20, e1, e2, X, R at next level, only parsing) : bi_scope.

Notation "ℓ ↦ₗ{ dq } v" := (eq_pt_l ℓ dq v) (at level 20, format "ℓ  ↦ₗ{ dq }  v") : bi_scope.
Notation "ℓ ↦ᵣ{ dq } v" := (eq_pt_r ℓ dq v) (at level 20, format "ℓ  ↦ᵣ{ dq }  v") : bi_scope.
Notation "ℓ ↦ₗ v" := (eq_pt_l ℓ (DfracOwn 1) v) (at level 20, format "ℓ  ↦ₗ  v") : bi_scope.
Notation "ℓ ↦ᵣ v" := (eq_pt_r ℓ (DfracOwn 1) v) (at level 20, format "ℓ  ↦ᵣ  v") : bi_scope.
Notation "ℓ ↦ₗ□ v" := (eq_pt_l ℓ DfracDiscarded v) (at level 20, format "ℓ  ↦ₗ□  v") : bi_scope.
Notation "ℓ ↦ᵣ□ v" := (eq_pt_r ℓ DfracDiscarded v) (at level 20, format "ℓ  ↦ᵣ□  v") : bi_scope.
Notation "α ↪ₗ{ dq }N ( N ; ns )" := (eq_tp_l α dq N ns) (at level 20, format "α  ↪ₗ{ dq }N  ( N ;  ns )") : bi_scope.
Notation "α ↪ᵣ{ dq }N ( N ; ns )" := (eq_tp_r α dq N ns) (at level 20, format "α  ↪ᵣ{ dq }N  ( N ;  ns )") : bi_scope.
Notation "α ↪ₗN ( N ; ns )" := (eq_tp_l α (DfracOwn 1) N ns) (at level 20, format "α  ↪ₗN  ( N ;  ns )") : bi_scope.
Notation "α ↪ᵣN ( N ; ns )" := (eq_tp_r α (DfracOwn 1) N ns) (at level 20, format "α  ↪ᵣN  ( N ;  ns )") : bi_scope.
Notation "α ↪ₗ□N ( N ; ns )" := (eq_tp_l α DfracDiscarded N ns) (at level 20, format "α  ↪ₗ□N  ( N ;  ns )") : bi_scope.
Notation "α ↪ᵣ□N ( N ; ns )" := (eq_tp_r α DfracDiscarded N ns) (at level 20, format "α  ↪ᵣ□N  ( N ;  ns )") : bi_scope.
Notation "⟪ τ ⟫" := (eq_lift τ%T) (format "⟪ τ ⟫") : bi_scope.

Global Arguments pick : simpl never.
#[local] Open Scope bi_scope.

Section eq_rules.
  Context `{!probblazeRGS Σ}.
  Implicit Types (el er : expr) (vl vr : val).
  Implicit Types (τ κ : sem_ty Σ).

  Lemma eq_rel_at d E el er X R :
    (EQ el ≈ er @ E <|X|> {{ R }}) d = brel E (pick d el er) (pick d er el) (eq_thy_at X d) (λ v1 v2, R (pick d v1 v2) (pick d v2 v1) d).
  Proof. by rewrite eq_rel_unseal. Qed.

  Lemma eq_rel_at_elim d E el er X R :
    (EQ el ≈ er @ E <|X|> {{ R }}) d ⊢ brel E (pick d el er) (pick d er el) (eq_thy_at X d) (λ v1 v2, R (pick d v1 v2) (pick d v2 v1) d).
  Proof. by rewrite eq_rel_at. Qed.

  Lemma eq_rel_at_elim_const d E el er (L : iLblThy Σ) R :
    (EQ el ≈ er @ E <|L|> {{ R }}) d ⊢ brel E (pick d el er) (pick d er el) L (λ v1 v2, R (pick d v1 v2) (pick d v2 v1) d).
  Proof. apply eq_rel_at_elim. Qed.

  Lemma eq_lift_at d τ vl vr : ⟪ τ ⟫ vl vr d = τ (pick d vl vr) (pick d vr vl).
  Proof. by rewrite eq_lift_unseal. Qed.

  (* ---------------------------------------------------------------- *)
  (* Proof-mode instances.                                              *)
  (* ---------------------------------------------------------------- *)

  Global Instance eq_pt_l_timeless ℓ dq v : Timeless (ℓ ↦ₗ{dq} v).
  Proof. split=> d. rewrite monPred_at_later monPred_at_except_0. destruct d; apply timeless, _. Qed.
  Global Instance eq_pt_r_timeless ℓ dq v : Timeless (ℓ ↦ᵣ{dq} v).
  Proof. split=> d. rewrite monPred_at_later monPred_at_except_0. destruct d; apply timeless, _. Qed.
  Global Instance eq_tp_l_timeless α dq N ns : Timeless (α ↪ₗ{dq}N (N; ns)).
  Proof. split=> d. rewrite monPred_at_later monPred_at_except_0. destruct d; apply timeless, _. Qed.
  Global Instance eq_tp_r_timeless α dq N ns : Timeless (α ↪ᵣ{dq}N (N; ns)).
  Proof. split=> d. rewrite monPred_at_later monPred_at_except_0. destruct d; apply timeless, _. Qed.

  Global Instance eq_pt_l_persistent ℓ v : Persistent (ℓ ↦ₗ□ v).
  Proof. split=> d. rewrite monPred_at_persistently. destruct d; apply persistent, _. Qed.
  Global Instance eq_pt_r_persistent ℓ v : Persistent (ℓ ↦ᵣ□ v).
  Proof. split=> d. rewrite monPred_at_persistently. destruct d; apply persistent, _. Qed.

  Lemma eq_pt_l_persist ℓ dq v : ⊢ ℓ ↦ₗ{dq} v ==∗ ℓ ↦ₗ□ v.
  Proof. iStartProof (iProp _). iIntros (d) "H". destruct d; by iApply ghost_map_elem_persist. Qed.
  Lemma eq_pt_r_persist ℓ dq v : ⊢ ℓ ↦ᵣ{dq} v ==∗ ℓ ↦ᵣ□ v.
  Proof. iStartProof (iProp _). iIntros (d) "H". destruct d; by iApply ghost_map_elem_persist. Qed.

  Lemma eq_pt_l_agree ℓ dq1 dq2 v1 v2 : ⊢ ℓ ↦ₗ{dq1} v1 -∗ ℓ ↦ₗ{dq2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    split=> d. rewrite monPred_at_emp monPred_at_wand. iIntros "_" (d1 <-) "H1".
    rewrite monPred_at_wand. iIntros (d2 <-) "H2". rewrite monPred_at_pure.
    destruct d; rewrite /eq_pt_l /eq_pt_r /=; by iCombine "H1 H2" gives %[_ ->].
  Qed.
  Lemma eq_pt_r_agree ℓ dq1 dq2 v1 v2 : ⊢ ℓ ↦ᵣ{dq1} v1 -∗ ℓ ↦ᵣ{dq2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    split=> d. rewrite monPred_at_emp monPred_at_wand. iIntros "_" (d1 <-) "H1".
    rewrite monPred_at_wand. iIntros (d2 <-) "H2". rewrite monPred_at_pure.
    destruct d; rewrite /eq_pt_l /eq_pt_r /=; by iCombine "H1 H2" gives %[_ ->].
  Qed.

  Global Instance eq_tp_l_persistent α N ns : Persistent (α ↪ₗ□N (N; ns)).
  Proof. split=> d. rewrite monPred_at_persistently. destruct d; apply persistent, _. Qed.
  Global Instance eq_tp_r_persistent α N ns : Persistent (α ↪ᵣ□N (N; ns)).
  Proof. split=> d. rewrite monPred_at_persistently. destruct d; apply persistent, _. Qed.

  Lemma eq_tp_l_persist α dq N ns : ⊢ α ↪ₗ{dq}N (N; ns) ==∗ α ↪ₗ□N (N; ns).
  Proof.
    iStartProof (iProp _). iIntros (d) "H".
    destruct d; [by iApply tapeN_to_persistent|by iApply spec_tape_to_persistent].
  Qed.
  Lemma eq_tp_r_persist α dq N ns : ⊢ α ↪ᵣ{dq}N (N; ns) ==∗ α ↪ᵣ□N (N; ns).
  Proof.
    iStartProof (iProp _). iIntros (d) "H".
    destruct d; [by iApply spec_tape_to_persistent|by iApply tapeN_to_persistent].
  Qed.

  (* A full tape assertion is exclusive. *)
  Lemma eq_tp_l_excl α dq N ns ms : ⊢ α ↪ₗN (N; ns) -∗ α ↪ₗ{dq}N (N; ms) -∗ False.
  Proof.
    split=> d. rewrite monPred_at_emp monPred_at_wand. iIntros "_" (d1 <-) "H1".
    rewrite monPred_at_wand. iIntros (d2 <-) "H2". rewrite monPred_at_pure.
    destruct d; rewrite /eq_tp_l /=; iDestruct "H1" as (??) "H1"; iDestruct "H2" as (??) "H2";
      by iDestruct (ghost_map_elem_ne with "H1 H2") as %?.
  Qed.
  Lemma eq_tp_r_excl α dq N ns ms : ⊢ α ↪ᵣN (N; ns) -∗ α ↪ᵣ{dq}N (N; ms) -∗ False.
  Proof.
    split=> d. rewrite monPred_at_emp monPred_at_wand. iIntros "_" (d1 <-) "H1".
    rewrite monPred_at_wand. iIntros (d2 <-) "H2". rewrite monPred_at_pure.
    destruct d; rewrite /eq_tp_r /=; iDestruct "H1" as (??) "H1"; iDestruct "H2" as (??) "H2";
      by iDestruct (ghost_map_elem_ne with "H1 H2") as %?.
  Qed.

  (* Likewise, a full points-to excludes any other one for the location. *)
  Lemma eq_pt_l_excl ℓ dq v w : ⊢ ℓ ↦ₗ v -∗ ℓ ↦ₗ{dq} w -∗ False.
  Proof.
    split=> d. rewrite monPred_at_emp monPred_at_wand. iIntros "_" (d1 <-) "H1".
    rewrite monPred_at_wand. iIntros (d2 <-) "H2". rewrite monPred_at_pure.
    destruct d; rewrite /eq_pt_l /=; by iDestruct (ghost_map_elem_ne with "H1 H2") as %?.
  Qed.
  Lemma eq_pt_r_excl ℓ dq v w : ⊢ ℓ ↦ᵣ v -∗ ℓ ↦ᵣ{dq} w -∗ False.
  Proof.
    split=> d. rewrite monPred_at_emp monPred_at_wand. iIntros "_" (d1 <-) "H1".
    rewrite monPred_at_wand. iIntros (d2 <-) "H2". rewrite monPred_at_pure.
    destruct d; rewrite /eq_pt_r /=; by iDestruct (ghost_map_elem_ne with "H1 H2") as %?.
  Qed.

  Global Instance eq_na_inv_persistent N P : Persistent (eq_na_inv N P).
  Proof. split=> d. rewrite monPred_at_persistently. apply persistent, _. Qed.

  (* The index is discrete, so a wand at an index is a wand of the components;
     this lets lemmas proved per index introduce wands. *)
  Global Instance from_wand_at_dir (P Q : iPropD Σ) 𝓟 𝓠 d :
    MakeMonPredAt d P 𝓟 → MakeMonPredAt d Q 𝓠 → FromWand ((P -∗ Q) d) 𝓟 𝓠.
  Proof. rewrite /MakeMonPredAt /FromWand monPred_at_wand => <- <-. by iIntros "H" (j <-). Qed.
  Global Instance into_wand_at_dir p q (P Q : iPropD Σ) 𝓟 𝓠 d :
    MakeMonPredAt d P 𝓟 → MakeMonPredAt d Q 𝓠 → IntoWand p q ((P -∗ Q) d) 𝓟 𝓠 | 0.
  Proof.
    rewrite /MakeMonPredAt /IntoWand monPred_at_wand !bi.intuitionistically_if_elim => <- <-.
    iIntros "H HP". iApply ("H" $! d with "[] HP"). by iPureIntro.
  Qed.

  Lemma fupd_eq E el er X R :
    (|={E}=> EQ el ≈ er @ E <|X|> {{ R }}) ⊢ EQ el ≈ er @ E <|X|> {{ R }}.
  Proof. split=> d. rewrite monPred_at_fupd eq_rel_at. apply fupd_brel. Qed.

  Global Instance elim_fupd_eq p E el er P X R :
    ElimModal True%type p false (|={E}=> P) P (EQ el ≈ er @ E <|X|> {{ R }}) (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof.
    rewrite /ElimModal. intros _. iIntros "[HP HI]". iApply fupd_eq.
    destruct p; simpl; rewrite ?bi.intuitionistically_elim; iMod "HP"; iModIntro; by iApply "HI".
  Qed.

  Global Instance elim_bupd_eq p E el er P X R :
    ElimModal True%type p false (|==> P) P (EQ el ≈ er @ E <|X|> {{ R }}) (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof. rewrite /ElimModal (bupd_fupd E). apply: elim_fupd_eq. Qed.

  Global Instance is_except_0_eq E el er X R : IsExcept0 (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof. rewrite /IsExcept0. iIntros "H". iApply fupd_eq. by iMod "H". Qed.

  Global Instance elim_modal_timeless_eq p P P' E el er X R :
    IntoExcept0 P P' →
    ElimModal True%type p p P P' (EQ el ≈ er @ E <|X|> {{ R }}) (EQ el ≈ er @ E <|X|> {{ R }}) | 0.
  Proof. intros. apply class_instances_later.elim_modal_timeless; first done. apply is_except_0_eq. Qed.

  (* ---------------------------------------------------------------- *)
  (* Values and invariants.                                             *)
  (* ---------------------------------------------------------------- *)

  Lemma eq_value vl vr X R : (|={⊤}=> R vl vr) ⊢ EQ vl ≈ vr <|X|> {{ R }}.
  Proof.
    split=> d. rewrite monPred_at_fupd eq_rel_at. iIntros "H".
    destruct d; rewrite /pick /=; iApply brel_value; iIntros "$"; by iMod "H".
  Qed.

  Lemma eq_na_alloc P N el er X R :
    ▷ P ∗ (eq_na_inv N P -∗ EQ el ≈ er <|X|> {{ R }}) ⊢ EQ el ≈ er <|X|> {{ R }}.
  Proof.
    split=> d. rewrite monPred_at_sep monPred_at_later monPred_at_wand eq_rel_at. iIntros "[HP H]".
    iApply brel_na_alloc. iFrame "HP". iIntros "#Hinv".
    iDestruct ("H" $! d with "[//] Hinv") as "H". by rewrite eq_rel_at.
  Qed.

  Lemma eq_na_open P E N el er X R :
    ↑N ⊆ E →
    eq_na_inv N P ∗ (▷ P ∗ eq_na_close P N E -∗ EQ el ≈ er @ (E ∖ ↑N) <|X|> {{ R }})
    ⊢ EQ el ≈ er @ E <|X|> {{ R }}.
  Proof.
    intros HN. split=> d. rewrite monPred_at_sep monPred_at_wand eq_rel_at. iIntros "[#Hinv H]".
    iApply brel_na_inv; first done. iFrame "Hinv". iIntros "[HP Hclose]".
    iDestruct ("H" $! d with "[//] [HP Hclose]") as "H".
    { rewrite monPred_at_sep monPred_at_later. iFrame. }
    by rewrite eq_rel_at.
  Qed.

  Lemma eq_na_close_rule P E N el er X R :
    ▷ P ∗ eq_na_close P N E ∗ EQ el ≈ er @ E <|X|> {{ R }} ⊢ EQ el ≈ er @ (E ∖ ↑N) <|X|> {{ R }}.
  Proof.
    split=> d. rewrite !monPred_at_sep monPred_at_later !eq_rel_at. iIntros "(HP & Hclose & H)".
    iApply brel_na_close. iFrame.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Steps of [l] and of [r].                                           *)
  (* ---------------------------------------------------------------- *)

  Lemma eq_pure_l E el el' er X R φ n :
    PureExec φ n el el' → φ →
    EQ el' ≈ er @ E <|X|> {{ R }} ⊢ EQ el ≈ er @ E <|X|> {{ R }}.
  Proof.
    intros ??. split=> d. rewrite !eq_rel_at. destruct d; rewrite /pick /=.
    - rewrite -brel_pure_step_later //. iIntros "H". by iModIntro.
    - by apply: brel_pure_step_r.
  Qed.

  Lemma eq_pure_r E el er er' X R φ n :
    PureExec φ n er er' → φ →
    EQ el ≈ er' @ E <|X|> {{ R }} ⊢ EQ el ≈ er @ E <|X|> {{ R }}.
  Proof.
    intros ??. split=> d. rewrite !eq_rel_at. destruct d; rewrite /pick /=.
    - by apply: brel_pure_step_r.
    - rewrite -brel_pure_step_later //. iIntros "H". by iModIntro.
  Qed.

  Lemma eq_load_l E K ℓ dq v er X R :
    ℓ ↦ₗ{dq} v ∗ (ℓ ↦ₗ{dq} v -∗ EQ fill K (Val v) ≈ er @ E <|X|> {{ R }}) ⊢ EQ fill K (! #ℓ) ≈ er @ E <|X|> {{ R }}.
  Proof.
    split=> d. rewrite monPred_at_sep monPred_at_wand !eq_rel_at. iIntros "[Hl H]".
    destruct d; rewrite /pick /=.
    - iApply (brel_load_l with "Hl"). iIntros "!> Hl". iApply (eq_rel_at_elim Fwd); iApply ("H" $! Fwd with "[//] Hl").
    - iApply (brel_load_r with "Hl"). iIntros "Hl". iApply (eq_rel_at_elim Bwd); iApply ("H" $! Bwd with "[//] Hl").
  Qed.

  Lemma eq_load_r E K ℓ dq v el X R :
    ℓ ↦ᵣ{dq} v ∗ (ℓ ↦ᵣ{dq} v -∗ EQ el ≈ fill K (Val v) @ E <|X|> {{ R }}) ⊢ EQ el ≈ fill K (! #ℓ) @ E <|X|> {{ R }}.
  Proof.
    split=> d. rewrite monPred_at_sep monPred_at_wand !eq_rel_at. iIntros "[Hl H]".
    destruct d; rewrite /pick /=.
    - iApply (brel_load_r with "Hl"). iIntros "Hl". iApply (eq_rel_at_elim Fwd); iApply ("H" $! Fwd with "[//] Hl").
    - iApply (brel_load_l with "Hl"). iIntros "!> Hl". iApply (eq_rel_at_elim Bwd); iApply ("H" $! Bwd with "[//] Hl").
  Qed.

  Lemma eq_store_l E K ℓ v w er X R :
    ℓ ↦ₗ v ∗ (ℓ ↦ₗ w -∗ EQ fill K #()%V ≈ er @ E <|X|> {{ R }}) ⊢ EQ fill K (#ℓ <- w) ≈ er @ E <|X|> {{ R }}.
  Proof.
    split=> d. rewrite monPred_at_sep monPred_at_wand !eq_rel_at. iIntros "[Hl H]".
    destruct d; rewrite /pick /=.
    - iApply (brel_store_l with "Hl"). iIntros "!> Hl". iApply (eq_rel_at_elim Fwd); iApply ("H" $! Fwd with "[//] Hl").
    - iApply (brel_store_r with "Hl"). iIntros "Hl". iApply (eq_rel_at_elim Bwd); iApply ("H" $! Bwd with "[//] Hl").
  Qed.

  Lemma eq_store_r E K ℓ v w el X R :
    ℓ ↦ᵣ v ∗ (ℓ ↦ᵣ w -∗ EQ el ≈ fill K #()%V @ E <|X|> {{ R }}) ⊢ EQ el ≈ fill K (#ℓ <- w) @ E <|X|> {{ R }}.
  Proof.
    split=> d. rewrite monPred_at_sep monPred_at_wand !eq_rel_at. iIntros "[Hl H]".
    destruct d; rewrite /pick /=.
    - iApply (brel_store_r with "Hl"). iIntros "Hl". iApply (eq_rel_at_elim Fwd); iApply ("H" $! Fwd with "[//] Hl").
    - iApply (brel_store_l with "Hl"). iIntros "!> Hl". iApply (eq_rel_at_elim Bwd); iApply ("H" $! Bwd with "[//] Hl").
  Qed.

  Lemma eq_alloc_l E K v er X R :
    (∀ ℓ : loc, ℓ ↦ₗ v -∗ EQ fill K #ℓ ≈ er @ E <|X|> {{ R }}) ⊢ EQ fill K (ref v) ≈ er @ E <|X|> {{ R }}.
  Proof.
    split=> d. rewrite monPred_at_forall !eq_rel_at. iIntros "H". destruct d; rewrite /pick /=.
    - iApply brel_alloc_l. iIntros "!>" (ℓ) "Hl". iSpecialize ("H" $! ℓ). rewrite monPred_at_wand.
      iApply (eq_rel_at_elim Fwd); iApply ("H" $! Fwd with "[//] Hl").
    - iApply brel_alloc_r. iIntros (ℓ) "Hl". iSpecialize ("H" $! ℓ). rewrite monPred_at_wand.
      iApply (eq_rel_at_elim Bwd); iApply ("H" $! Bwd with "[//] Hl").
  Qed.

  Lemma eq_alloc_r E K v el X R :
    (∀ ℓ : loc, ℓ ↦ᵣ v -∗ EQ el ≈ fill K #ℓ @ E <|X|> {{ R }}) ⊢ EQ el ≈ fill K (ref v) @ E <|X|> {{ R }}.
  Proof.
    split=> d. rewrite monPred_at_forall !eq_rel_at. iIntros "H". destruct d; rewrite /pick /=.
    - iApply brel_alloc_r. iIntros (ℓ) "Hl". iSpecialize ("H" $! ℓ). rewrite monPred_at_wand.
      iApply (eq_rel_at_elim Fwd); iApply ("H" $! Fwd with "[//] Hl").
    - iApply brel_alloc_l. iIntros "!>" (ℓ) "Hl". iSpecialize ("H" $! ℓ). rewrite monPred_at_wand.
      iApply (eq_rel_at_elim Bwd); iApply ("H" $! Bwd with "[//] Hl").
  Qed.

  Lemma eq_alloctape_l E K N (z : Z) er X R :
    TCEq N (Z.to_nat z) →
    (∀ α : loc, α ↪ₗN (N; []) -∗ EQ fill K #lbl:α ≈ er @ E <|X|> {{ R }})
    ⊢ EQ fill K (alloc #z) ≈ er @ E <|X|> {{ R }}.
  Proof.
    intros HN. split=> d. rewrite monPred_at_forall !eq_rel_at. iIntros "H". destruct d; rewrite /pick /=.
    - iApply brel_alloctape_l. iIntros "!>" (α) "Hα". iSpecialize ("H" $! α). rewrite monPred_at_wand.
      iApply (eq_rel_at_elim Fwd); iApply ("H" $! Fwd with "[//] Hα").
    - iApply (brel_alloctape_r K N z). iIntros (α) "Hα". iSpecialize ("H" $! α). rewrite monPred_at_wand.
      iApply (eq_rel_at_elim Bwd); iApply ("H" $! Bwd with "[//] [Hα]"). iExists []. by iFrame.
  Qed.

  Lemma eq_alloctape_r E K N (z : Z) el X R :
    TCEq N (Z.to_nat z) →
    (∀ α : loc, α ↪ᵣN (N; []) -∗ EQ el ≈ fill K #lbl:α @ E <|X|> {{ R }})
    ⊢ EQ el ≈ fill K (alloc #z) @ E <|X|> {{ R }}.
  Proof.
    intros HN. split=> d. rewrite monPred_at_forall !eq_rel_at. iIntros "H". destruct d; rewrite /pick /=.
    - iApply (brel_alloctape_r K N z). iIntros (α) "Hα". iSpecialize ("H" $! α). rewrite monPred_at_wand.
      iApply (eq_rel_at_elim Fwd); iApply ("H" $! Fwd with "[//] [Hα]"). iExists []. by iFrame.
    - iApply brel_alloctape_l. iIntros "!>" (α) "Hα". iSpecialize ("H" $! α). rewrite monPred_at_wand.
      iApply (eq_rel_at_elim Bwd); iApply ("H" $! Bwd with "[//] Hα").
  Qed.

  Lemma eq_rand_l E K (α : loc) N (z : Z) n ns er X R :
    TCEq N (Z.to_nat z) →
    α ↪ₗN (N; n :: ns) ∗ (α ↪ₗN (N; ns) -∗ ⌜n ≤ N⌝ -∗ EQ fill K #n ≈ er @ E <|X|> {{ R }})
    ⊢ EQ fill K (rand(#lbl:α) #z) ≈ er @ E <|X|> {{ R }}.
  Proof.
    intros HN. split=> d. rewrite monPred_at_sep monPred_at_wand !eq_rel_at. iIntros "[Hα H]".
    destruct d; rewrite /pick /=.
    - iApply brel_randT_l. iFrame "Hα". iIntros "!> Hα %Hn".
      iSpecialize ("H" $! Fwd with "[//] Hα"). iEval (rewrite monPred_at_wand) in "H".
      iApply (eq_rel_at_elim Fwd); iApply ("H" $! Fwd with "[//] []"). by rewrite monPred_at_pure.
    - iApply (brel_randT_r with "Hα"). iIntros "Hα %Hn".
      iSpecialize ("H" $! Bwd with "[//] Hα"). iEval (rewrite monPred_at_wand) in "H".
      iApply (eq_rel_at_elim Bwd); iApply ("H" $! Bwd with "[//] []"). by rewrite monPred_at_pure.
  Qed.

  Lemma eq_rand_r E K (α : loc) N (z : Z) n ns el X R :
    TCEq N (Z.to_nat z) →
    α ↪ᵣN (N; n :: ns) ∗ (α ↪ᵣN (N; ns) -∗ ⌜n ≤ N⌝ -∗ EQ el ≈ fill K #n @ E <|X|> {{ R }})
    ⊢ EQ el ≈ fill K (rand(#lbl:α) #z) @ E <|X|> {{ R }}.
  Proof.
    intros HN. split=> d. rewrite monPred_at_sep monPred_at_wand !eq_rel_at. iIntros "[Hα H]".
    destruct d; rewrite /pick /=.
    - iApply (brel_randT_r with "Hα"). iIntros "Hα %Hn".
      iSpecialize ("H" $! Fwd with "[//] Hα"). iEval (rewrite monPred_at_wand) in "H".
      iApply (eq_rel_at_elim Fwd); iApply ("H" $! Fwd with "[//] []"). by rewrite monPred_at_pure.
    - iApply brel_randT_l. iFrame "Hα". iIntros "!> Hα %Hn".
      iSpecialize ("H" $! Bwd with "[//] Hα"). iEval (rewrite monPred_at_wand) in "H".
      iApply (eq_rel_at_elim Bwd); iApply ("H" $! Bwd with "[//] []"). by rewrite monPred_at_pure.
  Qed.

  (* Coupling the next values of a tape of [l] and a tape of [r] (equal). *)
  Lemma eq_couple_tapes E (N : nat) el er X R α β ns ms :
    α ↪ₗN (N; ns) ∗ β ↪ᵣN (N; ms) ∗
    (∀ n, α ↪ₗN (N; ns ++ [n]) ∗ β ↪ᵣN (N; ms ++ [n]) -∗ EQ el ≈ er @ E <|X|> {{ R }})
    ⊢ EQ el ≈ er @ E <|X|> {{ R }}.
  Proof.
    split=> d. rewrite !monPred_at_sep monPred_at_forall eq_rel_at. iIntros "(Hα & Hβ & H)".
    destruct d; simpl.
    - iApply (brel_couple_TT _ _ (λ x, x) _ _ _ _ α β ns ms); try done.
      iFrame "Hα Hβ". iIntros (n) "[Hα Hβ]". iSpecialize ("H" $! n). rewrite monPred_at_wand.
      iApply (eq_rel_at_elim Fwd); iApply ("H" $! Fwd with "[//]"). rewrite monPred_at_sep. iFrame.
    - iApply (brel_couple_TT _ _ (λ x, x) _ _ _ _ β α ms ns); try done.
      iFrame "Hα Hβ". iIntros (n) "[Hβ Hα]". iSpecialize ("H" $! n). rewrite monPred_at_wand.
      iApply (eq_rel_at_elim Bwd); iApply ("H" $! Bwd with "[//]"). rewrite monPred_at_sep. iFrame.
  Qed.


  (* Coupling a tape of [l] with a [rand] of [r] (equal values). *)
  Lemma eq_couple_tape_rand E N K α X R z ns el :
    TCEq N (Z.to_nat z) → to_val el = None →
    α ↪ₗN (N; ns) ∗ (∀ n, ⌜n ≤ N⌝ -∗ α ↪ₗN (N; ns ++ [n]) -∗ EQ el ≈ fill K #n @ E <|X|> {{ R }})
    ⊢ EQ el ≈ fill K (rand #z) @ E <|X|> {{ R }}.
  Proof.
    intros HN Hel. split=> d. rewrite monPred_at_sep monPred_at_forall eq_rel_at. iIntros "[Hα H]".
    destruct d; rewrite /pick /=.
    - iDestruct "Hα" as (fs) "[%Hfs Hα]".
      iApply (brel_couple_TU _ _ (λ x, x) with "[$Hα H]"); [done|].
      iIntros (n) "Hα". iSpecialize ("H" $! (fin_to_nat n)).
      iApply (eq_rel_at_elim Fwd). iApply ("H" with "[] [Hα]").
      + iPureIntro. pose proof (fin_to_nat_lt n). lia.
      + iExists (fs ++ [n]). rewrite fmap_app Hfs. by iFrame.
    - iApply (brel_couple_UT _ _ (λ x, x)); first by intros. iFrame "Hα". iIntros "!>" (n Hn) "Hα".
      iSpecialize ("H" $! n). iApply (eq_rel_at_elim Bwd). iApply ("H" with "[] Hα").
      by iPureIntro.
  Qed.

  (* Coupling a [rand] of [l] with a tape of [r] (equal values). *)
  Lemma eq_couple_rand_tape E N K α X R z ns er :
    TCEq N (Z.to_nat z) → to_val er = None →
    α ↪ᵣN (N; ns) ∗ (∀ n, ⌜n ≤ N⌝ -∗ α ↪ᵣN (N; ns ++ [n]) -∗ EQ fill K #n ≈ er @ E <|X|> {{ R }})
    ⊢ EQ fill K (rand #z) ≈ er @ E <|X|> {{ R }}.
  Proof.
    intros HN Her. split=> d. rewrite monPred_at_sep monPred_at_forall eq_rel_at. iIntros "[Hα H]".
    destruct d; rewrite /pick /=.
    - iApply (brel_couple_UT _ _ (λ x, x)); first by intros. iFrame "Hα". iIntros "!>" (n Hn) "Hα".
      iSpecialize ("H" $! n). iApply (eq_rel_at_elim Fwd). iApply ("H" with "[] Hα").
      by iPureIntro.
    - iDestruct "Hα" as (fs) "[%Hfs Hα]".
      iApply (brel_couple_TU _ _ (λ x, x) with "[$Hα H]"); [done|].
      iIntros (n) "Hα". iSpecialize ("H" $! (fin_to_nat n)).
      iApply (eq_rel_at_elim Bwd). iApply ("H" with "[] [Hα]").
      + iPureIntro. pose proof (fin_to_nat_lt n). lia.
      + iExists (fs ++ [n]). rewrite fmap_app Hfs. by iFrame.
  Qed.

  (* Coupling a [rand] of [l] with a [rand] of [r] (equal values). *)
  Lemma eq_couple_rand_rand E N Kl Kr X R z :
    TCEq N (Z.to_nat z) →
    (∀ n, ⌜n ≤ N⌝ -∗ EQ fill Kl #n ≈ fill Kr #n @ E <|X|> {{ R }})
    ⊢ EQ fill Kl (rand #z) ≈ fill Kr (rand #z) @ E <|X|> {{ R }}.
  Proof.
    intros HN. split=> d. rewrite monPred_at_forall eq_rel_at. iIntros "H".
    destruct d; rewrite /pick /=;
      (iApply (brel_couple_rand_rand _ _ (λ n, n)); first by intros);
      iIntros (n Hn); iSpecialize ("H" $! n); [iApply (eq_rel_at_elim Fwd)|iApply (eq_rel_at_elim Bwd)];
      by iApply "H".
  Qed.

  (* Coupling a [rand] of [l] with a [rand] of [r] along a bijection [f]. *)
  Lemma eq_couple_rand_rand_bij E N f `{!Bij f} Kl Kr X R z :
    TCEq N (Z.to_nat z) → (∀ n, n < S N → f n < S N)%nat%type →
    (∀ n, ⌜n ≤ N⌝ -∗ EQ fill Kl #n ≈ fill Kr #(f n) @ E <|X|> {{ R }})
    ⊢ EQ fill Kl (rand #z) ≈ fill Kr (rand #z) @ E <|X|> {{ R }}.
  Proof.
    intros HN Hdom. split=> d. rewrite monPred_at_forall eq_rel_at. iIntros "H".
    destruct d; rewrite /pick /=.
    - iApply (brel_couple_rand_rand _ _ f); first done.
      iIntros (n Hn). iSpecialize ("H" $! n). iApply (eq_rel_at_elim Fwd). iApply "H". by iPureIntro.
    - pose proof (f_inv_bij f).
      iApply (brel_couple_rand_rand _ _ (f_inv f)).
      { intros n Hn. apply (f_inv_restr (S N) f Hdom n Hn). }
      iIntros (m Hm). iSpecialize ("H" $! (f_inv f m)). rewrite f_inv_cancel_r.
      iApply (eq_rel_at_elim Bwd). iApply "H". iPureIntro.
      pose proof (f_inv_restr (S N) f Hdom m ltac:(lia)). lia.
  Qed.

  (* Coupling a tape of [l] with a [rand] of [r] along a bijection [f]: the
     tape gets [f n] where the [rand] returns [n]. *)
  Lemma eq_couple_tape_rand_bij E N f `{!Bij f} K α X R z ns el :
    TCEq N (Z.to_nat z) → (∀ n, n < S N → f n < S N)%nat%type → to_val el = None →
    α ↪ₗN (N; ns) ∗ (∀ n, ⌜n ≤ N⌝ -∗ α ↪ₗN (N; ns ++ [f n]) -∗ EQ el ≈ fill K #n @ E <|X|> {{ R }})
    ⊢ EQ el ≈ fill K (rand #z) @ E <|X|> {{ R }}.
  Proof.
    intros HN Hdom Hel. split=> d. rewrite monPred_at_sep monPred_at_forall eq_rel_at. iIntros "[Hα H]".
    destruct d; rewrite /pick /=.
    - pose proof (f_inv_bij f).
      destruct (restr_bij_fin (S N) (f_inv f) (f_inv_restr (S N) f Hdom)) as (h & Hh & Hhf).
      iDestruct "Hα" as (fs) "[%Hfs Hα]".
      iApply (brel_couple_TU _ _ h with "[$Hα H]"); [done|].
      iIntros (x) "Hα". iSpecialize ("H" $! (fin_to_nat (h x))).
      iApply (eq_rel_at_elim Fwd). iApply ("H" with "[] [Hα]").
      + iPureIntro. pose proof (fin_to_nat_lt (h x)). lia.
      + iExists (fs ++ [x]). rewrite fmap_app Hfs Hhf f_inv_cancel_r. by iFrame.
    - iApply (brel_couple_UT _ _ f); first done. iFrame "Hα". iIntros "!>" (n Hn) "Hα".
      iSpecialize ("H" $! n). iApply (eq_rel_at_elim Bwd). iApply ("H" with "[] Hα"). by iPureIntro.
  Qed.

  Lemma tapeN_last_bound α dq N ns n :
    α ↪{dq}N (N; ns ++ [n]) ⊢ ⌜n ≤ N⌝ ∗ α ↪{dq}N (N; ns ++ [n]).
  Proof.
    iIntros "(%fs & %Hfs & Hα)". iSplit; last (iExists fs; by iFrame).
    iPureIntro. assert (n ∈ fin_to_nat <$> fs) as Hin by (rewrite Hfs; set_solver).
    apply list_elem_of_fmap in Hin as (x & -> & _). pose proof (fin_to_nat_lt x). lia.
  Qed.
  Lemma spec_tapeN_last_bound α dq N ns n :
    α ↪ₛ{dq}N (N; ns ++ [n]) ⊢ ⌜n ≤ N⌝ ∗ α ↪ₛ{dq}N (N; ns ++ [n]).
  Proof.
    iIntros "(%fs & %Hfs & Hα)". iSplit; last (iExists fs; by iFrame).
    iPureIntro. assert (n ∈ fin_to_nat <$> fs) as Hin by (rewrite Hfs; set_solver).
    apply list_elem_of_fmap in Hin as (x & -> & _). pose proof (fin_to_nat_lt x). lia.
  Qed.

  (* Coupling a tape of [l] with a tape of [r] along a bijection [f]. *)
  Lemma eq_couple_tapes_bij E (N : nat) f `{!Bij f} el er X R α β ns ms :
    (∀ n, n < S N → f n < S N)%nat%type →
    α ↪ₗN (N; ns) ∗ β ↪ᵣN (N; ms) ∗
    (∀ n, ⌜n ≤ N⌝ -∗ α ↪ₗN (N; ns ++ [n]) ∗ β ↪ᵣN (N; ms ++ [f n]) -∗ EQ el ≈ er @ E <|X|> {{ R }})
    ⊢ EQ el ≈ er @ E <|X|> {{ R }}.
  Proof.
    intros Hdom. split=> d. rewrite !monPred_at_sep monPred_at_forall eq_rel_at. iIntros "(Hα & Hβ & H)".
    destruct d; rewrite /pick /=.
    - iApply (brel_couple_TT _ N f _ _ _ _ α β ns ms); first done.
      iFrame "Hα Hβ". iIntros (n) "[Hα Hβ]".
      iDestruct (tapeN_last_bound with "Hα") as "[%Hn Hα]".
      iSpecialize ("H" $! n). iApply (eq_rel_at_elim Fwd). iApply ("H" with "[] [Hα Hβ]").
      + by iPureIntro.
      + iFrame.
    - pose proof (f_inv_bij f).
      iApply (brel_couple_TT _ N (f_inv f) _ _ _ _ β α ms ns); first (intros; by apply f_inv_restr).
      iFrame "Hα Hβ". iIntros (m) "[Hβ Hα]".
      iDestruct (spec_tapeN_last_bound with "Hα") as "[%Hn Hα]".
      iSpecialize ("H" $! (f_inv f m)). iApply (eq_rel_at_elim Bwd). iApply ("H" with "[] [Hα Hβ]").
      + by iPureIntro.
      + rewrite f_inv_cancel_r. iFrame.
  Qed.

  (* [rand] on an empty tape of [r] (or [l]), e.g. a persistent one: any value. *)
  Lemma eq_rand_empty_r E K (α : loc) dq N (z : Z) el X R :
    TCEq N (Z.to_nat z) →
    α ↪ᵣ{dq}N (N; []) ∗ (∀ n, α ↪ᵣ{dq}N (N; []) -∗ ⌜n ≤ N⌝ -∗ EQ el ≈ fill K #n @ E <|X|> {{ R }})
    ⊢ EQ el ≈ fill K (rand(#lbl:α) #z) @ E <|X|> {{ R }}.
  Proof.
    intros HN. split=> d. rewrite monPred_at_sep monPred_at_forall eq_rel_at. iIntros "[Hα H]".
    destruct d; rewrite /pick /=.
    - iApply brel_randT_empty_r. iFrame "Hα". iIntros (n) "Hα %Hn".
      iSpecialize ("H" $! n). iApply (eq_rel_at_elim Fwd). iApply ("H" with "Hα []"). by iPureIntro.
    - iApply brel_randT_empty_l. iFrame "Hα". iIntros "!>" (n) "Hα %Hn".
      iSpecialize ("H" $! n). iApply (eq_rel_at_elim Bwd). iApply ("H" with "Hα []"). by iPureIntro.
  Qed.
  Lemma eq_rand_empty_l E K (α : loc) dq N (z : Z) er X R :
    TCEq N (Z.to_nat z) →
    α ↪ₗ{dq}N (N; []) ∗ (∀ n, α ↪ₗ{dq}N (N; []) -∗ ⌜n ≤ N⌝ -∗ EQ fill K #n ≈ er @ E <|X|> {{ R }})
    ⊢ EQ fill K (rand(#lbl:α) #z) ≈ er @ E <|X|> {{ R }}.
  Proof.
    intros HN. split=> d. rewrite monPred_at_sep monPred_at_forall eq_rel_at. iIntros "[Hα H]".
    destruct d; rewrite /pick /=.
    - iApply brel_randT_empty_l. iFrame "Hα". iIntros "!>" (n) "Hα %Hn".
      iSpecialize ("H" $! n). iApply (eq_rel_at_elim Fwd). iApply ("H" with "Hα []"). by iPureIntro.
    - iApply brel_randT_empty_r. iFrame "Hα". iIntros (n) "Hα %Hn".
      iSpecialize ("H" $! n). iApply (eq_rel_at_elim Bwd). iApply ("H" with "Hα []"). by iPureIntro.
  Qed.

  (* Coupling a [rand] of [l] with a tape of [r] along a bijection [f]. *)
  Lemma eq_couple_rand_tape_bij E N f `{!Bij f} K α X R z ns er :
    TCEq N (Z.to_nat z) → (∀ n, n < S N → f n < S N)%nat%type → to_val er = None →
    α ↪ᵣN (N; ns) ∗ (∀ n, ⌜n ≤ N⌝ -∗ α ↪ᵣN (N; ns ++ [f n]) -∗ EQ fill K #n ≈ er @ E <|X|> {{ R }})
    ⊢ EQ fill K (rand #z) ≈ er @ E <|X|> {{ R }}.
  Proof.
    intros HN Hdom Her. split=> d. rewrite monPred_at_sep monPred_at_forall eq_rel_at. iIntros "[Hα H]".
    destruct d; rewrite /pick /=.
    - iApply (brel_couple_UT _ _ f); [done|]. iFrame "Hα". iIntros "!>" (n Hn) "Hα".
      iSpecialize ("H" $! n). iApply (eq_rel_at_elim Fwd). iApply ("H" with "[] Hα"). by iPureIntro.
    - destruct (restr_bij_fin (S N) f Hdom) as (g & Hg & Hgf).
      pose proof (f_inv_bij g) as Hginv.
      iDestruct "Hα" as (fs) "[%Hfs Hα]".
      iApply (brel_couple_TU _ _ (f_inv g) with "[$Hα H]"); [done|].
      iIntros (m) "Hα". iSpecialize ("H" $! (fin_to_nat (f_inv g m))).
      iApply (eq_rel_at_elim Bwd). iApply ("H" with "[] [Hα]").
      + iPureIntro. pose proof (fin_to_nat_lt (f_inv g m)). lia.
      + iExists (fs ++ [m]). rewrite fmap_app Hfs -Hgf f_inv_cancel_r. by iFrame.
  Qed.

  (* Coupling two tapes of [l] with one [rand] of [r], along an injection
     [f] of the pairs onto the range of the [rand]. *)
  Lemma eq_couple_tapes_rand (M N1 N2 : nat) (f : nat → nat → nat)
      (Hdom : (∀ n1 n2 : nat, n1 < S N1 → n2 < S N2 → f n1 n2 < S M)%nat%type)
      (Hinj : (∀ n1 n2 n1' n2' : nat, n1 < S N1 → n2 < S N2 → n1' < S N1 → n2' < S N2 →
                f n1 n2 = f n1' n2' → n1 = n1' ∧ n2 = n2')%nat%type)
      z K E el X R α1 α2 ns1 ns2 :
    TCEq M (Z.to_nat z) → (S M = S N1 * S N2)%nat →
    α1 ↪ₗN (N1; ns1) ∗ α2 ↪ₗN (N2; ns2) ∗
    (∀ n1 n2 : nat, ⌜n1 < S N1⌝%nat -∗ ⌜n2 < S N2⌝%nat -∗
       α1 ↪ₗN (N1; ns1 ++ [n1]) -∗ α2 ↪ₗN (N2; ns2 ++ [n2]) -∗ EQ el ≈ fill K #(f n1 n2) @ E <|X|> {{ R }})
    ⊢ EQ el ≈ fill K (rand #z) @ E <|X|> {{ R }}.
  Proof.
    intros HM HMN. split=> d. rewrite !monPred_at_sep monPred_at_forall eq_rel_at. iIntros "(H1 & H2 & H)".
    destruct d; rewrite /pick /=.
    - iApply (brel_couple_TT_U M N1 N2 f Hdom Hinj); first done. iFrame "H1 H2".
      iIntros (n1 n2 Hn1 Hn2) "H1 H2". iSpecialize ("H" $! n1). rewrite monPred_at_forall. iSpecialize ("H" $! n2).
      iApply (eq_rel_at_elim Fwd). iApply ("H" with "[] [] H1 H2"); by iPureIntro.
    - iApply (brel_couple_U_TT M N1 N2 f Hdom Hinj); first done. iFrame "H1 H2".
      iIntros "!>" (n1 n2 Hn1 Hn2) "H1 H2". iSpecialize ("H" $! n1). rewrite monPred_at_forall. iSpecialize ("H" $! n2).
      iApply (eq_rel_at_elim Bwd). iApply ("H" with "[] [] H1 H2"); by iPureIntro.
  Qed.

  (* The mirror image: one [rand] of [l] with two tapes of [r]. *)
  Lemma eq_couple_rand_tapes (M N1 N2 : nat) (f : nat → nat → nat)
      (Hdom : (∀ n1 n2 : nat, n1 < S N1 → n2 < S N2 → f n1 n2 < S M)%nat%type)
      (Hinj : (∀ n1 n2 n1' n2' : nat, n1 < S N1 → n2 < S N2 → n1' < S N1 → n2' < S N2 →
                f n1 n2 = f n1' n2' → n1 = n1' ∧ n2 = n2')%nat%type)
      z K E er X R α1 α2 ns1 ns2 :
    TCEq M (Z.to_nat z) → (S M = S N1 * S N2)%nat →
    α1 ↪ᵣN (N1; ns1) ∗ α2 ↪ᵣN (N2; ns2) ∗
    (∀ n1 n2 : nat, ⌜n1 < S N1⌝%nat -∗ ⌜n2 < S N2⌝%nat -∗
       α1 ↪ᵣN (N1; ns1 ++ [n1]) -∗ α2 ↪ᵣN (N2; ns2 ++ [n2]) -∗ EQ fill K #(f n1 n2) ≈ er @ E <|X|> {{ R }})
    ⊢ EQ fill K (rand #z) ≈ er @ E <|X|> {{ R }}.
  Proof.
    intros HM HMN. split=> d. rewrite !monPred_at_sep monPred_at_forall eq_rel_at. iIntros "(H1 & H2 & H)".
    destruct d; rewrite /pick /=.
    - iApply (brel_couple_U_TT M N1 N2 f Hdom Hinj); first done. iFrame "H1 H2".
      iIntros "!>" (n1 n2 Hn1 Hn2) "H1 H2". iSpecialize ("H" $! n1). rewrite monPred_at_forall. iSpecialize ("H" $! n2).
      iApply (eq_rel_at_elim Fwd). iApply ("H" with "[] [] H1 H2"); by iPureIntro.
    - iApply (brel_couple_TT_U M N1 N2 f Hdom Hinj); first done. iFrame "H1 H2".
      iIntros (n1 n2 Hn1 Hn2) "H1 H2". iSpecialize ("H" $! n1). rewrite monPred_at_forall. iSpecialize ("H" $! n2).
      iApply (eq_rel_at_elim Bwd). iApply ("H" with "[] [] H1 H2"); by iPureIntro.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Lifting refinement rules.                                          *)
  (* ---------------------------------------------------------------- *)

  (* A step of one program that the refinement logic provides on both
     sides is a step of [l] (and of [r]). *)
  Lemma eq_step_l E X R el el' er :
    (∀ e (S : val → val → iProp Σ), brel E el' e (eq_thy_at X Fwd) S ⊢ brel E el e (eq_thy_at X Fwd) S) →
    (∀ e (S : val → val → iProp Σ), brel E e el' (eq_thy_at X Bwd) S ⊢ brel E e el (eq_thy_at X Bwd) S) →
    EQ el' ≈ er @ E <|X|> {{ R }} ⊢ EQ el ≈ er @ E <|X|> {{ R }}.
  Proof. intros Hl Hr. split=> d. rewrite !eq_rel_at. destruct d; rewrite /pick /=; [apply Hl|apply Hr]. Qed.

  Lemma eq_step_r E X R el er er' :
    (∀ e (S : val → val → iProp Σ), brel E er' e (eq_thy_at X Bwd) S ⊢ brel E er e (eq_thy_at X Bwd) S) →
    (∀ e (S : val → val → iProp Σ), brel E e er' (eq_thy_at X Fwd) S ⊢ brel E e er (eq_thy_at X Fwd) S) →
    EQ el ≈ er' @ E <|X|> {{ R }} ⊢ EQ el ≈ er @ E <|X|> {{ R }}.
  Proof. intros Hl Hr. split=> d. rewrite !eq_rel_at. destruct d; rewrite /pick /=; [apply Hr|apply Hl]. Qed.

  (* The same as [eq_step_l]/[eq_step_r], for rules that need a resource [P]
     that does not depend on the direction. *)
  Lemma eq_step_l_with (P : iProp Σ) E X R el el' er :
    (∀ e (S : val → val → iProp Σ), P ∗ brel E el' e (eq_thy_at X Fwd) S ⊢ brel E el e (eq_thy_at X Fwd) S) →
    (∀ e (S : val → val → iProp Σ), P ∗ brel E e el' (eq_thy_at X Bwd) S ⊢ brel E e el (eq_thy_at X Bwd) S) →
    ⎡P⎤ ∗ EQ el' ≈ er @ E <|X|> {{ R }} ⊢ EQ el ≈ er @ E <|X|> {{ R }}.
  Proof.
    intros Hl Hr. split=> d. rewrite monPred_at_sep monPred_at_embed !eq_rel_at.
    destruct d; rewrite /pick /=; [apply Hl|apply Hr].
  Qed.

  Lemma eq_step_r_with (P : iProp Σ) E X R el er er' :
    (∀ e (S : val → val → iProp Σ), P ∗ brel E er' e (eq_thy_at X Bwd) S ⊢ brel E er e (eq_thy_at X Bwd) S) →
    (∀ e (S : val → val → iProp Σ), P ∗ brel E e er' (eq_thy_at X Fwd) S ⊢ brel E e er (eq_thy_at X Fwd) S) →
    ⎡P⎤ ∗ EQ el ≈ er' @ E <|X|> {{ R }} ⊢ EQ el ≈ er @ E <|X|> {{ R }}.
  Proof.
    intros Hl Hr. split=> d. rewrite monPred_at_sep monPred_at_embed !eq_rel_at.
    destruct d; rewrite /pick /=; [apply Hr|apply Hl].
  Qed.

  (* Binding a computation without effects (theory [⊥]) in evaluation
     contexts [Kl] and [Kr]. *)
  Lemma eq_bind_nil Kl Kr el er X R :
    EQ el ≈ er <|(⊥ : iLblThy Σ)|> {{ λ vl vr, EQ fill Kl vl ≈ fill Kr vr <|X|> {{ R }} }}
    ⊢ EQ fill Kl el ≈ fill Kr er <|X|> {{ R }}.
  Proof.
    split=> d. rewrite !eq_rel_at. iIntros "H".
    destruct d; rewrite /pick /=;
      (iApply brel_bind; [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|]);
      iApply (brel_wand with "H"); iIntros "!>" (v1 v2) "H"; by rewrite eq_rel_at /pick /=.
  Qed.

  (* Pure steps of [l] (resp. [r]) given as a reduction sequence. *)
  Lemma eq_rtc_pure_l E K e e' er X R :
    rtc pure_step e e' →
    EQ fill K e' ≈ er @ E <|X|> {{ R }} ⊢ EQ fill K e ≈ er @ E <|X|> {{ R }}.
  Proof.
    intros Hrtc. split=> d. rewrite !eq_rel_at. destruct d; rewrite /pick /=;
      induction Hrtc as [|x y z Hxy _ IH]; try done; iIntros "H".
    - iApply (brel_pure_step_later _ _ _ _ True 1); [intros _; apply nsteps_once; by apply logic.pure_step_ctx|done|].
      iNext. by iApply IH.
    - iApply (brel_pure_step_r _ _ _ _ True 1); [intros _; apply nsteps_once; by apply logic.pure_step_ctx|done|].
      by iApply IH.
  Qed.

  Lemma eq_rtc_pure_r E K e e' el X R :
    rtc pure_step e e' →
    EQ el ≈ fill K e' @ E <|X|> {{ R }} ⊢ EQ el ≈ fill K e @ E <|X|> {{ R }}.
  Proof.
    intros Hrtc. split=> d. rewrite !eq_rel_at. destruct d; rewrite /pick /=;
      induction Hrtc as [|x y z Hxy _ IH]; try done; iIntros "H".
    - iApply (brel_pure_step_r _ _ _ _ True 1); [intros _; apply nsteps_once; by apply logic.pure_step_ctx|done|].
      by iApply IH.
    - iApply (brel_pure_step_later _ _ _ _ True 1); [intros _; apply nsteps_once; by apply logic.pure_step_ctx|done|].
      iNext. by iApply IH.
  Qed.


  (* A refinement of a program with itself, with a symmetric
     postcondition, is an equivalence. *)
  Lemma eq_brel_self E e (S : val → val → iProp Σ) R :
    (⊢ brel E e e ⊥ S) → (∀ v1 v2, S v1 v2 ⊢ S v2 v1) →
    (∀ vl vr, ⎡S vl vr⎤ -∗ R vl vr) ⊢ EQ e ≈ e @ E <|(⊥ : iLblThy Σ)|> {{ R }}.
  Proof.
    intros He HS. split=> d. rewrite monPred_at_forall eq_rel_at. iIntros "HR".
    destruct d; rewrite /pick /=;
      (iApply (brel_mono OS _ _ [] [] with "[] [] [HR]"); [iApply to_iThy_le_refl|iApply He|]);
      simpl; iIntros (v1 v2) "H".
    - iSpecialize ("HR" $! v1). rewrite monPred_at_forall. iSpecialize ("HR" $! v2).
      rewrite monPred_at_wand. iApply ("HR" $! Fwd with "[//]"). by rewrite monPred_at_embed.
    - iSpecialize ("HR" $! v2). rewrite monPred_at_forall. iSpecialize ("HR" $! v1).
      rewrite monPred_at_wand. iApply ("HR" $! Bwd with "[//]"). rewrite monPred_at_embed. by iApply HS.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Lifted types.                                                      *)
  (* ---------------------------------------------------------------- *)

  (* A type relating a value to itself, independently of the direction. *)
  Lemma eq_lift_same τ v : ⎡τ v v⎤ ⊢ ⟪ τ ⟫ v v.
  Proof. split=> d. by rewrite monPred_at_embed eq_lift_at pick_same. Qed.

  Lemma eq_lift_unit vl vr : eq_lift (Σ := Σ) sem_ty_unit vl vr ⊣⊢ ⌜vl = #()%V ∧ vr = #()%V⌝.
  Proof.
    split=> d. rewrite monPred_at_pure eq_lift_at. destruct d; rewrite /pick /sem_ty_unit /=; iSplit; iPureIntro; naive_solver.
  Qed.

  Lemma eq_lift_prod τ κ vl vr :
    ⟪ τ × κ ⟫ vl vr ⊣⊢ ∃ al ar bl br, ⌜vl = (al, bl)%V⌝ ∗ ⌜vr = (ar, br)%V⌝ ∗ ⟪ τ ⟫ al ar ∗ ⟪ κ ⟫ bl br.
  Proof.
    split=> d. rewrite eq_lift_unseal !monPred_at_exist /eq_lift_def /=.
        destruct d; rewrite /pick /sem_ty_prod /=; iSplit.
    - iIntros "(%w1 & %w1' & %w2 & %w2' & -> & -> & H1 & H2)". iExists w1, w1', w2, w2'. by iFrame.
    - iIntros "(%al & %ar & %bl & %br & H)".
      iDestruct "H" as "(-> & -> & H1 & H2)". iExists _, _, _, _. by iFrame.
    - iIntros "(%w1 & %w1' & %w2 & %w2' & -> & -> & H1 & H2)". iExists w1', w1, w2', w2. by iFrame.
    - iIntros "(%al & %ar & %bl & %br & H)".
      iDestruct "H" as "(-> & -> & H1 & H2)". iExists _, _, _, _. by iFrame.
  Qed.

  Lemma eq_lift_sum τ κ vl vr :
    ⟪ τ + κ ⟫ vl vr ⊣⊢ ∃ wl wr, (⌜vl = InjLV wl⌝ ∗ ⌜vr = InjLV wr⌝ ∗ ⟪ τ ⟫ wl wr)
                             ∨ (⌜vl = InjRV wl⌝ ∗ ⌜vr = InjRV wr⌝ ∗ ⟪ κ ⟫ wl wr).
  Proof.
    split=> d. rewrite eq_lift_unseal !monPred_at_exist /eq_lift_def /=.
        destruct d; rewrite /pick /sem_ty_sum /=; iSplit.
    - iIntros "(%w1 & %w2 & [(-> & -> & H)|(-> & -> & H)])"; iExists w1, w2;
        [iLeft|iRight]; by iFrame.
    - iIntros "(%wl & %wr & H)".
      iDestruct "H" as "[(-> & -> & H)|(-> & -> & H)]"; iExists _, _; [iLeft|iRight]; by iFrame.
    - iIntros "(%w1 & %w2 & [(-> & -> & H)|(-> & -> & H)])"; iExists w2, w1;
        [iLeft|iRight]; by iFrame.
    - iIntros "(%wl & %wr & H)".
      iDestruct "H" as "[(-> & -> & H)|(-> & -> & H)]"; iExists _, _; [iLeft|iRight]; by iFrame.
  Qed.

  Lemma eq_lift_mbang m τ vl vr : ⟪ ![m] τ ⟫ vl vr ⊣⊢ □?m ⟪ τ ⟫ vl vr.
  Proof. split=> d. by rewrite monPred_at_intuitionistically_if !eq_lift_at. Qed.

  Global Instance eq_lift_mbang_persistent τ vl vr : Persistent (⟪ ![MS] τ ⟫ vl vr).
  Proof. rewrite /Persistent eq_lift_mbang /=. by iIntros "#H !> !>". Qed.
  Global Instance eq_lift_mbang_from_modal τ vl vr :
    FromModal True%type modality_intuitionistically (⟪ ![MS] τ ⟫ vl vr) (⟪ ![MS] τ ⟫ vl vr) (⟪ τ ⟫ vl vr).
  Proof. rewrite /FromModal /= => _. by rewrite eq_lift_mbang. Qed.

  (* A semantic type that may depend on the direction, e.g. one
     instantiated at a direction-dependent row. *)
  Definition eq_lift_dep (τ : dir → sem_ty Σ) vl vr : iPropD Σ :=
    MonPred (λ d, τ d (pick d vl vr) (pick d vr vl)) _.

  Lemma eq_lift_dep_intro (τ : dir → sem_ty Σ) vl vr :
    (∀ d, ⊢ τ d (pick d vl vr) (pick d vr vl)) → ⊢ eq_lift_dep τ vl vr.
  Proof. intros H. split=> d. rewrite monPred_at_emp. iIntros "_". iApply H. Qed.

  (* Applying a function polymorphic in a row at a row [θd d] that depends
     on the direction. *)
  Lemma eq_lift_forall_app (A : sem_row Σ → sem_ty Σ) (ρ : sem_row Σ → sem_row Σ) κ
      (θd : dir → sem_row Σ) (fl fr wl wr : val) :
    ⊢ ⟪ ∀ᵣ θ, A θ -{ ρ θ }-∘ κ ⟫ fl fr -∗ eq_lift_dep (λ d, A (θd d)) wl wr -∗
      EQ fl wl ≈ fr wr <|EqThy (λ d, iLblSig_to_iLblThy (ρ (θd d)))|> {{ ⟪ κ ⟫ }}.
  Proof.
    iStartProof (iProp _). iIntros (d) "Hf Hw". rewrite eq_lift_at eq_rel_at /=.
    iSpecialize ("Hf" $! (θd d)). rewrite /sem_ty_arr /=.
    destruct d; rewrite /pick /=; iApply (brel_wand with "(Hf Hw)");
      iIntros "!>" (v1 v2) "H"; by rewrite eq_lift_at /pick /=.
  Qed.

  Lemma eq_lift_type_forall (C : sem_ty Σ → sem_ty Σ) vl vr : ⟪ ∀ₜ α, C α ⟫ vl vr ⊣⊢ ∀ α, ⟪ C α ⟫ vl vr.
  Proof. split=> d. by rewrite eq_lift_unseal monPred_at_forall. Qed.

  Lemma eq_lift_forall (C : sem_row Σ → sem_ty Σ) vl vr : ⟪ ∀ᵣ θ, C θ ⟫ vl vr ⊣⊢ ∀ θ, ⟪ C θ ⟫ vl vr.
  Proof. split=> d. by rewrite eq_lift_unseal monPred_at_forall. Qed.

  (* Introducing and using a (linear) arrow. *)
  Lemma eq_lift_arr (ρ : sem_row Σ) τ κ (fl fr : val) :
    (∀ wl wr, ⟪ τ ⟫ wl wr -∗ EQ fl wl ≈ fr wr <|iLblSig_to_iLblThy ρ|> {{ ⟪ κ ⟫ }}) ⊢ ⟪ τ -{ ρ }-∘ κ ⟫ fl fr.
  Proof.
    split=> d. rewrite monPred_at_forall eq_lift_at /=. iIntros "H" (w1 w2) "Hw".
    iSpecialize ("H" $! (pick d w1 w2)). rewrite monPred_at_forall.
    iSpecialize ("H" $! (pick d w2 w1)). rewrite monPred_at_wand.
    iSpecialize ("H" $! d with "[//] [Hw]"); first by rewrite eq_lift_at pick_pick_l pick_pick_r.
    rewrite eq_rel_at. destruct d; rewrite /pick /=; iApply (brel_wand with "H");
      iIntros "!> % % H"; by rewrite eq_lift_at /pick /=.
  Qed.

  Lemma eq_lift_app m (ρ : sem_row Σ) τ κ (fl fr wl wr : val) :
    ⊢ ⟪ τ -{ ρ }-[m]-> κ ⟫ fl fr -∗ ⟪ τ ⟫ wl wr -∗ EQ fl wl ≈ fr wr <|iLblSig_to_iLblThy ρ|> {{ ⟪ κ ⟫ }}.
  Proof.
    split=> d. rewrite monPred_at_emp monPred_at_wand. iIntros "_" (d1 <-) "Hf". rewrite monPred_at_wand.
    iIntros (d2 <-) "Hw". rewrite eq_rel_at !eq_lift_at /sem_ty_mbang /sem_ty_arr /=.
    iDestruct (bi.intuitionistically_if_elim with "Hf") as "Hf".
    destruct d; rewrite /pick /=; iApply (brel_wand with "(Hf Hw)");
      iIntros "!> % % H"; by rewrite eq_lift_at /pick /=.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* From an equivalence to the two typing judgements.                  *)
  (* ---------------------------------------------------------------- *)

  Lemma EQ_sem_typed (vl vr : val) (ρ : sem_row Σ) τ :
    (⊢ EQ vl ≈ vr <|iLblSig_to_iLblThy ρ|> {{ ⟪ τ ⟫ }}) →
    ∀ d, ⊢ sem_typed [] (pick d vl vr) (pick d vr vl) ρ τ [].
  Proof.
    intros [H] d. specialize (H d). rewrite monPred_at_emp eq_rel_at in H.
    iIntros (vs) "!> _". iPoseProof H as "H".
    destruct d; rewrite /pick /=; iApply (brel_wand with "(H [//])");
      iIntros "!>" (v1 v2) "Hτ"; rewrite eq_lift_at /pick /=; by iFrame.
  Qed.

  (* The same for expressions that substitution leaves unchanged, such as
     applications of closed values. *)
  Lemma EQ_sem_typed_expr (el er : expr) (ρ : sem_row Σ) τ (d : dir) :
    (⊢ EQ el ≈ er <|iLblSig_to_iLblThy ρ|> {{ ⟪ τ ⟫ }}) →
    (∀ vs, subst_map vs el = el) → (∀ vs, subst_map vs er = er) →
    ⊢ sem_typed [] (pick d el er) (pick d er el) ρ τ [].
  Proof.
    intros [H] Hl Hr. specialize (H d). rewrite monPred_at_emp eq_rel_at in H.
    iIntros (vs) "!> _". iPoseProof H as "H".
    destruct d; rewrite /pick /= Hl Hr; iApply (brel_wand with "(H [//])");
      iIntros "!>" (v1 v2) "Hτ"; rewrite eq_lift_at /pick /=; by iFrame.
  Qed.

End eq_rules.

Global Arguments eq_pt_l : simpl never.
Global Arguments eq_pt_r : simpl never.
Global Arguments eq_tp_l : simpl never.
Global Arguments eq_tp_r : simpl never.

(* ------------------------------------------------------------------ *)
(* Proof-mode lemmas and tactics.                                     *)
(* ------------------------------------------------------------------ *)

Section eq_tactics.
  Context `{!probblazeRGS Σ}.
  Implicit Types (el er : expr) (Δ : envs (iPropD Σ)) (ℓ : loc).

  Lemma tac_eq_pure_l {Δ E el el' er X R φ} n :
    DoPureSteps φ n el el' → φ →
    envs_entails Δ (EQ el' ≈ er @ E <|X|> {{ R }}) → envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof.
    rewrite envs_entails_unseal. intros [Hsteps] Hφ HΔ.
    assert (PureExec φ n el el') by (intros ?; by apply Hsteps). rewrite HΔ. by apply: eq_pure_l.
  Qed.

  Lemma tac_eq_pure_r {Δ E el er er' X R φ} n :
    DoPureSteps φ n er er' → φ →
    envs_entails Δ (EQ el ≈ er' @ E <|X|> {{ R }}) → envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof.
    rewrite envs_entails_unseal. intros [Hsteps] Hφ HΔ.
    assert (PureExec φ n er er') by (intros ?; by apply Hsteps). rewrite HΔ. by apply: eq_pure_r.
  Qed.

  Lemma tac_eq_load_l E K Δ i ℓ dq v p el el' er X R :
    IntoCtx el (TCEq (Load #ℓ)) K → envs_lookup i Δ = Some (p, ℓ ↦ₗ{dq} v)%I → el' = fill K (Val v) →
    envs_entails Δ (EQ el' ≈ er @ E <|X|> {{ R }}) → envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof.
    rewrite envs_entails_unseal=> HK Hi -> HΔ. apply tc_eq_fill in HK. rewrite -HK.
    iIntros "HΔ". iDestruct (envs_lookup_split with "HΔ") as "[Hl Hclose]"; first done.
    destruct p; simpl.
    - iDestruct "Hl" as "#Hl". iApply eq_load_l. iFrame "Hl". iIntros "_". iApply HΔ. by iApply ("Hclose" with "Hl").
    - iApply eq_load_l. iFrame "Hl". iIntros "Hl". iApply HΔ. by iApply "Hclose".
  Qed.

  Lemma tac_eq_load_r E K Δ i ℓ dq v p el er er' X R :
    IntoCtx er (TCEq (Load #ℓ)) K → envs_lookup i Δ = Some (p, ℓ ↦ᵣ{dq} v)%I → er' = fill K (Val v) →
    envs_entails Δ (EQ el ≈ er' @ E <|X|> {{ R }}) → envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof.
    rewrite envs_entails_unseal=> HK Hi -> HΔ. apply tc_eq_fill in HK. rewrite -HK.
    iIntros "HΔ". iDestruct (envs_lookup_split with "HΔ") as "[Hl Hclose]"; first done.
    destruct p; simpl.
    - iDestruct "Hl" as "#Hl". iApply eq_load_r. iFrame "Hl". iIntros "_". iApply HΔ. by iApply ("Hclose" with "Hl").
    - iApply eq_load_r. iFrame "Hl". iIntros "Hl". iApply HΔ. by iApply "Hclose".
  Qed.

  Lemma tac_eq_store_l E K Δ Δ' i ℓ v v' el el' er X R :
    IntoCtx el (TCEq (Store #ℓ (Val v))) K → envs_lookup i Δ = Some (false, ℓ ↦ₗ v')%I →
    envs_simple_replace i false (Esnoc Enil i (ℓ ↦ₗ v)) Δ = Some Δ' → el' = fill K #()%V →
    envs_entails Δ' (EQ el' ≈ er @ E <|X|> {{ R }}) → envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof.
    rewrite envs_entails_unseal=> HK ?? -> HΔ. apply tc_eq_fill in HK. rewrite -HK.
    rewrite envs_simple_replace_sound //; simpl. iIntros "[Hl Hclose]".
    iApply eq_store_l. iFrame "Hl". iIntros "Hl". iApply HΔ. iApply "Hclose". by iFrame.
  Qed.

  Lemma tac_eq_store_r E K Δ Δ' i ℓ v v' el er er' X R :
    IntoCtx er (TCEq (Store #ℓ (Val v))) K → envs_lookup i Δ = Some (false, ℓ ↦ᵣ v')%I →
    envs_simple_replace i false (Esnoc Enil i (ℓ ↦ᵣ v)) Δ = Some Δ' → er' = fill K #()%V →
    envs_entails Δ' (EQ el ≈ er' @ E <|X|> {{ R }}) → envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof.
    rewrite envs_entails_unseal=> HK ?? -> HΔ. apply tc_eq_fill in HK. rewrite -HK.
    rewrite envs_simple_replace_sound //; simpl. iIntros "[Hl Hclose]".
    iApply eq_store_r. iFrame "Hl". iIntros "Hl". iApply HΔ. iApply "Hclose". by iFrame.
  Qed.

  Lemma tac_eq_alloc_l E K Δ el er v X R :
    IntoCtx el (TCEq (Alloc (Val v))) K →
    envs_entails Δ (∀ ℓ : loc, ℓ ↦ₗ v -∗ EQ fill K #ℓ ≈ er @ E <|X|> {{ R }}) →
    envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof. rewrite envs_entails_unseal=> HK ->. apply tc_eq_fill in HK. rewrite -HK. apply eq_alloc_l. Qed.

  Lemma tac_eq_alloc_r E K Δ el er v X R :
    IntoCtx er (TCEq (Alloc (Val v))) K →
    envs_entails Δ (∀ ℓ : loc, ℓ ↦ᵣ v -∗ EQ el ≈ fill K #ℓ @ E <|X|> {{ R }}) →
    envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof. rewrite envs_entails_unseal=> HK ->. apply tc_eq_fill in HK. rewrite -HK. apply eq_alloc_r. Qed.

  Lemma tac_eq_alloctape_l E K Δ el er N z X R :
    TCEq N (Z.to_nat z) → IntoCtx el (TCEq (AllocTape #z)) K →
    envs_entails Δ (∀ α : loc, α ↪ₗN (N; []) -∗ EQ fill K #lbl:α ≈ er @ E <|X|> {{ R }}) →
    envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof. rewrite envs_entails_unseal=> ? HK ->. apply tc_eq_fill in HK. rewrite -HK. by apply eq_alloctape_l. Qed.

  Lemma tac_eq_alloctape_r E K Δ el er N z X R :
    TCEq N (Z.to_nat z) → IntoCtx er (TCEq (AllocTape #z)) K →
    envs_entails Δ (∀ α : loc, α ↪ᵣN (N; []) -∗ EQ el ≈ fill K #lbl:α @ E <|X|> {{ R }}) →
    envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof. rewrite envs_entails_unseal=> ? HK ->. apply tc_eq_fill in HK. rewrite -HK. by apply eq_alloctape_r. Qed.

  Lemma tac_eq_rand_l E K Δ Δ' i (α : loc) N (z : Z) n ns el el' er X R :
    IntoCtx el (TCEq (Rand #z #lbl:α)) K → envs_lookup i Δ = Some (false, α ↪ₗN (N; n :: ns))%I →
    TCEq N (Z.to_nat z) →
    envs_simple_replace i false (Esnoc Enil i (α ↪ₗN (N; ns))) Δ = Some Δ' → el' = fill K #n →
    envs_entails Δ' (⌜n ≤ N⌝ -∗ EQ el' ≈ er @ E <|X|> {{ R }}) → envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof.
    rewrite envs_entails_unseal=> HK ? ?? -> HΔ. apply tc_eq_fill in HK. rewrite -HK.
    rewrite envs_simple_replace_sound //; simpl. iIntros "[Hα Hclose]".
    iApply eq_rand_l. iFrame "Hα". iIntros "Hα %Hn". iApply (HΔ with "[Hα Hclose]"); last done.
    iApply "Hclose". by iFrame.
  Qed.

  Lemma tac_eq_rand_r E K Δ Δ' i (α : loc) N (z : Z) n ns el er er' X R :
    IntoCtx er (TCEq (Rand #z #lbl:α)) K → envs_lookup i Δ = Some (false, α ↪ᵣN (N; n :: ns))%I →
    TCEq N (Z.to_nat z) →
    envs_simple_replace i false (Esnoc Enil i (α ↪ᵣN (N; ns))) Δ = Some Δ' → er' = fill K #n →
    envs_entails Δ' (⌜n ≤ N⌝ -∗ EQ el ≈ er' @ E <|X|> {{ R }}) → envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof.
    rewrite envs_entails_unseal=> HK ? ?? -> HΔ. apply tc_eq_fill in HK. rewrite -HK.
    rewrite envs_simple_replace_sound //; simpl. iIntros "[Hα Hclose]".
    iApply eq_rand_r. iFrame "Hα". iIntros "Hα %Hn". iApply (HΔ with "[Hα Hclose]"); last done.
    iApply "Hclose". by iFrame.
  Qed.

  Lemma tac_eq_couple_tape_rand E K Δ Δ' i (α : loc) N (z : Z) ns el er X R :
    IntoCtx er (TCEq (Rand #z #()%V)) K →
    envs_lookup_delete false i Δ = Some (false, α ↪ₗN (N; ns), Δ')%I →
    TCEq N (Z.to_nat z) → to_val el = None →
    envs_entails Δ' (∀ n, ⌜n ≤ N⌝ -∗ α ↪ₗN (N; ns ++ [n]) -∗ EQ el ≈ fill K #n @ E <|X|> {{ R }}) →
    envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof.
    rewrite envs_entails_unseal=> HK Hlk ? Hel HΔ. apply tc_eq_fill in HK. rewrite -HK.
    rewrite envs_lookup_delete_sound //=. iIntros "[Hα HΔ]".
    iApply eq_couple_tape_rand; [done|]. iFrame "Hα". by iApply HΔ.
  Qed.

  Lemma tac_eq_couple_rand_tape E K Δ Δ' i (α : loc) N (z : Z) ns el er X R :
    IntoCtx el (TCEq (Rand #z #()%V)) K →
    envs_lookup_delete false i Δ = Some (false, α ↪ᵣN (N; ns), Δ')%I →
    TCEq N (Z.to_nat z) → to_val er = None →
    envs_entails Δ' (∀ n, ⌜n ≤ N⌝ -∗ α ↪ᵣN (N; ns ++ [n]) -∗ EQ fill K #n ≈ er @ E <|X|> {{ R }}) →
    envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof.
    rewrite envs_entails_unseal=> HK Hlk ? Her HΔ. apply tc_eq_fill in HK. rewrite -HK.
    rewrite envs_lookup_delete_sound //=. iIntros "[Hα HΔ]".
    iApply eq_couple_rand_tape; [done|]. iFrame "Hα". by iApply HΔ.
  Qed.

  (* Focusing on a subexpression [e] of [l] (or [r]) in evaluation position. *)
  Lemma tac_eq_focus_l Δ E X R K e el er :
    IntoCtx el (TCEq e) K →
    envs_entails Δ (EQ fill K e ≈ er @ E <|X|> {{ R }}) → envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof. intros HK. apply tc_eq_fill in HK. by rewrite -HK. Qed.

  Lemma tac_eq_focus_r Δ E X R K e el er :
    IntoCtx er (TCEq e) K →
    envs_entails Δ (EQ el ≈ fill K e @ E <|X|> {{ R }}) → envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof. intros HK. apply tc_eq_fill in HK. by rewrite -HK. Qed.

End eq_tactics.

Ltac eq_goal_check tac :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _ (eq_rel _ _ _ _ _) => tac
  | |- _ => fail "not an EQ goal"
  end.

Tactic Notation "eq_pures_l" :=
  eq_goal_check ltac:(
    notypeclasses refine (tac_eq_pure_l (S _) _ _ _);
      [ tc_solve || fail 1 "eq_pures_l: no pure steps can be performed"
      | try done
      | simpl; pm_prettify ]).

Tactic Notation "eq_pures_r" :=
  eq_goal_check ltac:(
    notypeclasses refine (tac_eq_pure_r (S _) _ _ _);
      [ tc_solve || fail 1 "eq_pures_r: no pure steps can be performed"
      | try done
      | simpl; pm_prettify ]).

Tactic Notation "eq_load_l" :=
  eq_goal_check ltac:(
    eapply tac_eq_load_l;
    [ tc_solve || fail "eq_load_l: cannot find a load"
    | let ℓ := match goal with |- _ = Some (_, eq_pt_l ?ℓ _ _) => ℓ end in
      iAssumptionCore || fail "eq_load_l: cannot find" ℓ "↦ₗ ?"
    | reflexivity
    | simpl ]).

Tactic Notation "eq_load_r" :=
  eq_goal_check ltac:(
    eapply tac_eq_load_r;
    [ tc_solve || fail "eq_load_r: cannot find a load"
    | let ℓ := match goal with |- _ = Some (_, eq_pt_r ?ℓ _ _) => ℓ end in
      iAssumptionCore || fail "eq_load_r: cannot find" ℓ "↦ᵣ ?"
    | reflexivity
    | simpl ]).

Tactic Notation "eq_store_l" :=
  eq_goal_check ltac:(
    eapply tac_eq_store_l;
    [ tc_solve || fail "eq_store_l: cannot find a store"
    | let ℓ := match goal with |- _ = Some (_, eq_pt_l ?ℓ _ _) => ℓ end in
      iAssumptionCore || fail "eq_store_l: cannot find" ℓ "↦ₗ ?"
    | pm_reflexivity
    | reflexivity
    | simpl ]).

Tactic Notation "eq_store_r" :=
  eq_goal_check ltac:(
    eapply tac_eq_store_r;
    [ tc_solve || fail "eq_store_r: cannot find a store"
    | let ℓ := match goal with |- _ = Some (_, eq_pt_r ?ℓ _ _) => ℓ end in
      iAssumptionCore || fail "eq_store_r: cannot find" ℓ "↦ᵣ ?"
    | pm_reflexivity
    | reflexivity
    | simpl ]).

Tactic Notation "eq_alloc_l" simple_intropattern(ℓ) "as" constr(H) :=
  eq_goal_check ltac:(
    eapply tac_eq_alloc_l; [ tc_solve || fail "eq_alloc_l: no allocation found" | simpl; iIntros (ℓ) H ]).

Tactic Notation "eq_alloc_r" simple_intropattern(ℓ) "as" constr(H) :=
  eq_goal_check ltac:(
    eapply tac_eq_alloc_r; [ tc_solve || fail "eq_alloc_r: no allocation found" | simpl; iIntros (ℓ) H ]).

Tactic Notation "eq_alloctape_l" simple_intropattern(α) "as" constr(H) :=
  eq_goal_check ltac:(
    eapply tac_eq_alloctape_l;
    [ tc_solve | tc_solve || fail "eq_alloctape_l: no tape allocation found" | simpl; iIntros (α) H ]).

Tactic Notation "eq_alloctape_r" simple_intropattern(α) "as" constr(H) :=
  eq_goal_check ltac:(
    eapply tac_eq_alloctape_r;
    [ tc_solve | tc_solve || fail "eq_alloctape_r: no tape allocation found" | simpl; iIntros (α) H ]).

Tactic Notation "eq_rand_l" "as" constr(H) :=
  eq_goal_check ltac:(
    eapply tac_eq_rand_l;
    [ tc_solve || fail "eq_rand_l: no rand found"
    | let α := match goal with |- _ = Some (_, eq_tp_l ?α _ _ _) => α end in
      iAssumptionCore || fail "eq_rand_l: cannot find tape" α
    | tc_solve
    | pm_reflexivity
    | reflexivity
    | simpl; iIntros H ]).

Tactic Notation "eq_rand_r" "as" constr(H) :=
  eq_goal_check ltac:(
    eapply tac_eq_rand_r;
    [ tc_solve || fail "eq_rand_r: no rand found"
    | let α := match goal with |- _ = Some (_, eq_tp_r ?α _ _ _) => α end in
      iAssumptionCore || fail "eq_rand_r: cannot find tape" α
    | tc_solve
    | pm_reflexivity
    | reflexivity
    | simpl; iIntros H ]).

(* [eq_couple_tape_rand "Hα"]: couple the tape [α ↪ₗN (N; ns)] in "Hα" with
   a [rand] of [r]; [eq_couple_rand_tape "Hα"] is the mirror image.  The goal
   becomes [∀ n, ⌜n ≤ N⌝ -∗ α ↪ₗN (N; ns ++ [n]) -∗ …]. *)
Tactic Notation "eq_couple_tape_rand" constr(H) :=
  eq_goal_check ltac:(
    eapply (tac_eq_couple_tape_rand _ _ _ _ H);
    [ tc_solve || fail "eq_couple_tape_rand: no rand found in r"
    | pm_reflexivity || fail "eq_couple_tape_rand: cannot find tape" H
    | tc_solve
    | done || fail "eq_couple_tape_rand: l is a value"
    | ]).

Tactic Notation "eq_couple_rand_tape" constr(H) :=
  eq_goal_check ltac:(
    eapply (tac_eq_couple_rand_tape _ _ _ _ H);
    [ tc_solve || fail "eq_couple_rand_tape: no rand found in l"
    | pm_reflexivity || fail "eq_couple_rand_tape: cannot find tape" H
    | tc_solve
    | done || fail "eq_couple_rand_tape: r is a value"
    | ]).

(* [eq_focus_l e]: write [l] as [fill K e], so that a rule stated for
   [fill K e] can be applied with [iApply]. *)
Tactic Notation "eq_focus_l" open_constr(e) :=
  eq_goal_check ltac:(
    eapply (tac_eq_focus_l _ _ _ _ _ e);
    [ tc_solve || fail "eq_focus_l: no such subexpression in l" | ]).

Tactic Notation "eq_focus_r" open_constr(e) :=
  eq_goal_check ltac:(
    eapply (tac_eq_focus_r _ _ _ _ _ e);
    [ tc_solve || fail "eq_focus_r: no such subexpression in r" | ]).

(* [eq_lift_l lemL lemR]: a step of [l] given by a refinement rule [lemL] for
   the left program and its mirror [lemR] for the right program, as a pair
   [brel_X_l]/[brel_X_r] of rules stated over [fill K]; [eq_lift_r] is the
   same for a step of [r]. *)
Tactic Notation "eq_lift_l" uconstr(lemL) uconstr(lemR) :=
  iApply eq_step_l;
  [ let e := fresh "e" in let S := fresh "S" in
    intros e S; iIntros "Hstep"; iApply lemL; first [done | iApply "Hstep"]
  | let e := fresh "e" in let S := fresh "S" in
    intros e S; iIntros "Hstep"; iApply lemR; first [done | iApply "Hstep"]
  | ].

Tactic Notation "eq_lift_r" uconstr(lemL) uconstr(lemR) :=
  iApply eq_step_r;
  [ let e := fresh "e" in let S := fresh "S" in
    intros e S; iIntros "Hstep"; iApply lemL; first [done | iApply "Hstep"]
  | let e := fresh "e" in let S := fresh "S" in
    intros e S; iIntros "Hstep"; iApply lemR; first [done | iApply "Hstep"]
  | ].

(* Focusing on an unlabelled [rand] before a coupling rule. *)
Tactic Notation "eq_couple_rand_rand" :=
  eq_focus_l (rand #_)%E; eq_focus_r (rand #_)%E; iApply eq_couple_rand_rand.

(* [eq_reshape_l e]: write [l] as [fill K e] for the evaluation context [K]
   around the subexpression [e] (which may contain evars), through any
   frames, handlers included. *)
Ltac eq_find_ctx e sub :=
  match constr:(tt) with
  | _ => let _ := match constr:(tt) with _ => unify e sub end in constr:(@nil frame)
  | _ =>
      let p := eval hnf in (get_frame e) in
      lazymatch p with
      | Some (?f, ?e1) => let k := eq_find_ctx e1 sub in constr:(f :: k)
      end
  end.

Tactic Notation "eq_reshape_l" open_constr(sub) :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _ (eq_rel _ ?el _ _ _) =>
      let k := eq_find_ctx el sub in change el with (fill k sub)
  end.

Tactic Notation "eq_reshape_r" open_constr(sub) :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _ (eq_rel _ _ ?er _ _) =>
      let k := eq_find_ctx er sub in change er with (fill k sub)
  end.
