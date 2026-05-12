(** Helper definitions and lemmas for the 2-SAT proof. *)

From clutch.common Require Import inject.
From clutch.eris Require Import eris.
From clutch.eris.lib Require Import list array.
From clutch.eris.tutorial Require Import two_sat two_sat_err_rec eris_rules.

Set Default Proof Using "Type*".

(** ** Rocq-level model of 2-SAT *)

Definition lit : Type := bool * nat.
Definition clause : Type := lit * lit.

Definition lit_index (l : lit) : nat := snd l.

Definition eval_lit_pure (a : list bool) (l : lit) : bool :=
  let '(b, i) := l in
  if b then negb (a !!! i) else (a !!! i).

Definition eval_clause_pure (a : list bool) (c : clause) : bool :=
  let '(l1, l2) := c in
  eval_lit_pure a l1 || eval_lit_pure a l2.

Definition satisfies (a : list bool) (cls : list clause) : Prop :=
  Forall (fun c => eval_clause_pure a c = true) cls.

Definition is_satisfiable (nvars : nat) (cls : list clause) : Prop :=
  exists w, length w = nvars /\ satisfies w cls.

Definition lit_well_formed (nvars : nat) (l : lit) : Prop :=
  (lit_index l < nvars)%nat.
Definition clause_well_formed (nvars : nat) (c : clause) : Prop :=
  lit_well_formed nvars (fst c) /\ lit_well_formed nvars (snd c).
Definition formula_well_formed (nvars : nat) (cls : list clause) : Prop :=
  Forall (clause_well_formed nvars) cls.

Definition flip_var (bs : list bool) (i : nat) : list bool :=
  <[i := negb (bs !!! i)]> bs.

Fixpoint hamming (a b : list bool) : nat :=
  match a with
  | [] => 0%nat
  | x :: xs =>
      match b with
      | [] => 0%nat
      | y :: ys =>
          ((if Bool.eqb x y then 0%nat else 1%nat) + hamming xs ys)%nat
      end
  end.

Lemma hamming_le_length a b :
  length a = length b ->
  (hamming a b <= length a)%nat.
Proof.
  revert b. induction a as [|x xs IH]; intros [|y ys] Hlen; simpl in *; try lia.
  specialize (IH ys ltac:(lia)).
  destruct (Bool.eqb x y); simpl; lia.
Qed.

(** Convenient reductions of [flip_var] on a cons. *)
Lemma flip_var_cons_O x xs : flip_var (x :: xs) 0 = negb x :: xs.
Proof. by unfold flip_var. Qed.

Lemma flip_var_cons_S x xs i : flip_var (x :: xs) (S i) = x :: flip_var xs i.
Proof. by unfold flip_var. Qed.

(** If position [i] is a disagreement, the Hamming distance is at least 1. *)
Lemma hamming_diff_ge_1 bs w i :
  length bs = length w ->
  (i < length bs)%nat ->
  bs !!! i ≠ w !!! i ->
  (1 <= hamming bs w)%nat.
Proof.
  revert w i.
  induction bs as [|x xs IH]; intros [|y ys] [|i'] Hlen Hi Hne;
    try (simpl in *; lia).
  - simpl in Hne. simpl.
    destruct (Bool.eqb x y) eqn:Heq.
    + apply Bool.eqb_prop in Heq. contradiction.
    + lia.
  - simpl in *.
    pose proof (IH ys i' ltac:(lia) ltac:(lia) Hne).
    destruct (Bool.eqb x y); lia.
Qed.

(** Flipping a position that disagrees decreases Hamming by exactly 1. *)
Lemma hamming_flip_diff bs w i :
  length bs = length w ->
  (i < length bs)%nat ->
  bs !!! i ≠ w !!! i ->
  hamming (flip_var bs i) w = (hamming bs w - 1)%nat.
Proof.
  revert w i.
  induction bs as [|x xs IH]; intros [|y ys] [|i'] Hlen Hi Hne;
    try (simpl in *; lia).
  - rewrite flip_var_cons_O. simpl in Hne. simpl.
    destruct x, y; simpl in *; try contradiction; lia.
  - rewrite flip_var_cons_S. simpl in *.
    rewrite (IH ys i' ltac:(lia) ltac:(lia) Hne).
    pose proof (hamming_diff_ge_1 xs ys i' ltac:(lia) ltac:(lia) Hne).
    destruct (Bool.eqb x y); lia.
Qed.

(** Flipping a position that agrees increases Hamming by exactly 1. *)
Lemma hamming_flip_same bs w i :
  length bs = length w ->
  (i < length bs)%nat ->
  bs !!! i = w !!! i ->
  hamming (flip_var bs i) w = (hamming bs w + 1)%nat.
Proof.
  revert w i.
  induction bs as [|x xs IH]; intros [|y ys] [|i'] Hlen Hi Heq;
    try (simpl in *; lia).
  - rewrite flip_var_cons_O. simpl in Heq. simpl.
    destruct x, y; simpl in *; try discriminate; lia.
  - rewrite flip_var_cons_S. simpl in *.
    rewrite (IH ys i' ltac:(lia) ltac:(lia) Heq).
    destruct (Bool.eqb x y); lia.
Qed.

(** If a clause is unsatisfied by [bs] but satisfied by [w], then at least
    one of its variables disagrees between [bs] and [w]; in particular the
    Hamming distance is positive. *)
Lemma clause_disagree_ge_1 c bs w (nvars : nat) :
  clause_well_formed nvars c ->
  length bs = nvars ->
  length w = nvars ->
  eval_clause_pure bs c = false ->
  eval_clause_pure w c = true ->
  (1 <= hamming bs w)%nat.
Proof.
  intros Hwf Hlen Hwlen Hunsat Hsat.
  destruct c as [[b1 i1] [b2 i2]].
  rewrite /clause_well_formed /lit_well_formed /lit_index /= in Hwf.
  destruct Hwf as [Hi1 Hi2].
  simpl in Hunsat. apply orb_false_iff in Hunsat. destruct Hunsat as [Hu1 Hu2].
  simpl in Hsat. apply orb_true_iff in Hsat.
  assert (Hbs1 : bs !!! i1 = b1).
  { destruct b1; simpl in Hu1; [apply negb_false_iff|]; exact Hu1. }
  assert (Hbs2 : bs !!! i2 = b2).
  { destruct b2; simpl in Hu2; [apply negb_false_iff|]; exact Hu2. }
  destruct Hsat as [Hs1 | Hs2].
  - apply (hamming_diff_ge_1 bs w i1); [lia | lia |].
    rewrite Hbs1. destruct b1; simpl in Hs1.
    + apply negb_true_iff in Hs1. congruence.
    + congruence.
  - apply (hamming_diff_ge_1 bs w i2); [lia | lia |].
    rewrite Hbs2. destruct b2; simpl in Hs2.
    + apply negb_true_iff in Hs2. congruence.
    + congruence.
Qed.

(** If Hamming is at its maximum (= length), every position disagrees. *)
Lemma hamming_max_diff bs w i :
  length bs = length w ->
  hamming bs w = length bs ->
  (i < length bs)%nat ->
  bs !!! i ≠ w !!! i.
Proof.
  revert w i.
  induction bs as [|x xs IH]; intros [|y ys] [|i'] Hlen Hh Hi;
    try (simpl in *; lia).
  - simpl in Hh. simpl.
    destruct (Bool.eqb x y) eqn:Heq.
    + pose proof (hamming_le_length xs ys ltac:(simpl in Hlen; lia)).
      simpl in Hh. lia.
    + apply Bool.eqb_false_iff in Heq. exact Heq.
  - simpl in *.
    destruct (Bool.eqb x y) eqn:Heq.
    + pose proof (hamming_le_length xs ys ltac:(lia)).
      simpl in Hh. lia.
    + apply (IH ys i' ltac:(lia)); [simpl in Hh; lia | lia].
Qed.

(** ** Encoding-hiding predicates that don't need [Σ] *)

Definition is_lit (l : lit) (lv : val) : Prop := lv = inject l.
Definition is_clause (c : clause) (cv : val) : Prop := cv = inject c.

Definition is_unsat_result (res : option clause) (v : val) : Prop :=
  match res with
  | None => v = NONEV
  | Some c => exists cv, v = SOMEV cv /\ is_clause c cv
  end.

Definition find_unsat_post (bs : list bool) (cls : list clause)
                           (res : option clause) : Prop :=
  match res with
  | None => satisfies bs cls
  | Some c => In c cls /\ eval_clause_pure bs c = false
  end.

(** ** Local copies of the library's [array_init] definitions *)

Local Definition array_init_loop' : val :=
  rec: "loop" "src" "i" "n" "f" :=
    if: "i" = "n" then #()
    else "src" +ₗ "i" <- "f" "i";;
         "loop" "src" ("i" + #1) "n" "f".

Local Definition array_init' : val :=
  λ: "n" "f",
    let: "src" := AllocN "n" #() in
    array_init_loop' "src" #0 "n" "f";;
    "src".

Lemma array_init_eq : array_init = array_init'.
Proof. reflexivity. Qed.

(** Bundled facts about an unsatisfied clause in a well-formed satisfiable
    formula: well-formedness, satisfaction by the witness, and at least one
    bit of disagreement between [bs] and [w]. *)
Lemma unsat_clause_facts c bs w (nvars : nat) (cls : list clause) :
  In c cls ->
  formula_well_formed nvars cls ->
  satisfies w cls ->
  eval_clause_pure bs c = false ->
  length bs = nvars ->
  length w = nvars ->
  clause_well_formed nvars c
  /\ eval_clause_pure w c = true
  /\ (1 <= hamming bs w)%nat.
Proof.
  intros Hin Hwf Hsatw Hbad Hlen Hwlen.
  assert (Hwfc : clause_well_formed nvars c).
  { rewrite /formula_well_formed in Hwf.
    by eapply List.Forall_forall in Hwf. }
  assert (Hsat_c : eval_clause_pure w c = true).
  { rewrite /satisfies in Hsatw.
    by eapply List.Forall_forall in Hsatw. }
  do 2 (split; [assumption|]).
  exact (clause_disagree_ge_1 c bs w nvars Hwfc Hlen Hwlen Hbad Hsat_c).
Qed.

(** ** Side-condition hints for auto

    These derived facts package the recurring side conditions in
    [papa_loop_spec] and [papa_2sat_correct] — [err]-nonnegativity, the
    Papadimitriou bound at the current Hamming distance, the [↯ ≥ 1]
    contradiction at zero budget, and Hamming-distance length bounds.
    They are registered as [Hint Resolve] so [auto] / [eauto] can chain
    them to discharge those side conditions. *)

Lemma hamming_le_nvars (a b : list bool) (nvars : nat) :
  length a = nvars -> length b = nvars -> (hamming a b <= nvars)%nat.
Proof. intros. pose proof (hamming_le_length a b ltac:(lia)). lia. Qed.

Lemma err_papa_hamming (nvars : nat) (a b : list bool) :
  length a = nvars -> length b = nvars ->
  (err nvars (2 * nvars * nvars) (hamming a b) <= 1 / 2)%R.
Proof. intros. apply err_papa. by apply hamming_le_nvars. Qed.

Lemma err_zero_ge_1 (nvars k : nat) :
  (1 <= k)%nat -> (1 <= err nvars 0 k)%R.
Proof. destruct k; [lia | rewrite err_O_S; lra]. Qed.

Lemma hamming_unsat_ge_1 c bs w (nvars : nat) (cls : list clause) :
  In c cls -> formula_well_formed nvars cls -> satisfies w cls ->
  eval_clause_pure bs c = false ->
  length bs = nvars -> length w = nvars ->
  (1 <= hamming bs w)%nat.
Proof. intros. by destruct (unsat_clause_facts _ _ _ _ _ H H0 H1 H2 H3 H4)
                       as (_ & _ & ?). Qed.

#[global] Hint Resolve err_nonneg err_papa_hamming err_zero_ge_1
                       hamming_le_nvars hamming_unsat_ge_1 : core.
#[global] Hint Extern 2 ((err _ _ _ <= err _ _ _)%R) =>
  apply err_mono_k; lia : core.

Section helpers.
  Context `{!erisGS Σ}.

  (** ** Iris-level representation predicates *)

  Definition bool_array (a : loc) (bs : list bool) : iProp Σ :=
    a ↦∗ ((λ b : bool, #b) <$> bs).

  Definition is_formula (cls : list clause) (clsv : val) : Prop :=
    is_list cls clsv.

  (** ** Load / store wrappers for [bool_array] *)

  Lemma twp_bool_array_load a bs (i : nat) (b : bool) E :
    bs !! i = Some b ->
    [[{ bool_array a bs }]]
      ! #(a +ₗ i) @ E
    [[{ RET #b; bool_array a bs }]].
  Proof.
    iIntros (Hlk Φ) "Hba HΦ".
    rewrite /bool_array.
    assert (Hfm : ((λ b0 : bool, #b0) <$> bs) !! i = Some #b).
    { rewrite list_lookup_fmap Hlk //. }
    wp_apply (twp_load_offset with "Hba"); [exact Hfm|].
    iIntros "Hba". by iApply "HΦ".
  Qed.

  Lemma twp_bool_array_store a bs (i : nat) (b : bool) E :
    (i < length bs)%nat ->
    [[{ bool_array a bs }]]
      #(a +ₗ i) <- #b @ E
    [[{ RET #(); bool_array a (<[i := b]> bs) }]].
  Proof.
    iIntros (Hi Φ) "Hba HΦ".
    rewrite /bool_array.
    assert (Hsome : is_Some (((λ b0 : bool, #b0) <$> bs) !! i)).
    { apply lookup_lt_is_Some. rewrite length_fmap. lia. }
    wp_apply (twp_store_offset with "Hba"); [exact Hsome|].
    iIntros "Hba". iApply "HΦ".
    by rewrite list_fmap_insert /=.
  Qed.

  (** ** Total-correctness array_init *)

  Section array_init_twp.
    Context (Q : nat → val → iProp Σ).
    Implicit Types (f v : val) (i j : nat).

    Local Lemma twp_array_init_loop E l i n k f :
      n = Z.of_nat (i + k) →
      [[{ (l +ₗ i) ↦∗ replicate k #() ∗
          [∗ list] j ∈ seq i k, WP f #(j : nat) @ E [{ Q j }]
      }]]
        array_init_loop' #l #i #n f @ E
      [[{ vs, RET #();
        ⌜ length vs = k ⌝ ∗ (l +ₗ i) ↦∗ vs ∗ [∗ list] j↦v ∈ vs, Q (i + j) v
      }]].
    Proof.
      iIntros (Hn Φ) "[Hl Hf] HΦ".
      iInduction k as [|k] "IH" forall (i Hn); simplify_eq/=; wp_rec; wp_pures.
      { rewrite bool_decide_eq_true_2; last (repeat f_equal; lia).
        wp_pures. iApply ("HΦ" $! []). auto. }
      rewrite bool_decide_eq_false_2; last naive_solver lia.
      iDestruct (array_cons with "Hl") as "[Hl HSl]".
      iDestruct "Hf" as "[Hf HSf]".
      wp_smart_apply (tgl_wp_wand with "Hf").
      iIntros (v) "Hv".
      wp_store. wp_pures.
      rewrite Z.add_1_r -Nat2Z.inj_succ.
      iApply ("IH" with "[%] [HSl] HSf"); first lia.
      { by rewrite loc_add_assoc Z.add_1_r -Nat2Z.inj_succ. }
      iIntros (vs). iDestruct 1 as (<-) "[HSl Hvs]".
      iApply ("HΦ" $! (v :: vs)). iSplit; [naive_solver|]. iSplitL "Hl HSl".
      - iFrame "Hl". by rewrite loc_add_assoc Z.add_1_r -Nat2Z.inj_succ.
      - iEval (rewrite /= Nat.add_0_r; setoid_rewrite Nat.add_succ_r). iFrame.
    Qed.

    Lemma twp_array_init E n f :
      (0 < n)%Z →
      [[{
        [∗ list] i ∈ seq 0 (Z.to_nat n), WP f #(i : nat) @ E [{ Q i }]
      }]]
        array_init #n f @ E
      [[{ l vs, RET #l;
        ⌜Z.of_nat (length vs) = n⌝ ∗ l ↦∗ vs ∗ [∗ list] k↦v ∈ vs, Q k v
      }]].
    Proof.
      iIntros (Hn Φ) "Hf HΦ".
      rewrite array_init_eq /array_init'.
      wp_lam. wp_alloc l as "Hl"; first done.
      wp_smart_apply (twp_array_init_loop _ _ 0 n (Z.to_nat n)
        with "[Hl $Hf]").
      { by rewrite /= Z2Nat.id; last lia. }
      { by rewrite loc_add_0. }
      iIntros (vs).
      iDestruct 1 as (Hlen) "[Hl Hvs]". wp_pures.
      iApply ("HΦ" $! _ vs). iModIntro. iSplit.
      { iPureIntro. by rewrite Hlen Z2Nat.id; last lia. }
      rewrite loc_add_0. iFrame.
    Qed.

  End array_init_twp.

  (** ** Sub-specifications for the helpers in [two_sat.v] *)

  Lemma twp_eval_lit a (bs : list bool) (l : lit) (lv : val) (nvars : nat) :
    is_lit l lv ->
    lit_well_formed nvars l ->
    length bs = nvars ->
    [[{ bool_array a bs }]]
      eval_lit #a lv
    [[{ RET #(eval_lit_pure bs l); bool_array a bs }]].
  Proof.
    iIntros (Hlit Hwf Hlen Φ) "Hba HΦ".
    destruct l as [b i].
    rewrite /is_lit /= in Hlit. subst lv.
    rewrite /lit_well_formed /lit_index /= in Hwf.
    assert (Hi : (i < length bs)%nat) by lia.
    destruct (lookup_lt_is_Some_2 bs i Hi) as [v Hv].
    rewrite /eval_lit. wp_pures.
    wp_apply (twp_bool_array_load with "Hba"); [exact Hv|].
    iIntros "Hba".
    rewrite /eval_lit_pure /= (list_lookup_total_correct _ _ _ Hv).
    destruct b.
    - wp_pures. rewrite /lang_negb. wp_pures.
      destruct v; wp_pures; iModIntro; by iApply "HΦ".
    - wp_pures. iModIntro. by iApply "HΦ".
  Qed.

  Lemma twp_eval_clause a (bs : list bool) (c : clause) (cv : val) (nvars : nat) :
    is_clause c cv ->
    clause_well_formed nvars c ->
    length bs = nvars ->
    [[{ bool_array a bs }]]
      eval_clause #a cv
    [[{ RET #(eval_clause_pure bs c); bool_array a bs }]].
  Proof.
    iIntros (Hcl Hwf Hlen Φ) "Hba HΦ".
    destruct c as [l1 l2].
    rewrite /is_clause /= in Hcl. subst cv.
    rewrite /clause_well_formed /= in Hwf. destruct Hwf as [Hwf1 Hwf2].
    rewrite /eval_clause. wp_pures.
    wp_apply (twp_eval_lit _ _ l1 _ nvars with "Hba"); [done|done|done|].
    iIntros "Hba".
    rewrite /eval_clause_pure /=.
    destruct (eval_lit_pure bs l1) eqn:Hl1.
    - wp_pures. iModIntro. by iApply "HΦ".
    - wp_pures.
      wp_apply (twp_eval_lit _ _ l2 _ nvars with "Hba"); [done|done|done|].
      iIntros "Hba". by iApply "HΦ".
  Qed.

  Lemma twp_find_unsat a (bs : list bool) (cls : list clause) (clsv : val)
        (nvars : nat) :
    formula_well_formed nvars cls ->
    is_formula cls clsv ->
    length bs = nvars ->
    [[{ bool_array a bs }]]
      find_unsat #a clsv
    [[{ res resv, RET resv;
         bool_array a bs ∗
         ⌜is_unsat_result res resv⌝ ∗
         ⌜find_unsat_post bs cls res⌝ }]].
  Proof.
    iIntros (Hwf Hform Hlen Φ) "Hba HΦ".
    iInduction cls as [|c cls'] "IH" forall (clsv Hwf Hform Φ).
    - rewrite /is_formula /= in Hform. subst clsv.
      rewrite /find_unsat. wp_pures. iModIntro.
      iApply ("HΦ" $! None NONEV). iFrame. iPureIntro. split.
      + reflexivity.
      + by apply Forall_nil.
    - rewrite /is_formula /= in Hform.
      destruct Hform as (clsv' & -> & Htail).
      pose proof (Forall_inv Hwf) as Hwfc.
      pose proof (Forall_inv_tail Hwf) as Hwfrest.
      rewrite /find_unsat. wp_pures. fold find_unsat.
      wp_apply (twp_eval_clause with "Hba"); [done|done|done|].
      iIntros "Hba".
      destruct (eval_clause_pure bs c) eqn:Hc.
      + wp_pures.
        wp_apply ("IH" $! clsv' Hwfrest Htail with "Hba").
        iIntros (res resv) "(Hba & %Hres & %Hpost)".
        iApply ("HΦ" $! res resv). iFrame. iPureIntro. split; [done|].
        destruct res as [c0|]; simpl in Hpost |- *.
        * destruct Hpost as [Hin Hbad]. split; [by right | done].
        * by apply Forall_cons.
      + wp_pures. iModIntro.
        iApply ("HΦ" $! (Some c) (SOMEV (inject c))). iFrame.
        iPureIntro. split.
        * exists (inject c). split; [done | reflexivity].
        * split; [by left | done].
  Qed.

  Lemma twp_flip_random_var a (bs : list bool) (c : clause) (cv : val)
        (nvars : nat) (ε0 ε1 : R) :
    is_clause c cv ->
    clause_well_formed nvars c ->
    length bs = nvars ->
    (0 <= ε0)%R -> (0 <= ε1)%R ->
    [[{ bool_array a bs ∗ ↯ ((ε0 + ε1) / 2) }]]
      flip_random_var #a cv
    [[{ RET #();
         ∃ bs',
           bool_array a bs' ∗
           ⌜length bs' = nvars⌝ ∗
           (⌜bs' = flip_var bs (lit_index (fst c))⌝ ∗ ↯ ε0
            ∨
            ⌜bs' = flip_var bs (lit_index (snd c))⌝ ∗ ↯ ε1) }]].
  Proof.
    iIntros (Hcl Hwf Hlen Hε0 Hε1 Φ) "[Hba Herr] HΦ".
    destruct c as [[b1 i1] [b2 i2]].
    rewrite /is_clause /= in Hcl. subst cv.
    rewrite /clause_well_formed /lit_well_formed /lit_index /= in Hwf.
    destruct Hwf as [Hi1 Hi2].
    rewrite /flip_random_var. wp_pures.
    set (ε2 := λ n : nat, if bool_decide (n = 0%nat) then ε0 else ε1).
    wp_apply (twp_rand_exp ε2 1 with "Herr").
    { intros n. unfold ε2. case_bool_decide; done. }
    { unfold ε2. simpl. lra. }
    iIntros (n) "[%Hn Herr]". unfold ε2 in *.
    destruct (decide (n = 0%nat)) as [Heq | Hne].
    - (* Branch 0: flip literal l1 (variable index i1). *)
      subst n.
      rewrite bool_decide_eq_true_2; [|done].
      wp_pures.
      assert (Hbi1 : (i1 < length bs)%nat) by lia.
      destruct (lookup_lt_is_Some_2 bs i1 Hbi1) as [v Hv].
      wp_apply (twp_bool_array_load with "Hba"); [exact Hv|].
      iIntros "Hba". wp_pures. rewrite /lang_negb. wp_pures.
      destruct v; wp_pures;
        wp_apply (twp_bool_array_store with "Hba"); try exact Hbi1;
        iIntros "Hba"; iApply "HΦ";
        iExists (flip_var bs i1);
        rewrite /flip_var (list_lookup_total_correct _ _ _ Hv) /=;
        iFrame; iSplit;
        [ iPureIntro; rewrite length_insert; lia
        | iLeft; by iFrame
        | iPureIntro; rewrite length_insert; lia
        | iLeft; by iFrame ].
    - (* Branch 1: flip literal l2 (variable index i2). *)
      assert (Hn1 : n = 1%nat) by lia. subst n.
      rewrite bool_decide_eq_false_2; [|done].
      wp_pures.
      assert (Hbi2 : (i2 < length bs)%nat) by lia.
      destruct (lookup_lt_is_Some_2 bs i2 Hbi2) as [v Hv].
      wp_apply (twp_bool_array_load with "Hba"); [exact Hv|].
      iIntros "Hba". wp_pures. rewrite /lang_negb. wp_pures.
      destruct v; wp_pures;
        wp_apply (twp_bool_array_store with "Hba"); try exact Hbi2;
        iIntros "Hba"; iApply "HΦ";
        iExists (flip_var bs i2);
        rewrite /flip_var (list_lookup_total_correct _ _ _ Hv) /=;
        iFrame; iSplit;
        [ iPureIntro; rewrite length_insert; lia
        | iRight; by iFrame
        | iPureIntro; rewrite length_insert; lia
        | iRight; by iFrame ].
  Qed.

  (** ** Derived flip specs phrased in terms of Hamming distance to a witness *)

  (** If the current assignment is already at maximum Hamming distance from
      [w] (i.e. every position disagrees), then *every* flip decreases the
      distance. No error credits are required. *)
  Lemma twp_flip_at_max a bs (c : clause) cv (nvars : nat) (w : list bool) :
    is_clause c cv ->
    clause_well_formed nvars c ->
    length bs = nvars ->
    length w = nvars ->
    hamming bs w = nvars ->
    [[{ bool_array a bs }]]
      flip_random_var #a cv
    [[{ RET #();
         ∃ bs',
           bool_array a bs' ∗
           ⌜length bs' = nvars⌝ ∗
           ⌜hamming bs' w = (hamming bs w - 1)%nat⌝ }]].
  Proof.
    iIntros (Hcl Hwf Hlen Hwlen Hh Φ) "Hba HΦ".
    iMod ec_zero as "Herr0".
    iAssert (↯ ((0 + 0) / 2)%R) with "[Herr0]" as "Herr".
    { iApply (ec_eq with "Herr0"). lra. }
    pose proof Hwf as Hwf'.
    destruct c as [[b1 i1] [b2 i2]].
    rewrite /clause_well_formed /lit_well_formed /lit_index /= in Hwf'.
    destruct Hwf' as [Hi1 Hi2].
    wp_apply (twp_flip_random_var _ _ _ _ _ 0%R 0%R with "[$Hba $Herr]");
      [exact Hcl | exact Hwf | exact Hlen | lra | lra |].
    iIntros "(%bs' & Hba & %Hlen' & Hdisj)".
    iApply "HΦ". iExists bs'. iFrame.
    iSplit; [iPureIntro; lia|].
    iDestruct "Hdisj" as "[[%Hbs1 _] | [%Hbs2 _]]"; subst bs'; cbn; iPureIntro.
    - apply hamming_flip_diff; [lia | lia |].
      apply (hamming_max_diff bs w i1); lia.
    - apply hamming_flip_diff; [lia | lia |].
      apply (hamming_max_diff bs w i2); lia.
  Qed.

  (** General derived spec: charge [↯ ((ε_down + ε_up)/2)] and get back
      either the "down" branch (Hamming decreased by 1, with [↯ ε_down])
      or the "up" branch (Hamming increased by 1, with [↯ ε_up]).

      Premises:
        - [c] is unsatisfied by [bs] (so flipping changes the value at
          [c]'s variables in a known way) and satisfied by [w] (so at
          least one of [c]'s variables disagrees between [bs] and [w]).
        - [ε_down <= ε_up], i.e., the "down" branch is at least as cheap
          as the "up" branch.  In Papadimitriou's analysis this holds
          because [err] is monotone in the Hamming distance, so
          [err (k-1) <= err (k+1)]. *)
  Lemma twp_flip_hamming a bs (c : clause) cv (nvars : nat) (w : list bool)
        (ε_down ε_up : R) :
    is_clause c cv ->
    clause_well_formed nvars c ->
    length bs = nvars ->
    length w = nvars ->
    eval_clause_pure bs c = false ->
    eval_clause_pure w c = true ->
    (0 <= ε_down)%R -> (0 <= ε_up)%R -> (ε_down <= ε_up)%R ->
    [[{ bool_array a bs ∗ ↯ ((ε_down + ε_up) / 2) }]]
      flip_random_var #a cv
    [[{ RET #();
         ∃ bs',
           bool_array a bs' ∗
           ⌜length bs' = nvars⌝ ∗
           ((⌜hamming bs' w = (hamming bs w - 1)%nat⌝ ∗ ↯ ε_down)
            ∨
            (⌜hamming bs' w = (hamming bs w + 1)%nat⌝ ∗ ↯ ε_up)) }]].
  Proof.
    iIntros (Hcl Hwf Hlen Hwlen Hunsat Hsat Hd0 Hu0 Hdu Φ) "[Hba Herr] HΦ".
    pose proof Hwf as Hwf'.
    destruct c as [[b1 i1] [b2 i2]].
    rewrite /clause_well_formed /lit_well_formed /lit_index /= in Hwf'.
    destruct Hwf' as [Hi1 Hi2].
    (* From [Hunsat] we get [bs !!! i_j = b_j]. *)
    simpl in Hunsat. apply orb_false_iff in Hunsat. destruct Hunsat as [Hu1 Hu2].
    assert (Hbs1 : bs !!! i1 = b1).
    { destruct b1; simpl in Hu1; [apply negb_false_iff|]; exact Hu1. }
    assert (Hbs2 : bs !!! i2 = b2).
    { destruct b2; simpl in Hu2; [apply negb_false_iff|]; exact Hu2. }
    (* Now case-split on which of [i1], [i2] disagrees between [bs] and [w]. *)
    destruct (decide (w !!! i1 = bs !!! i1)) as [Hi1a | Hi1d];
    destruct (decide (w !!! i2 = bs !!! i2)) as [Hi2a | Hi2d].
    - (* Both agree at i1 and i2: this makes [c] also unsatisfied in [w],
         contradicting [Hsat]. *)
      exfalso. simpl in Hsat.
      rewrite Hi1a Hi2a Hbs1 Hbs2 in Hsat.
      destruct b1, b2; simpl in Hsat; discriminate.
    - (* i1 agrees, i2 disagrees:
         outcome 0 (flip i1) -> up, outcome 1 (flip i2) -> down.
         Pass [ε_up] for outcome 0, [ε_down] for outcome 1.  Our budget
         [↯ ((ε_down + ε_up)/2)] equals [↯ ((ε_up + ε_down)/2)] up to
         commutativity. *)
      iAssert (↯ ((ε_up + ε_down) / 2)%R) with "[Herr]" as "Herr".
      { iApply (ec_eq with "Herr"). lra. }
      wp_apply (twp_flip_random_var _ _ _ _ _ ε_up ε_down with "[$Hba $Herr]");
        [exact Hcl | exact Hwf | exact Hlen | lra | lra |].
      iIntros "(%bs' & Hba & %Hlen' & Hdisj)".
      iApply "HΦ". iExists bs'. iFrame.
      iSplit; [done|].
      iDestruct "Hdisj" as "[[%Hbs' Herr] | [%Hbs' Herr]]"; subst bs'; cbn.
      + iRight. iFrame. iPureIntro.
        apply hamming_flip_same; [lia | lia | congruence].
      + iLeft. iFrame. iPureIntro.
        apply hamming_flip_diff; [lia | lia | congruence].
    - (* i1 disagrees, i2 agrees:
         outcome 0 (flip i1) -> down, outcome 1 (flip i2) -> up.
         Pass [ε_down] for outcome 0, [ε_up] for outcome 1.  Budget matches
         our [↯ ((ε_down + ε_up)/2)] directly. *)
      wp_apply (twp_flip_random_var _ _ _ _ _ ε_down ε_up with "[$Hba $Herr]");
        [exact Hcl | exact Hwf | exact Hlen | lra | lra |].
      iIntros "(%bs' & Hba & %Hlen' & Hdisj)".
      iApply "HΦ". iExists bs'. iFrame.
      iSplit; [done|].
      iDestruct "Hdisj" as "[[%Hbs' Herr] | [%Hbs' Herr]]"; subst bs'; cbn.
      + iLeft. iFrame. iPureIntro.
        apply hamming_flip_diff; [lia | lia | congruence].
      + iRight. iFrame. iPureIntro.
        apply hamming_flip_same; [lia | lia | congruence].
    - (* Both disagree: both outcomes go down.  Weaken our budget from
         [(ε_down + ε_up)/2] to [(ε_down + ε_down)/2 = ε_down] (this uses
         [ε_down <= ε_up]) and pass [ε_down] to both random outcomes. *)
      iAssert (↯ ((ε_down + ε_down) / 2)%R) with "[Herr]" as "Herr".
      { iApply (ec_weaken with "Herr"). split; lra. }
      wp_apply (twp_flip_random_var _ _ _ _ _ ε_down ε_down with "[$Hba $Herr]");
        [exact Hcl | exact Hwf | exact Hlen | lra | lra |].
      iIntros "(%bs' & Hba & %Hlen' & Hdisj)".
      iApply "HΦ". iExists bs'. iFrame.
      iSplit; [done|].
      iDestruct "Hdisj" as "[[%Hbs' Herr] | [%Hbs' Herr]]"; subst bs'; cbn;
        iLeft; iFrame; iPureIntro;
        apply hamming_flip_diff;
          [lia | lia | congruence | lia | lia | congruence].
  Qed.

  (** Combined random-flip step with the credit budget written directly in
      terms of [err].  Internally case-splits on whether [hamming bs w] has
      hit the upper boundary [nvars]; the caller sees just the recurrence
      [err nvars (S iter) k -> err nvars iter (hamming bs' w)]. *)
  Lemma twp_flip_step a bs (c : clause) cv
        (cls : list clause) (w : list bool) (nvars iter : nat) :
    In c cls ->
    formula_well_formed nvars cls ->
    satisfies w cls ->
    is_clause c cv ->
    eval_clause_pure bs c = false ->
    length bs = nvars ->
    length w = nvars ->
    [[{ bool_array a bs ∗ ↯ (err nvars (S iter) (hamming bs w)) }]]
      flip_random_var #a cv
    [[{ bs', RET #();
         bool_array a bs' ∗
         ⌜length bs' = nvars⌝ ∗
         ↯ (err nvars iter (hamming bs' w)) }]].
  Proof.
    iIntros (Hin Hwf Hsatw Hcv Hbad Hlen Hwlen Φ) "[Hba Herr] HΦ".
    destruct (unsat_clause_facts _ _ _ _ _ Hin Hwf Hsatw Hbad Hlen Hwlen)
      as (Hwfc & Hsat_c & Hh1).
    pose proof (hamming_le_nvars _ _ _ Hlen Hwlen) as Hh_le.
    destruct (decide (hamming bs w = nvars)) as [Heq | Hneq].
    - (* Boundary: flip is deterministic-down, no credit consumed. *)
      wp_apply (twp_flip_at_max _ _ _ _ _ w with "Hba"); [done..|].
      iIntros "(%bs' & Hba & %Hlen' & %Hh')".
      iApply ("HΦ" $! bs'); iFrame; iSplit; [done|].
      iApply (ec_eq with "Herr").
      rewrite Heq in Hh'. rewrite Hh' Heq. apply err_at_max; lia.
    - (* Interior: charge the credit as an average of the two neighbors. *)
      iAssert (↯ ((err nvars iter (hamming bs w - 1) +
                   err nvars iter (hamming bs w + 1)) / 2)%R)
        with "[Herr]" as "Herr".
      { iApply (ec_eq with "Herr"). apply err_step_interior; lia. }
      wp_apply (twp_flip_hamming _ _ _ _ _ w _ _ with "[$Hba $Herr]");
        try done; auto.
      iIntros "(%bs' & Hba & %Hlen' & Hdisj)".
      iApply ("HΦ" $! bs'); iFrame; iSplit; [done|].
      iDestruct "Hdisj" as "[[%Hh' Herr] | [%Hh' Herr]]"; rewrite Hh'; iFrame.
  Qed.

  (** From a list of vals where each is the encoding of some [bool],
      extract a [list bool] producing that encoding via [fmap]. *)
  Lemma bool_list_of_vals (vs : list val) :
    ([∗ list] _ ↦ v ∈ vs, ⌜∃ b : bool, v = #b⌝)%I -∗
    ⌜∃ bs : list bool, vs = (λ b : bool, #b) <$> bs⌝ : iProp Σ.
  Proof.
    iInduction vs as [|v vs] "IH".
    - iIntros "_". iPureIntro. by exists [].
    - rewrite big_sepL_cons.
      iIntros "[%Hv Hvs]".
      iDestruct ("IH" with "Hvs") as "%Hbs".
      iPureIntro.
      destruct Hv as [b ->].
      destruct Hbs as [bs ->].
      by exists (b :: bs).
  Qed.

  (** Allocate a length-[n] array of uniformly-random booleans, as used at
      the start of [papa_2sat]. *)
  Lemma twp_init_rand (n : nat) :
    (0 < n)%nat ->
    [[{ True }]]
      init_rand #n
    [[{ a bs, RET #a; bool_array a bs ∗ ⌜length bs = n⌝ }]].
  Proof.
    iIntros (Hn Φ) "_ HΦ".
    rewrite /init_rand.
    wp_pures.
    wp_apply (twp_array_init (λ _ v, ⌜∃ b : bool, v = #b⌝)%I _ (Z.of_nat n)).
    { lia. }
    { iApply big_sepL_intro. iModIntro. iIntros (k i) "_".
      wp_pures. wp_apply twp_rand_nat; auto.
      iIntros (m) "%Hm". wp_pures. iPureIntro. by eexists. }
    iIntros (a vs) "(%Hlen & Hba & Hvs)".
    iDestruct (bool_list_of_vals with "Hvs") as "%Hbs".
    destruct Hbs as [bs ->].
    iApply ("HΦ" $! a bs).
    rewrite /bool_array. iFrame.
    iPureIntro. rewrite length_fmap in Hlen. lia.
  Qed.

End helpers.
