(** * Fast Dice Roller (FDR) via urns / distributional invariants

    This file redoes the Fast Dice Roller case study inside the Elton program logic, 
    using urns instead of the fuel-indexed error-credit redistribution [fdr_f]/[fdr_h].

    The design follows the *distributional invariant* in 
    "Verifying Sampling Algorithms via Distributional Invariants" (Fig. 2):

        loop invariant:  c is uniformly distributed on {0, ..., v-1}.

    In Elton this is captured by an urn resource: at every loop head we own
    a delayed uniform value [c] with

        is_unif_urn c (Zrange v)   :=   "c is a delayed value uniform on {0,...,v-1}".
  *)

From clutch.elton Require Import elton.
Set Default Proof Using "Type*".

Definition fdr_loop' : val :=
  rec: "loop" "n" "v" "c" :=
    let: "v2" := #2 * "v" in
    let: "c2" := #2 * "c" + drand #1 in (* allocates a urn uniform on {0,1} *)
    if: "n" ≤ "v2"
    then (if: "c2" < "n" then "c2"
          else "loop" "n" ("v2" - "n") ("c2" - "n"))
    else "loop" "n" "v2" "c2".

(** We seed [c] with [drand #0] (a urn uniform on the singleton {0}), so that
    the uniform-urn invariant [is_unif_urn c (Zrange 1)] already holds on entry. *)
Definition fdr' : val :=
  λ: "n", fdr_loop' "n" #1 (drand #0).

Definition fdr_loop : val :=
  rec: "loop" "n" "v" "c" :=
    let: "v2" := #2 * "v" in
    let: "c2" := #2 * "c" + rand #1 in
    if: "n" ≤ "v2"
    then (if: "c2" < "n" then "c2"
          else "loop" "n" ("v2" - "n") ("c2" - "n"))
    else "loop" "n" "v2" "c2".

Definition fdr : val :=
  λ: "n", fdr_loop "n" #1 (rand #0).

Lemma fdr_remove_drand :
  remove_drand_expr fdr' = Some (Val fdr).
Proof. reflexivity. Qed.

(** The set {0, 1, ..., v-1} *)
Definition Zrange (v : nat) : gset Z := list_to_set (Z.of_nat <$> seq 0 v).

Definition avg (n : nat) (E : Z → R) : R :=
  (SeriesC (λ i : nat, if bool_decide (i < n)%nat then E (Z.of_nat i) else 0%R)) / n.

Lemma elem_of_Zrange z v :
  z ∈ Zrange v ↔ (0 ≤ z < Z.of_nat v)%Z.
Proof.
  rewrite /Zrange elem_of_list_to_set list_elem_of_fmap.
  setoid_rewrite elem_of_seq.
  split.
  - intros (k & -> & Hk). lia.
  - intros Hz. exists (Z.to_nat z). lia.
Qed.

Lemma Zrange_size v : size (Zrange v) = v.
Proof.
  rewrite /Zrange size_list_to_set.
  - by rewrite length_fmap length_seq.
  - apply NoDup_fmap; [intros ??; lia | apply NoDup_seq].
Qed.

Lemma Zrange_nonempty v : (0 < v)%nat → Zrange v ≠ ∅.
Proof.
  intros Hv He.
  assert (0%Z ∈ Zrange v) as Hin; last set_solver.
  apply elem_of_Zrange. lia.
Qed.

Lemma Zrange_diff_nonempty w n : (n < w)%nat → Zrange w ∖ Zrange n ≠ ∅.
Proof.
  intros Hlt He.
  assert (Z.of_nat n ∈ Zrange w ∖ Zrange n) as Hin; last set_solver.
  apply elem_of_difference. rewrite !elem_of_Zrange. lia.
Qed.

(** Shifting the reject window down by [n] gives an initial segment. *)
Lemma Zrange_diff_shift w n :
  (n ≤ w)%nat →
  set_map (λ z, z - Z.of_nat n)%Z (Zrange w ∖ Zrange n) = Zrange (w - n).
Proof.
  intros Hle. apply set_eq. intros z.
  rewrite elem_of_map.
  setoid_rewrite elem_of_difference.
  setoid_rewrite elem_of_Zrange.
  split.
  - intros (y & -> & Hy1 & Hy2). lia.
  - intros Hz. exists (z + Z.of_nat n)%Z. lia.
Qed.

Section fdr_spec.
  Context `{eltonGS Σ}.

  (** [is_unif_urn c s] : "the (possibly delayed) value [c] is uniformly
      distributed on the set [s]"

      Concretely: we own the urns that [c] reads (a finite urn heap
      [m] covering [val_support_set c]), and the pushforward of the urn
      distribution [urns_f_distr m] along the substitution [urn_subst_val · c]
      equals the uniform distribution on [s] (viewed as integer values [#z]).

      This is faithful to the *symbolic* delayed values produced by doubling
      ([2*c + coin], a [BinOp] over two urn labels): [c] need not be a bare
      label. *)
  Definition unif_val_distr (s : gset Z) : distr (option val) :=
    dmap (λ z : Z, Some #z) (unif_set s).

  Definition is_unif_urn (c : val) (s : gset Z) : iProp Σ :=
    ∃ m : gmap loc urn,
      ([∗ map] l ↦ u ∈ m, l ↪ u) ∗
      ⌜ val_support_set c ⊆ dom m ⌝ ∗
      ⌜ dmap (λ f, urn_subst_val f c) (urns_f_distr m) = unif_val_distr s ⌝.

  (** compute_distr of a uniform urn is the uniform-set distribution. *)
  Lemma compute_distr_unif (s : gset Z) :
    urns_f_distr_compute_distr (urn_unif s) = unif_set s.
  Proof.
    apply distr_ext. intros z.
    rewrite /urns_f_distr_compute_distr {1}/pmf /urns_f_distr_compute.
    rewrite /unif_set {1}/pmf. done.
  Qed.

  (** The urn distribution of a single fresh uniform urn. *)
  Lemma urns_f_distr_singleton (l : loc) (s : gset Z) :
    s ≠ ∅ →
    urns_f_distr {[l := urn_unif s]} = dmap (λ z : Z, {[l := z]}) (unif_set s).
  Proof.
    intros Hs.
    rewrite -insert_empty.
    rewrite urns_f_distr_insert; [| by rewrite lookup_empty | done].
    rewrite urns_f_distr_empty dret_id_left.
    rewrite compute_distr_unif.
    rewrite /dmap.
    apply dbind_ext_right. intros z.
    by rewrite insert_empty.
  Qed.

  (** A single owned uniform urn label is a uniform delayed value. *)
  Lemma is_unif_urn_intro_label (l : loc) (s : gset Z) :
    s ≠ ∅ →
    l ↪ urn_unif s -∗ is_unif_urn (#lbl:l) s.
  Proof.
    intros Hs. iIntros "Hl".
    iExists {[l := urn_unif s]}.
    rewrite big_sepM_singleton. iFrame "Hl".
    iPureIntro. split.
    - simpl. set_solver.
    - rewrite urns_f_distr_singleton //.
      rewrite /unif_val_distr /dmap.
      rewrite -dbind_assoc.
      apply dbind_ext_right. intros z.
      rewrite dret_id_left.
      f_equal. simpl. by rewrite lookup_singleton_eq.
  Qed.

  Lemma unif_urn_create (N : nat) E :
    {{{ True }}} drand #N @ E {{{ c, RET c; is_unif_urn c (Zrange (S N)) }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_apply (wp_drand_thunk N (Z.of_nat N) _ _ _ True with "[]").
    { rewrite rupd_unseal /rupd_def.
      iIntros (?) "$". iPureIntro. intros f Hf.
      eexists _. split; [done|]. done. }
    iIntros (l) "[_ Hl]".
    iApply "HΦ".
    iApply (is_unif_urn_intro_label l (Zrange (S N))).
    - rewrite /Zrange. apply non_empty_inhabited_L with (x := 0%Z).
      rewrite elem_of_list_to_set list_elem_of_fmap.
      setoid_rewrite elem_of_seq. exists 0%nat. lia.
    - rewrite /Zrange. iFrame "Hl".
  Qed.

  (** A uniform value on a nonempty set is an int-typed literal. *)
  Lemma is_unif_urn_shape c s :
    s ≠ ∅ →
    is_unif_urn c s -∗ ⌜∃ bl, c = LitV bl ∧ base_lit_type_check bl = Some BLTInt⌝.
  Proof.
    iIntros (Hs) "(%m & Hm & %Hsupp & %Hdistr)". iPureIntro.
    apply set_choose_L in Hs as [z0 Hz0].
    assert (dmap (λ f, urn_subst_val f c) (urns_f_distr m) (Some #z0) > 0)%R as Hpos.
    { rewrite Hdistr /unif_val_distr.
      apply dmap_pos. exists z0. split; [done|].
      apply unif_set_pos. split; [set_solver|done]. }
    apply dmap_pos in Hpos as (f & Hval & _).
    destruct c as [bl| | | |]; simpl in Hval.
    all: symmetry in Hval; rewrite bind_Some in Hval; destruct Hval as (x0 & Hx0 & Heq).
    { apply urn_subst_well_typed in Hx0 as (t & Ht1 & Ht2). simplify_eq. simpl in Ht2.
      eexists; split; [done|]. by simplify_eq. }
    { by simplify_eq. }
    { rewrite bind_Some in Heq. by destruct!/=. }
    { by simplify_eq. }
    { by simplify_eq. }
  Qed.

  (** Size of the image of an injective map. *)
  Lemma size_set_map_inj (s : gset Z) (g : Z → Z) :
    (∀ z1 z2, z1 ∈ s → z2 ∈ s → g z1 = g z2 → z1 = z2) →
    size (set_map g s : gset Z) = size s.
  Proof.
    intros Hinj.
    rewrite /set_map size_list_to_set.
    - by rewrite length_fmap length_elements_size_gset.
    - apply NoDup_fmap_2_strong; last apply NoDup_elements.
      intros x y Hx Hy. rewrite !elem_of_elements in Hx, Hy. by apply Hinj.
  Qed.

  (** Injective pushforward of a uniform-set distribution is uniform. *)
  Lemma dmap_unif_set_inj (s : gset Z) (g : Z → Z) :
    (∀ z1 z2, z1 ∈ s → z2 ∈ s → g z1 = g z2 → z1 = z2) →
    dmap g (unif_set s) = unif_set (set_map g s).
  Proof.
    intros Hinj.
    pose proof (size_set_map_inj s g Hinj) as Hsz.
    apply distr_ext. intros z'.
    destruct (decide (z' ∈ (set_map g s : gset Z))) as [Hin|Hout].
    - rewrite elem_of_map in Hin. destruct Hin as (z & -> & Hz).
      rewrite {1}/pmf/=/dbind_pmf.
      erewrite (SeriesC_ext _ (λ x, if bool_decide (x = z) then / size s else 0)); last first.
      { intros n. case_bool_decide as Hb.
        - subst n. rewrite unif_set_compute; last done.
          rewrite dret_1_1; last done. lra.
        - destruct (decide (g n = g z)) as [Hg|Hg].
          + rewrite Hg. rewrite dret_1_1; last done.
            destruct (decide (n ∈ s)) as [Hns|Hns].
            * exfalso. apply Hb. by apply Hinj.
            * rewrite unif_set_compute'; last done.
              rewrite Rmult_0_l. reflexivity.
          + rewrite dret_0; last naive_solver.
            rewrite Rmult_0_r. reflexivity. }
      rewrite SeriesC_singleton.
      rewrite unif_set_compute; last (apply elem_of_map; eauto).
      by rewrite Hsz.
    - rewrite {1}/pmf/=/dbind_pmf.
      rewrite unif_set_compute'; last done.
      apply SeriesC_0. intros n.
      destruct (decide (g n = z')) as [Hg|Hg].
      + destruct (decide (n ∈ s)) as [Hns|Hns].
        * exfalso. apply Hout. apply elem_of_map. eauto.
        * rewrite unif_set_compute'; last done.
          rewrite Rmult_0_l. reflexivity.
      + rewrite dret_0; last naive_solver.
        rewrite Rmult_0_r. reflexivity.
  Qed.

  (** Doubling a uniform-on-{0..v-1} value and adding a
      fresh fair delayed coin yields a uniform-on-{0..2v-1} value.

      if c ~ Unif{0..v-1} and b ~ Unif{0,1} are independent,
      then 2c + b ~ Unif{0..2v-1}  (the map (c,b) ↦ 2c+b is a bijection
      {0..v-1} × {0,1} → {0..2v-1}).
    *)
  Lemma unif_double_distr (v : nat) :
    (0 < v)%nat →
    dbind (λ a, dmap (λ b, (2*a+b)%Z) (unif_set (Zrange 2))) (unif_set (Zrange v))
      = unif_set (Zrange (2*v)).
  Proof.
    intros Hv.
    assert (∀ a : Z, size (set_map (λ b, (2*a+b)%Z) (Zrange 2) : gset Z) = 2%nat) as Hsz2.
    { intros a. rewrite size_set_map_inj; [apply Zrange_size | intros; lia]. }
    apply distr_ext. intros z.
    rewrite {1}/pmf/=/dbind_pmf.
    erewrite (SeriesC_ext _
      (λ a, if bool_decide (a = z `div` 2)%Z
            then (if bool_decide (z ∈ Zrange (2*v)) then / size (Zrange (2*v)) else 0%R)
            else 0%R)); last first.
    { intros a.
      rewrite (dmap_unif_set_inj _ _); last (intros; lia).
      case_bool_decide as Hb.
      - subst a.
        case_bool_decide as Hz.
        + (* z in range: both factors positive *)
          apply elem_of_Zrange in Hz.
          rewrite unif_set_compute; last first.
          { apply elem_of_Zrange. split; [apply Z.div_pos; lia|].
            apply Z.div_lt_upper_bound; lia. }
          rewrite unif_set_compute; last first.
          { apply elem_of_map. exists (z `mod` 2)%Z.
            split; last (apply elem_of_Zrange; split;
                          [apply Z.mod_pos; lia | apply Z.mod_pos_bound; lia]).
            rewrite {1}(Z.div_mod z 2); lia. }
          rewrite Hsz2 !Zrange_size.
          replace (2 * v)%nat with (v * 2)%nat by lia.
          rewrite mult_INR Rinv_mult /=. lra.
        + (* z out of range: the first factor vanishes *)
          rewrite (unif_set_compute' (Zrange v)); first (rewrite Rmult_0_l; done).
          rewrite elem_of_Zrange. intros [? ?].
          apply Hz, elem_of_Zrange.
          pose proof (Z.mod_pos_bound z 2 ltac:(lia)).
          pose proof (Z.div_mod z 2 ltac:(lia)). lia.
      - (* a is not z's block: the second factor vanishes *)
        rewrite (unif_set_compute' (set_map _ _)); first (rewrite Rmult_0_r; done).
        rewrite elem_of_map. intros (b & -> & Hb2).
        apply elem_of_Zrange in Hb2.
        apply Hb.
        replace (2*a+b)%Z with (a*2+b)%Z by lia.
        rewrite Z.div_add_l; last lia.
        rewrite Z.div_small; lia. }
    rewrite SeriesC_singleton_dependent.
    rewrite /unif_set/pmf. done.
  Qed.

  Lemma unif_urn_double (v : nat) (c : val) E :
    (0 < v)%nat →
    {{{ is_unif_urn c (Zrange v) }}}
      (#2 * c + drand #1)%E @ E
    {{{ c', RET c'; is_unif_urn c' (Zrange (2 * v)) }}}.
  Proof.
    iIntros (Hv Φ) "Hurn HΦ".
    iDestruct (is_unif_urn_shape with "Hurn") as %(bl & -> & Htc);
      first by apply Zrange_nonempty.
    iDestruct "Hurn" as "(%m & Hm & %Hsub & %Hdistr)".
    (* the symbolic (or concrete) doubled literal *)
    assert (∃ blM, bin_op_eval MultOp #2 (LitV bl) = Some (LitV blM)
              ∧ base_lit_support_set blM ⊆ base_lit_support_set bl
              ∧ base_lit_type_check blM = Some BLTInt
              ∧ (∀ f i, urn_subst f bl = Some i →
                   urn_subst f blM
                     = match i with LitInt a => Some (LitInt (2*a)) | _ => None end))
      as (blM & HevM & HsuppM & HtcM & HpointM).
    { assert (bin_op_eval MultOp #2 (LitV bl)
                = Some (LitV (MultOp' (LitInt 2) bl))
              ∨ (∃ a : Z, bl = LitInt a ∧
                   bin_op_eval MultOp #2 (LitV bl) = Some (LitV (LitInt (2*a)))))
        as [HevM | (a & -> & HevM)].
      { rewrite /bin_op_eval/bin_op_eval_bl Htc /=.
        destruct bl; try (by left). right. eexists. by split. }
      - exists (MultOp' (LitInt 2) bl).
        split_and!; [done | simpl; set_solver | by rewrite /= Htc |].
        intros f i Hi. simpl. rewrite Hi. by destruct i.
      - exists (LitInt (2*a)).
        split_and!; [done | set_solver | done |].
        intros f i Hi. by simplify_eq/=. }
    (* sample the fresh fair coin *)
    wp_apply (wp_drand_thunk _ 1 _ _ _ True%I).
    { rewrite rupd_unseal/rupd_def. iIntros (?) "$". iPureIntro. naive_solver. }
    iIntros (lb) "[_ Hlb]".
    iAssert (lb ↪ urn_unif (Zrange 2))%I with "[Hlb]" as "Hlb"; first iExact "Hlb".
    (* the coin label is fresh for [c]'s urns *)
    iAssert (⌜m !! lb = None⌝)%I as %Hfresh.
    { destruct (m !! lb) as [u|] eqn:Hlb; last done.
      iDestruct (big_sepM_lookup with "Hm") as "Hlb'"; first done.
      iDestruct (ghost_map_elem_ne with "Hlb' Hlb") as %Hne.
      exfalso. by apply Hne. }
    (* the symbolic sum *)
    assert (bin_op_eval PlusOp (LitV blM) #lbl:lb
              = Some (LitV (PlusOp' blM (LitLbl lb)))) as HevP.
    { rewrite /bin_op_eval/bin_op_eval_bl HtcM /=. by destruct blM. }
    do 2 wp_pure.
    iModIntro. iApply "HΦ".
    (* support facts about the urn assignments of [c] *)
    assert (∀ f, (urns_f_distr m f > 0)%R →
              ∃ a : Z, a ∈ Zrange v ∧ urn_subst_val f (LitV bl) = Some #a) as Hpoint.
    { intros f Hf.
      assert ((dmap (λ f, urn_subst_val f (LitV bl)) (urns_f_distr m)
                 (urn_subst_val f (LitV bl)) > 0)%R) as Hpos.
      { apply dmap_pos. eauto. }
      rewrite Hdistr /unif_val_distr in Hpos.
      apply dmap_pos in Hpos as (a & Heq & Ha).
      apply unif_set_pos in Ha as [? ?]. eauto. }
    assert (∀ f, (urns_f_distr m f > 0)%R → f !! lb = None) as Hflb.
    { intros f Hf. apply urns_f_distr_pos in Hf.
      specialize (Hf lb). rewrite Hfresh in Hf. by case_match. }
    (* the joint evaluation of the symbolic sum *)
    assert (∀ f (a b : Z), urn_subst_val f (LitV bl) = Some #a → f !! lb = None →
              urn_subst_val (<[lb:=b]> f) (LitV (PlusOp' blM (LitLbl lb)))
                = Some #(2*a+b)) as Hval.
    { intros f a b Hf Hlb'. simpl in Hf |- *.
      destruct (urn_subst f bl) as [i|] eqn:Hi; simplify_eq/=.
      assert (urn_subst (<[lb:=b]> f) bl = Some (LitInt a)) as Hi'.
      { eapply urn_subst_subset; [|done]. by apply insert_subseteq. }
      pose proof (HpointM _ _ Hi') as HM.
      rewrite HM /= lookup_insert_eq /=. done. }
    (* assemble the resource *)
    iExists (<[lb := urn_unif (Zrange 2)]> m).
    rewrite big_sepM_insert; last done.
    iFrame "Hlb Hm".
    iPureIntro. split.
    { simpl. rewrite dom_insert. simpl in Hsub. set_solver. }
    rewrite urns_f_distr_insert;
      [| by rewrite Hfresh | simpl; apply Zrange_nonempty; lia].
    rewrite compute_distr_unif.
    rewrite /dmap.
    rewrite -dbind_assoc'.
    trans (dbind
             (λ f, match urn_subst_val f (LitV bl) with
                   | Some (LitV (LitInt a)) =>
                       dbind (λ b, dret (Some #(2*a+b))) (unif_set (Zrange 2))
                   | _ => dzero
                   end) (urns_f_distr m)).
    { apply dbind_ext_right_strong. intros f Hf.
      rewrite -dbind_assoc'.
      destruct (Hpoint f Hf) as (a & Ha & Hfa).
      rewrite Hfa.
      apply dbind_ext_right. intros b.
      rewrite dret_id_left. cbn beta.
      by rewrite (Hval f a b) // (Hflb f Hf). }
    (* pull the pushforward equation through *)
    trans (dbind
             (λ ov, match ov with
                    | Some (LitV (LitInt a)) =>
                        dbind (λ b, dret (Some #(2*a+b))) (unif_set (Zrange 2))
                    | _ => dzero
                    end) (dmap (λ f, urn_subst_val f (LitV bl)) (urns_f_distr m))).
    { rewrite /dmap -dbind_assoc'.
      apply dbind_ext_right. intros f. by rewrite dret_id_left. }
    rewrite Hdistr /unif_val_distr /dmap -dbind_assoc'.
    (* conclude with the pure doubling lemma *)
    rewrite -(unif_double_distr v Hv).
    rewrite /dmap -dbind_assoc'.
    apply dbind_ext_right. intros a.
    rewrite dret_id_left.
    rewrite -dbind_assoc'.
    apply dbind_ext_right. intros b.
    by rewrite dret_id_left.
  Qed.

  (** Injective integer pushforward on the [option val] wrapper. *)
  Definition int_map (g : Z → Z) (ov : option val) : option val :=
    match ov with
    | Some (LitV (LitInt a)) => Some (LitV (LitInt (g a)))
    | _ => None
    end.

  (** Generic pushforward principle: if [c'] denotes (pointwise, under every
      urn assignment) the image of [c] under an injective integer map [g],
      then uniformity of [c] on [s] transports to uniformity of [c'] on
      [set_map g s], reusing the same owned urns. *)
  Lemma is_unif_urn_pushforward (c c' : val) (g : Z → Z) (s : gset Z) :
    (∀ z1 z2, z1 ∈ s → z2 ∈ s → g z1 = g z2 → z1 = z2) →
    val_support_set c' ⊆ val_support_set c →
    (∀ f, urn_subst_val f c' = int_map g (urn_subst_val f c)) →
    is_unif_urn c s -∗ is_unif_urn c' (set_map g s).
  Proof.
    iIntros (Hinj Hsupp Hpoint) "(%m & Hm & %Hsub & %Hdistr)".
    iExists m. iFrame "Hm". iPureIntro. split; first set_solver.
    trans (dmap (int_map g) (dmap (λ f, urn_subst_val f c) (urns_f_distr m))).
    { rewrite dmap_comp. rewrite /dmap.
      apply dbind_ext_right. intros f. by rewrite /compose Hpoint. }
    rewrite Hdistr /unif_val_distr.
    rewrite dmap_comp.
    rewrite -(dmap_unif_set_inj _ _ Hinj).
    rewrite dmap_comp.
    rewrite /dmap. apply dbind_ext_right. intros ?. done.
  Qed.

  (** On the reject branch we have learned that the
      sample lies in {n,..,w-1} (i.e. [c] is uniform on [Zrange w ∖ Zrange n]);
      subtracting [n] yields a value uniform on {0,..,(w-n)-1}.

      Distributionally: the injective map x ↦ x - n sends Unif{n..w-1} to
      Unif{0..w-n-1}.  The one-urn special case of the combination in (2).

      Note the subtraction happens symbolically: [bin_op_eval] combines the
      delayed literal with [#n] into [MinusOp' bl n] without resolving urns. *)
  Lemma unif_urn_shift (w n : nat) (c : val) E :
    (n < w)%nat →
    {{{ is_unif_urn c (Zrange w ∖ Zrange n) }}}
      (c - #n)%E @ E
    {{{ c', RET c'; is_unif_urn c' (Zrange (w - n)) }}}.
  Proof.
    iIntros (Hlt Φ) "Hurn HΦ".
    iDestruct (is_unif_urn_shape with "Hurn") as %(bl & -> & Htc);
      first by apply Zrange_diff_nonempty.
    (* the symbolic (or concrete) result of the subtraction *)
    assert (bin_op_eval MinusOp (LitV bl) #n
              = Some (LitV (MinusOp' bl (LitInt n)))
            ∨ (∃ a : Z, bl = LitInt a ∧
                 bin_op_eval MinusOp (LitV bl) #n = Some (LitV (LitInt (a - n)))))
      as Hcase.
    { rewrite /bin_op_eval/bin_op_eval_bl Htc /=.
      destruct bl; try (by left). right. eexists. by split. }
    rewrite -(Zrange_diff_shift w n); last lia.
    destruct Hcase as [Hev | (a & -> & Hev)].
    - (* symbolic result *)
      wp_pure.
      iModIntro. iApply "HΦ".
      iApply (is_unif_urn_pushforward with "Hurn").
      + intros. lia.
      + simpl. set_solver.
      + intros f. simpl.
        destruct (urn_subst f bl) as [i|] eqn:Hf; simpl; last done.
        destruct i; simpl; done.
    - (* concrete result *)
      wp_pure.
      iModIntro. iApply "HΦ".
      iApply (is_unif_urn_pushforward with "Hurn").
      + intros. lia.
      + simpl. set_solver.
      + intros f. simpl. done.
  Qed.

  (** (4) SPLIT (the accept/reject test): the missing urn-mixing rule.

      Given [↯ (avg n E)] and [c] uniform on {0..w-1} with [n ≤ w], the test
      [if: c < #n then e1 else e2] resolves the accept/reject partition:

        - ACCEPT ([c] lands in {0,..,n-1}): [c] promotes to a concrete [z < n]
          and we keep exactly [↯ (E z)] for the caller;

        - REJECT ([c] lands in {n,..,w-1}): [c] is now uniform on
          [Zrange w ∖ Zrange n] (so in particular [n < w]) and we recover the
          full [↯ (avg n E)].

      The credit re-balances *exactly*: with the allocation
          ε2 x = E x       for x < n      (accept: pay the caller)
          ε2 x = avg n E   for n ≤ x < w  (reject: keep enough to continue)
      we get (1/w) Σ_{x<w} ε2 x
           = (1/w) ( Σ_{i<n} E i + (w-n)·avg n E )
           = (1/w) ( n·avg n E + (w-n)·avg n E ) = avg n E.

      This rule is sound for a semantics with joint/correlated urns, 
      but it is not derivable in the current Elton model:

      1. The physical urn heap [gmap loc urn] can only represent product
         distributions — each label an independent uniform urn.  After [k]
         doubling steps, [c] is a symbolic value over [k] labels, and its
         reject-conditioned joint distribution {f | eval f ∈ [n,w)} is not a
         product: any box (product of sub-urns of {0,1}-coins) has size a
         power of two, while the reject branch needs the pushforward image to
         be uniform on [w-n] values — impossible whenever [w-n] is not a power
         of two (the doubling map is injective on boxes, so the image size
         equals the box size).

      2. [If] on a delayed boolean only steps when the guard is
         [urn_subst_equal] to a definite [true]/[false] under every urn
         assignment in the support (see the head step for [If] in [lang.v]) —
         so the proof must resolve urns at the test, and by (1) the
         post-resolution state cannot carry the reject invariant.

      3. The resolve rules ([pupd_resolve_urn] et al.) shrink a single urn,
         and value promotion ([wp_value_promotion]) can only promote to urn-free 
         values; neither can re-box a symbolic multi-label value into a fresh single urn.

      This is exactly the "urn mixing" extension listed as future work in the
      Elton paper: an extended model where several labels may share one joint
      urn (with labels as projections) validates this rule — the reject
      outcome keeps a joint urn uniform on {f | eval f ∈ [n,w)}, whose
      pushforward along [c] is uniform on [Zrange w ∖ Zrange n] as required.
      The two continuations are combined with [∧] (not [∗]) since exactly one
      branch runs. *)
  Definition unif_urn_split : Prop :=
    ∀ (w n : nat) (c : val) (E : Z → R) (e1 e2 : expr) Φ,
    (0 < n)%nat → (n ≤ w)%nat → (∀ z, 0 <= E z)%R →
    ⊢ ↯ (avg n E) -∗
      is_unif_urn c (Zrange w) -∗
      ( (∀ z : Z, ⌜(0 ≤ z < Z.of_nat n)%Z⌝ -∗ ↯ (E z) -∗
            rupd (λ x, x = #z) True%I c -∗ WP e1 {{ Φ }})
        ∧ (⌜(n < w)%nat⌝ -∗ ↯ (avg n E) -∗
            is_unif_urn c (Zrange w ∖ Zrange n) -∗ WP e2 {{ Φ }}) ) -∗
      WP (if: c < #n then e1 else e2)%E {{ Φ }}.

  Context (unif_urn_split_ctxt : unif_urn_split).

  Lemma fdr_loop_spec (n : nat) (E : Z → R) (v : nat) (c : val) :
    (0 < n)%nat → (0 < v)%nat → (∀ z, 0 <= E z)%R →
    {{{ ↯ (avg n E) ∗ is_unif_urn c (Zrange v) }}}
      fdr_loop' #n #v c
    {{{ (z : Z), RET #z; ⌜(0 ≤ z < Z.of_nat n)%Z⌝ ∗ ↯ (E z) }}}.
  Proof.
    iIntros (Hn Hv HE Φ) "(Herr & Hurn) HΦ".
    iLöb as "IH" forall (v c Φ Hv) "Herr Hurn HΦ".
    rewrite {2}/fdr_loop'.
    wp_pures.
    (* c2 := 2*c + coin : uniform on {0..2v-1} *)
    wp_apply (unif_urn_double with "Hurn"); first done.
    iIntros (c') "Hurn".
    wp_pures.
    case_bool_decide as Hcmp.
    - (* n ≤ 2v : run the accept/reject test *)
      assert ((n ≤ 2*v)%nat) as Hle by lia.
      wp_pures.
      iApply (unif_urn_split_ctxt (2*v) n c' E _ _ _ Hn Hle HE with "Herr Hurn").
      iSplit.
      + (* accept: promote c' to the concrete result *)
        iIntros (z Hz) "Herr Hrupd".
        iApply (wp_value_promotion with "Hrupd").
        iIntros "_".
        wp_pures.
        iApply "HΦ". by iFrame.
      + (* reject: shift down by n and re-establish the invariant *)
        iIntros (Hlt) "Herr Hurn".
        wp_apply (unif_urn_shift (2*v) n with "Hurn"); first done.
        iIntros (c'') "Hurn".
        wp_pure.
        replace (2 * Z.of_nat v - Z.of_nat n)%Z
          with (Z.of_nat (2 * v - n)%nat) by lia.
        iApply ("IH" $! (2*v-n)%nat c'' Φ with "[] Herr Hurn HΦ").
        iPureIntro. lia.
    - (* 2v < n : keep doubling *)
      wp_pure (If _ _ _).
      replace (2 * Z.of_nat v)%Z with (Z.of_nat (2 * v)%nat) by lia.
      iApply ("IH" $! (2*v)%nat c' Φ with "[] Herr Hurn HΦ").
      iPureIntro. lia.
  Qed.

  Lemma fdr_spec (n : nat) (E : Z → R) (ε : R) :
    (0 < n)%nat →
    (∀ z, 0 <= E z)%R →
    (avg n E <= ε)%R →
    {{{ ↯ ε }}}
      fdr' #n
    {{{ (z : Z), RET #z; ⌜(0 ≤ z < Z.of_nat n)%Z⌝ ∗ ↯ (E z) }}}.
  Proof.
    iIntros (Hn HE Hle Φ) "Herr HΦ".
    rewrite /fdr'. wp_pures.
    wp_apply (unif_urn_create 0 with "[//]").
    iIntros (c) "Hurn".
    wp_apply (fdr_loop_spec n E 1 c with "[Herr Hurn]"); [done|lia|done| |done].
    iFrame "Hurn".
    iApply (ec_weaken with "Herr").
    split; last done.
    rewrite /avg.
    apply Rcomplements.Rdiv_le_0_compat.
    - apply SeriesC_ge_0'. intros i. case_bool_decide; [apply HE|lra].
    - apply lt_0_INR. lia.
  Qed.

End fdr_spec.

Section adequacy.
  Context (Hrule : ∀ Σ (H : eltonGS Σ), unif_urn_split).

  (** The uniform expectation of the indicator of a single target [m < n]
      is exactly [1/n]. *)
  Local Lemma avg_indicator (n : nat) (m : Z) :
    (0 < n)%nat → (0 ≤ m < Z.of_nat n)%Z →
    avg n (λ z, if bool_decide (z = m) then 1%R else 0%R) = (1 / n)%R.
  Proof using Hrule.
    intros Hn Hm.
    rewrite /avg.
    rewrite (SeriesC_ext _
      (λ i : nat, if bool_decide (i = Z.to_nat m) then 1%R else 0%R));
      last first.
    { intros i. cbn beta. repeat case_bool_decide; try lra; exfalso; lia. }
    rewrite SeriesC_singleton. done.
  Qed.

  (* The ideal bound is phrased using total eris, but we just talk about the following:
     `fdr` will land in each of {0, ..., n - 1} with probability at most 1/n. *)
  Lemma fdr_correct (n : nat) (m : Z) :
    (0 < n)%nat → (0 ≤ m < Z.of_nat n)%Z →
    pgl (lim_exec (fdr #n, {| heap := ∅; urns := ∅ |}))
        (λ v, v ≠ #m) (1 / n).
  Proof using Hrule.
    intros Hn Hm.
    eapply (elton_adequacy_remove_drand eltonΣ (fdr' #n)).
    - reflexivity.
    - apply Rcomplements.Rdiv_le_0_compat; [lra | apply lt_0_INR; lia].
    - iIntros (H0 Φ) "!> Herr HΦ".
      assert (∀ z, 0 <= (if bool_decide (z = m) then 1%R else 0%R))%R as HE.
      { intros z. case_bool_decide; lra. }
      assert (avg n (λ z, if bool_decide (z = m) then 1%R else 0%R) <= 1 / n)%R
        as Havg.
      { rewrite avg_indicator //. }
      wp_apply (fdr_spec (Hrule _ _) n _ (1/n) Hn HE Havg with "Herr").
      iIntros (z) "[%Hz Herr]".
      destruct (decide (z = m)) as [->|Hne].
      + rewrite bool_decide_eq_true_2; last done.
        iDestruct (ec_contradict with "Herr") as %[]. lra.
      + iApply "HΦ". iPureIntro.
        split; first done.
        intros Heq. apply Hne. by simplify_eq.
  Qed.

End adequacy.
