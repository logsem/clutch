(** Report-noisy-max with ONE-SIDED EXPONENTIAL noise: the noise-specific
    argmax-coupling and tape-state-step lemmas, the exp analogue of
    [report_noisy_max_lemmas].  The pure argmax lemmas ([list_Z_max],
    [pw_list_Z_max_correct], [dZ_bounded_cases], [ineq_convert], …) are
    noise-independent and REUSED by importing [report_noisy_max_lemmas].

    The ONLY mathematical difference from the Laplace development is the
    per-coordinate draw coupling [exp_map_pw]: the costly +1 shift at the argmax
    coordinate uses the one-sided [Mcoupl_exp] (k=1, k'=2) whose directionality
    [0 ≤ 1+hd-hd'] is satisfied exactly because [dZ hd hd' ≤ 1] (so hd-hd'≥-1);
    the 0-cost coordinates use [Mcoupl_exp_isometry] / [Mcoupl_exp_rat_isometry]
    (same shape as Laplace). *)
From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics iris_ext.
From clutch.prob Require Import differential_privacy distribution exponential couplings couplings_app couplings_dp.
From clutch.gen_diffpriv Require Import adequacy all.
From clutch.gen_diffpriv.lib Require Import exponential exponential_tapes.
From clutch.gen_prob_lang Require Import erasure gwp.list inject families.
From clutch.gen_prob_lang.spec Require Import spec_ra spec_rules.
From clutch.gen_diffpriv.examples Require Import report_noisy_max_lemmas.
From iris.prelude Require Import options.

(** NB: NO global [Open Scope R] here (matching [report_noisy_max_lemmas]); the
    argmax relations use nat [>]/[=] and reals are written with explicit [%R],
    so a global R-scope would mis-parse [length zs > 0] as [Rgt]. *)

(** The rational-ε exponential isometry (0-cost exact center shift), the exp
    analogue of [Mcoupl_laplace_rat_isometry]; both [exp_rat] branches (positive
    ε via [Mcoupl_exp_isometry], degenerate ε via the [dret] diagonal). *)
Fact Mcoupl_exp_rat_isometry (num den loc loc' : Z) :
  Mcoupl (exp_rat num den loc) (exp_rat num den loc') (λ z z', z - z' = loc - loc')%Z 0.
Proof.
  rewrite /exp_rat. case_decide as H.
  - apply (Mcoupl_exp_isometry (mkposreal _ H) loc loc').
  - apply Mcoupl_dret; [done | lia].
Qed.

(** The shared [inv_distr] (in distribution.v) carries a dedicated [laplace_rat]
    support clause but, being defined before [exponential.v], none for [exp_rat].
    This mirror adds the [exp_rat] case (unfold + [decide]-split, exactly as the
    [laplace_rat] clause) and otherwise defers to the generic [inv_distr].

    IMPORTANT: [inv_distr] is defined in [distribution.v] under [#[local] Open
    Scope R], so all its [_ > 0] match patterns parse as [Rgt].  This file has NO
    global [Open Scope R] (see header note), so every [> 0] below MUST carry an
    explicit [%R]; otherwise the patterns parse as [nat]/[Z] [>] and silently fail
    to match the real-valued support hypotheses, leaving e.g. the [dret]-draw
    hypothesis (and hence the bound state [σ']) unsubstituted. *)
Ltac inv_distr_exp :=
  repeat
    match goal with
    | H : (dzero.(pmf) _ > 0)%R |- _ => exfalso; by eapply dzero_supp_empty
    | H : ((dret _).(pmf) _ > 0)%R |- _ => apply dret_pos in H; simplify_eq
    | H : ((dbind _ _).(pmf) _ > 0)%R |- _ => apply dbind_pos in H as (?&?&?)
    | H : ((dmap _ _).(pmf) _ > 0)%R |- _ => apply dmap_pos in H as (?&?&?); simplify_eq
    | H : ((d_proj_Some _).(pmf) _ > 0)%R |- _ => apply d_proj_Some_pos in H
    | H : (((exp_rat ?num ?den _).(pmf) _) > 0)%R |- _
      => rewrite /exp_rat in H ;
         destruct (decide (0 < IZR num / IZR den)%R) ; [|inv_distr_exp]
    end.

(** exp_map *)
Fixpoint exp_map num den (Hproof:(0<IZR num / IZR den)%R) (l:list Z) :=
  match l with
  | [] => dret []
  | loc::l' =>
      dbind (λ z,
               dbind (λ zs, dret (z::zs)) (exp_map num den Hproof l')
        ) (exp_rat num den loc)
  end.

Lemma exp_map_pos num den Hproof l zs:
  (exp_map num den Hproof l zs > 0)%R ->
  length zs = length l.
Proof.
  revert zs.
  induction l as [|?? IHl]; intros zs; simpl; intros H; inv_distr; first done.
  all: erewrite <-IHl; done.
Qed.

Lemma exp_map_mass num den Hproof l :
  (SeriesC (exp_map num den Hproof l) =1)%R.
Proof.
  induction l as [|? ? IHl]; first (simpl; solve_distr_mass).
  simpl.
  setoid_rewrite dbind_mass.
  erewrite SeriesC_ext; last first.
  { intros. rewrite dbind_mass.
    erewrite SeriesC_ext; last first.
    - intros. rewrite dret_mass.
      by rewrite Rmult_1_r.
    - rewrite IHl. by rewrite Rmult_1_r.
  }
  (* [solve_distr_mass] (shared, in distribution.v) has no [exp_rat] clause; the
     remaining head-draw mass is [exp_rat_mass]. *)
  rewrite exp_rat_mass //.
Qed.

Lemma exp_map_pw_after num den l l' (Hproof: (0 < IZR num / IZR (2 * den))%R):
  length l = length l' ->
  (∀ p, p ∈ zip_with (λ x y, (x,y)) l l' -> (dZ p.1 p.2 <= 1)%R) ->
  DPcoupl (exp_map num (2*den) (Hproof) l)
    (exp_map num (2*den) (Hproof) l')
    (λ zs zs',
       length zs = length zs' /\
       (∀ p, p ∈ zip_with (λ x y, (x,y)) zs zs' -> (dZ p.1 p.2 <= 1)%R) 
    ) 0 0.
Proof.
  revert l'.
  induction l as [|hd tl IHl].
  - intros []; last done.
    simpl.
    intros.
    apply DPcoupl_dret; naive_solver.
  - intros [|hd' tl']; first done.
    simpl.
    intros H1 H2.
    replace 0%R with (0+0)%R by lra.
    unshelve epose proof H2 (hd, hd') _ as H3.
    { rewrite elem_of_cons; naive_solver. }
    apply dZ_bounded_cases in H3 as H4.
    eapply (DPcoupl_dbind _ _ _ _ (λ z z', (dZ z z' <= 1)%R)); try done; last first.
    { eapply DPcoupl_mono; [done|done|..]; last apply Mcoupl_to_DPcoupl; last apply Mcoupl_exp_rat_isometry; try done.
      intros.
      apply dZ_bounded_cases'. simpl in *. lia.
    }
    intros z z' Hz.
    replace 0%R with (0+0)%R by lra.
    eapply DPcoupl_dbind; last apply IHl; try done; last first.
    + intros. apply H2. rewrite elem_of_cons; naive_solver.
    + by simplify_eq.
    + simpl.
      intros ??[H5 H6].
      apply DPcoupl_dret; try done.
      split; first (simpl; lia).
      simpl.
      intros [].
      rewrite elem_of_cons.
      intros [|]; simplify_eq; naive_solver.
Qed.


Lemma exp_map_pw num den l l' (Hproof: (0 < IZR num / IZR (2 * den))%R) j:
  length l = length l' ->
  (length l > 0)%nat ->
  (j<length l)%nat->
  (∀ p, p ∈ zip_with (λ x y, (x,y)) l l' -> (dZ p.1 p.2 <= 1)%R) ->
  DPcoupl (exp_map num (2*den) (Hproof) l)
    (exp_map num (2*den) (Hproof) l')
    (λ zs zs',
       length zs > 0 /\
       length zs = length zs' /\
       (∀ p, p ∈ zip_with (λ x y, (x,y)) zs zs' -> (dZ p.1 p.2 <= 1)%R) /\
       ∃ (z: Z),
         zs!!j=Some z /\ zs' !!j = Some (z+1)%Z
    ) (IZR num / IZR den) 0.
Proof.
  revert l l'.
  induction j as [|? Hj].
  - replace 0%R with (0+0)%R by lra.
    replace (_/_)%R with (IZR num / IZR den + 0)%R by lra.
    intros [|hd tl] [|hd' tl']; simpl; try lia.
    intros H1 H2 H3 H4.
    simplify_eq.
    eapply (DPcoupl_dbind _ _ _ _ (λ z z', z+1=z')%Z); try done; last first.
    { rewrite /exp_rat. case_decide as Hd ; [|done].
      (* the +1 shift at the argmax coordinate: one-sided [Mcoupl_exp] with k=1,
         k'=2.  Directionality [0 ≤ 1+hd-hd'] AND bound [1+hd-hd' ≤ 2] both follow
         from [dZ hd hd' ≤ 1] (i.e. [-1 ≤ hd-hd' ≤ 1]); the cost [IZR 2 · ε] with
         ε = num/(2·den) is EXACTLY num/den. *)
      unshelve epose proof H4 (hd, hd') _ as H5.
      { rewrite elem_of_cons; naive_solver. }
      apply dZ_bounded_cases in H5. simpl in H5.
      eapply DPcoupl_mono; [done|done|..]; last apply Mcoupl_to_DPcoupl;
        last eapply (Mcoupl_exp (mkposreal _ Hd) hd hd' 1 2); try done.
      - (* cost: IZR 2 * (num/(2*den)) ≤ num/den (equality) *)
        simpl. rewrite mult_IZR.
        replace (_/(_*_))%R with (/2 * (IZR num / IZR den))%R; last (rewrite Rdiv_mult_distr; lra).
        rewrite -Rmult_assoc.
        rewrite -{2}(Rmult_1_l (_/_)%R).
        apply Rmult_le_compat_r; [left; by apply ineq_convert | lra].
      - (* directionality 0 ≤ 1 + hd - hd' *) lia.
      - (* bound 1 + hd - hd' ≤ 2 *) lia.
    }
    intros ?? <-.
    replace 0%R with (0+0)%R by lra.
    eapply DPcoupl_dbind; last apply exp_map_pw_after; try done; last first.
    { intros. apply H4. rewrite elem_of_cons; naive_solver. }
    simpl.
    intros ??[].
    apply DPcoupl_dret; try done.
    repeat split; simpl; try lia; last naive_solver.
    intros [].
    rewrite elem_of_cons.
    intros []; simplify_eq; last naive_solver.
    apply dZ_bounded_cases'. simpl. lia.
  - intros [|hd tl] [|hd' tl']; simpl; try lia.
    intros H1 H2 H3 H4.
    simplify_eq.
    replace 0%R with (0+0)%R by lra.
    replace (_/_)%R with (0+IZR num / IZR den)%R by lra.
    eapply (DPcoupl_dbind _ _ _ _ (λ z z', (dZ z z' <= 1)%R)); try done; last first.
    { rewrite /exp_rat. case_decide ; [|done].
      eapply DPcoupl_mono; [done|done|..]; last apply Mcoupl_to_DPcoupl; last eapply (Mcoupl_exp_isometry); try done.
      simpl.
      intros ?? ->.
      unshelve epose proof H4 (_,_) _ as H5; last apply H5.
      rewrite elem_of_cons. naive_solver.
    }
    intros ???.
    replace 0%R with (0+0)%R by lra.
    replace (_/_)%R with (IZR num / IZR den+0)%R by lra.
    eapply DPcoupl_dbind; last apply Hj; try done; try lia; last first. 
    + intros. apply H4. rewrite elem_of_cons; naive_solver.
    + simpl.
      intros. destruct!/=.
      apply DPcoupl_dret; try done; simpl.
      repeat split; try lia.
      * intros []. rewrite elem_of_cons. intros. destruct!/=; naive_solver.
      * naive_solver.
Qed.

Lemma exp_map_correct' num den l l' (Hproof: (0 < IZR num / IZR (2 * den))%R):
  length l = length l' ->
  (length l > 0)%nat ->
  (∀ p, p ∈ zip_with (λ x y, (x,y)) l l' -> (dZ p.1 p.2 <= 1)%R) ->
  DPcoupl (exp_map num (2*den) (Hproof) l)
    (exp_map num (2*den) (Hproof) l')
    (λ zs zs', list_Z_max zs = list_Z_max zs'
    ) (IZR num / IZR den) 0.
Proof.
  intros Ha Hb Hc.
  replace 0%R with (SeriesC (λ (x:nat), 0)); last by apply SeriesC_0.
  apply DPcoupl_pweq'.
  - pose proof (ineq_convert _ _ Hproof) as K. lra.
  - done.
  - apply ex_seriesC_0.
  - intros j.
    destruct (decide (j<length l)); last first.
    {
      eapply DPcoupl_mono; last eapply DPcoupl_pos_R; last eapply DPcoupl_trivial; try done.
      - simpl. intros ? ? [? [?%exp_map_pos ?]].
        intros. subst.
        unshelve epose proof list_Z_max_bound x _; lia.
      - left. by apply ineq_convert.
      - apply exp_map_mass.
      - apply exp_map_mass.
    }
    eapply DPcoupl_mono; last eapply DPcoupl_pos_R; last eapply exp_map_pw; try done.
    simpl.
    intros ?? [H [Hlen%exp_map_pos Hlen'%exp_map_pos]]?.
    destruct!/=. eapply pw_list_Z_max_correct; naive_solver.
Qed. 

Lemma exp_map_correct num den l l' (Hproof: (0 < IZR num / IZR (2 * den))%R):
  length l = length l' ->
  (length l > 0)%nat ->
  (∀ p, p ∈ zip_with (λ x y, (x,y)) l l' -> (dZ p.1 p.2 <= 1)%R) ->
  DPcoupl (exp_map num (2*den) (Hproof) l)
    (exp_map num (2*den) (Hproof) l')
    (λ zs zs', length zs = length zs' /\ (length zs = length l)%nat /\
               list_Z_max zs = list_Z_max zs'
    ) (IZR num / IZR den) 0.
Proof.
  intros.
  eapply DPcoupl_mono; last (eapply DPcoupl_pos_R; eapply exp_map_correct'); try done.
  intros ??[?[?%exp_map_pos ?%exp_map_pos]]. lia.
Qed.

Section rnme_lemmas.
  Context {S : Sig} `{!SampleIn exp_family S} `{!diffprivGS S Σ}.
  Canonical Structure gen_ectxi_lang_rnme := gen_ectxi_lang S.
  Canonical Structure gen_ectx_lang_rnme := gen_ectx_lang S.
  Canonical Structure gen_lang_rnme := gen_lang S.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang S)).
  Local Notation lidx := (@sample_idx exp_family S _).
  (* the generic tape value standing in for [prob_lang]'s [Tape_Laplace] record *)
  Local Notation ExpT num den mean zs :=
    (sample_idx (D := exp_family), sf_param_to_val exp_family (num, den, mean)%Z,
      ((λ z : Z, LitV (LitInt z)) <$> zs)).

  (** Laplace-specific unfold of the generic [state_step]: a Laplace tape steps
      by a [exp_rat] draw (appending its injection to the tape).  This
      reduces the generic [match sig_sample …] (via [sig_sample_at]) and composes
      the two [dmap]s — the gen analogue of [prob_lang]'s [state_step_exp_unfold]. *)
  Lemma state_step_exp_unfold σ α num den mean zs :
    stapes σ !! α = Some (ExpT num den mean zs) →
    state_step S σ α =
      dmap (λ z : Z, state_upd_stapes (<[α := ExpT num den mean (zs ++ [z])]>) σ)
        (exp_rat num den mean).
  Proof.
    intros Hlook.
    erewrite state_step_unfold; last exact Hlook.
    rewrite (sig_sample_at exp_family S (num, den, mean)).
    rewrite dmap_comp.
    apply dmap_eq; [|done]. intros z _.
    rewrite /compose fmap_app /=. done.
  Qed.

Fixpoint exp_presample_list σ ls:=
  match ls with
  | [] => dret σ
  | hd :: tl => dbind (λ σ', exp_presample_list σ' tl) (state_step S σ hd)
  end.

Fixpoint replace_exp_tape num den σ ls :=
  match ls with
  | [] => σ
  | hd::tl =>
      let '(ι, mean, ls, z) :=hd in
        state_upd_stapes <[ι := ExpT num den mean (ls++[z])]> (replace_exp_tape num den σ tl)
  end.

Lemma exp_presample_list_rewrite_notin l tl x σ num den :
  l ∉ tl.*1.*1.*1 ->
  replace_exp_tape num den (state_upd_stapes <[l:=x]> σ)
    tl =
  state_upd_stapes <[l:=x]>
    (replace_exp_tape num den σ tl).
Proof.
  induction tl; first naive_solver.
  rewrite !fmap_cons.
  destruct a as [[[]]].
  rewrite elem_of_cons.
  intros Hcontra.
  simpl.
  rewrite IHtl; last naive_solver.
  simpl.
  f_equal.
  rewrite insert_insert_ne; first done.
  naive_solver.
Qed. 

Lemma exp_presample_list_rewrite num den l σ (Hproof: (0 < IZR num / IZR (2*den))%R):
  Forall (λ '(ι, loc, lis), stapes σ!!ι = Some (ExpT num (2*den) loc lis)) l ->
  NoDup (l.*1.*1) ->
  exp_presample_list σ ((l.*1).*1) =
  dbind (λ zs,
           dret (replace_exp_tape num (2*den) σ (zip l zs))
    ) (exp_map num (2*den) (Hproof) (l.*1.*2))
.
Proof.
  revert σ.
  induction l as [|hd tl IHl].
  { simpl. intros. by rewrite dret_id_left. }
  intros σ Hforall Hnodup.
  destruct hd as [[]].
  rewrite !fmap_cons.
  rewrite /exp_presample_list.
  etrans.
  { simpl.
    rewrite Forall_cons in Hforall.
    erewrite state_step_exp_unfold; last naive_solver.
    rewrite /dmap.
    eapply dbind_ext_right_strong.
    intros σ' Hpos.
    apply dbind_pos in Hpos.
    destruct!/=.
    inv_distr_exp; last naive_solver.
    erewrite IHl; last first.
    - apply NoDup_cons in Hnodup. naive_solver.
    - apply NoDup_cons in Hnodup as [Hnodup _]. revert H2 Hnodup.
      clear.
      induction tl as [|[[]] ? IHtl]; first by rewrite !Forall_nil.
      rewrite !Forall_cons.
      intros. destruct!/=.
      split.
      + rewrite lookup_insert_ne; first done.
        rewrite elem_of_cons in Hnodup. naive_solver.
      + apply IHtl; first done.
        rewrite elem_of_cons in Hnodup.
        naive_solver.
    - rewrite dmap_fold.
      instantiate (1:=λ x, dmap
                        (λ a0 : list Z,
                           replace_exp_tape num (2*den)
                             x
                             (zip tl a0))
                        (exp_map num (2*den) Hproof tl.*1.*2)).
      done.
  }
  rewrite /exp_map.
  rewrite -/exp_map.
  rewrite -!dbind_assoc'.
  apply dbind_ext_right.
  intros z'.
  rewrite /dmap.
  rewrite dret_id_left.
  rewrite -dbind_assoc'.
  apply dbind_ext_right_strong.
  intros ? Hpos.
  apply exp_map_pos in Hpos.
  rewrite dret_id_left.
  simpl. f_equal.
  rewrite exp_presample_list_rewrite_notin; first done.
  rewrite !length_fmap in Hpos.
  rewrite fst_zip; last lia.
  simpl in Hnodup.
  apply NoDup_cons in Hnodup.
  naive_solver.
Qed. 

(* ls a list of tape loc content*)

Lemma replace_exp_tape_zip ls zs num den σ:
  length ls = length zs ->
  NoDup (ls.*1.*1) ->
  Forall
    (λ '(ι, loc, lis, z),
       stapes (replace_exp_tape num (2 * den) σ (zip ls zs)) !! ι =
       Some (ExpT num (2 * den) loc (lis ++ [z])))
    (zip ls zs).
Proof.
  revert zs σ.
  induction ls as [|[[]]? IHl].
  { simpl. intros. by apply Forall_nil. }
  intros [|z']?; first (simpl; lia).
  rewrite !fmap_cons.
  intros H1 H2.
  simpl in H1, H2.
  simplify_eq.
  apply NoDup_cons in H2.
  rewrite /zip-/zip.
  apply Forall_cons.
  split.
  - simpl.
    by rewrite lookup_insert_eq.
  - epose proof IHl _ (state_upd_stapes <[_:=_]> σ) _ _ as H.
    eapply Forall_impl; first done.
    intros [[[]]].
    rewrite exp_presample_list_rewrite_notin; first done.
    rewrite fst_zip; first naive_solver.
    lia.
    Unshelve.
    + lia.
    + naive_solver.
Qed. 

Lemma exp_state_list_coupl num den ls ls' σ σ':
  (0 < IZR num / IZR (2 * den))%R -> 
  length ls = length ls' ->
  (length ls > 0)%nat ->
  (∀ p, p ∈ zip_with (λ x y, (x.1.2,y.1.2)) ls ls' -> (dZ p.1 p.2 <= 1)%R) ->
  (NoDup ls.*1.*1) ->
  (NoDup ls'.*1.*1) ->
  Forall (λ '(ι, loc, lis), stapes σ!!ι = Some (ExpT num (2*den) loc lis)) ls ->
  Forall (λ '(ι, loc, lis), stapes σ'!!ι = Some (ExpT num (2*den) loc lis)) ls' ->
  DPcoupl (exp_presample_list σ ls.*1.*1)
    (exp_presample_list σ' ls'.*1.*1)
    (λ σf σf',
       ∃ zs zs', length zs = length zs' /\ (length zs = length ls)%nat /\
                 list_Z_max zs = list_Z_max zs' /\
                 σf = (replace_exp_tape num (2 * den) σ (zip ls zs)) /\ 
                 σf' = (replace_exp_tape num (2 * den) σ' (zip ls' zs'))(*  /\  *)
                 (* Forall (λ '(ι, loc, lis, z), stapes σf!!ι = Some (ExpT num (2*den) loc (lis ++ [z]))) (zip ls zs) /\ *)
                 (* Forall (λ '(ι, loc, lis, z), stapes σf'!!ι = Some (ExpT num (2*den) loc (lis ++ [z]))) (zip ls' zs') *)
    ) (IZR num / IZR den) 0.
Proof.
  intros H1 H2 H3 H4 H5 H6 H7 H8.
  unshelve (repeat erewrite exp_presample_list_rewrite); last first; try done.
  replace (0)%R with (0+0)%R by lra.
  replace (_/_)%R with (IZR num / IZR den + 0)%R by lra.
  eapply DPcoupl_dbind; [done|done| |apply exp_map_correct]; last first.
  - repeat setoid_rewrite zip_with_fmap_l.
    repeat setoid_rewrite zip_with_fmap_r. naive_solver.
  - rewrite !length_fmap. lia.
  - rewrite !length_fmap. lia.
  - simpl.
    rewrite !length_fmap.
    intros zs zs' (?&?&?).
    apply DPcoupl_dret; try done.
    exists zs, zs'.
    repeat split; lia. 
Qed. 

Lemma exp_presample_list_erasable num den σ ls (Hineq:(0 < IZR num / IZR (2 * den))%R):
  NoDup ls.*1.*1->
  Forall (λ '(ι, loc, lis), stapes σ!!ι = Some (ExpT num (2*den) loc lis)) ls ->
  erasable (Λ := gen_lang S) (exp_presample_list σ ls.*1.*1) σ.
Proof.
  revert σ.
  induction ls as [|[[]] tl IHls]; intros ? Hnodup H; first apply dret_erasable.
  simpl.
  apply erasable_dbind.
  - eapply state_step_erasable.
    rewrite Forall_cons in H. naive_solver.
  - intros ? Hpos. apply IHls.
    { rewrite !fmap_cons in Hnodup.
      rewrite NoDup_cons in Hnodup.
      naive_solver.
    }
    rewrite Forall_cons in H.
    destruct!/=.
    rewrite (state_step_exp_unfold _ _ _ _ _ _ H0) in Hpos.
    simpl in *.
    inv_distr_exp; last lra.
    simpl.
    clear -H1 Hnodup.
    apply NoDup_cons in Hnodup as [Hnodup _].
    revert H1 Hnodup.
    induction tl.
    + intros. by apply Forall_nil.
    + rewrite Forall_cons.
      intros. destruct!/=.
      rewrite Forall_cons; split.
      * rewrite lookup_insert_ne; first done.
        rewrite elem_of_cons in Hnodup. naive_solver.
      * apply IHtl; first done.
        rewrite elem_of_cons in Hnodup. naive_solver.
Qed.

Lemma replace_exp_tape_heap num den h l ls:
  (heap (replace_exp_tape num (2 * den)
                              {| heap := h; stapes := l |} ls) = h).
Proof.
  revert h l.
  induction ls; first naive_solver.
  intros. simpl.
  repeat case_match; subst.
  simpl.
  naive_solver.
Qed.

Section coupling_rule.

  Lemma hoare_couple_exp_list_update xιs xιs' zs zs' ls ls' σ σ' num den:
    length xιs = length xιs' -> 
    NoDup xιs.*2 -> NoDup xιs'.*2 ->
    length zs = length xιs ->
    length zs' = length xιs ->
    ls = zip (zip xιs.*2 xιs.*1) (replicate (length xιs) []) ->
    ls' =zip (zip xιs'.*2 xιs'.*1) (replicate (length xιs) []) ->
    stapes_auth 1 (stapes σ) -∗
    spec_tapes_auth (stapes σ') -∗
    ([∗ list] '(x, ι);'(x', ι') ∈ xιs;xιs', ι ↪E (num,2 * den,x; []) ∗
            ι' ↪Eₛ (num,2 * den,x'; []) ∗ ⌜(Rabs (IZR (x - x')) <= 1)%R⌝)
    ==∗
    (stapes_auth 1 (stapes (replace_exp_tape num (2 * den) σ (zip ls zs)))) ∗
     spec_tapes_auth (stapes (replace_exp_tape num (2 * den) σ' (zip ls' zs'))) ∗
    ([∗ list] k↦'(x, ι);'(x', ι') ∈ xιs;xιs', ι ↪E (num,2 * den,x; [
                                                    zs !!! k]) ∗ ι' ↪Eₛ (num,2 * den,x'; [zs' !!! k]) ∗ ⌜(Rabs (IZR (x - x')) <= 1)%R⌝).
  Proof.
    revert xιs' zs zs' ls ls' σ σ'.
    induction xιs as [|hd xιs IH].
    {
      intros []; last (simpl; lia).
      intros []; last (simpl; lia).
      intros []; last (simpl; lia).
      simpl.
      intros.
      subst. simpl.
      iIntros.
      by iFrame.
    }
    simpl.
    intros [|? xιs']; first (simpl; lia).
    intros [|? zs]; first (simpl; lia).
    intros [|? zs']; first (simpl; lia).
    simpl.
    intros ls ls' σ σ'.
    intros H1 H2 H3 H4 H5 -> ->.
    rewrite !NoDup_cons in H2, H3.
    iIntros "H1 H2 H3".
    case_match. case_match; subst.
    iDestruct "H3" as "(H3 & H4)".
    iMod (IH xιs' zs zs' _ _ σ σ' with "[$][$][$]") as "H".
    - lia.
    - naive_solver.
    - naive_solver.
    - lia.
    - lia.
    - done.
    - done.
    - iDestruct ("H3") as "(H1&H2&%)".
      iDestruct "H" as "(H3&H4&H5)".
      simpl.
      iMod (ghost_map_update with "H3 H1") as "[$ $]".
      iMod (ghost_map_update with "H4 H2") as "[$ $]".
      iModIntro.
      iSplit; first done.
      iFrame.
  Qed. 
  
  Lemma hoare_couple_exp_list num den xιs xιs' N e Φ:
    (0 < IZR num / IZR (2 * den))%R ->
    length xιs = N ->
    length xιs = length xιs' ->
    (length xιs > 0)%nat ->
    NoDup xιs.*2 -> NoDup xιs'.*2 ->
           ↯m (IZR num / IZR den) -∗
           ([∗ list] '(x, ι);'(x', ι') ∈ xιs;xιs', ι ↪E (num, 2 * den,x; []) ∗ ι' ↪Eₛ (num,2 * den,x'; []) ∗ ⌜(dZ x x' <= 1)%R⌝) -∗
             ((∃ zs zs', ([∗ list] k ↦ '(x, ι);'(x', ι') ∈ xιs;xιs',
                            ι ↪E (num, 2 * den,x; [zs !!! k]) ∗
                            ι' ↪Eₛ (num,2 * den,x'; [zs' !!! k]) ∗
                            ⌜(dZ x x' <= 1)%R⌝) ∗
                         ⌜length zs = N⌝ ∗
                         ⌜length zs' = N⌝ ∗
                         ⌜list_Z_max zs = list_Z_max zs'⌝)
              -∗
              WP e {{ v, Φ v }})
             -∗
               WP e {{ v, Φ v }}.
  Proof.
    iIntros (Hineq Hlen1 Hlen2 Hlen3 Hnodup1 Hnodup2) "Herr Hlist HΦ".
    iApply wp_lift_step_spec_couple.
    iIntros (σ e' σ' ε δ) "((Hh1 & Htl1) & Hauth2 & Hε2 & Hδ2)".
    iDestruct "Hauth2" as "(HK&Hh2&Htl2)/=".
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ecm_supply_ecm_inv with "Hε2 Herr") as %(ε'' & ε_now_rest & foo & Hε'').
    set (ls := zip (zip xιs.*2 xιs.*1) (replicate N ([]:list Z))).
    set (ls' := zip (zip xιs'.*2 xιs'.*1) (replicate N ([]:list Z))).
    iAssert (⌜Forall (λ '(ι, loc, lis), stapes σ!!ι = Some (ExpT num (2*den) loc lis)) ls⌝)%I as "%".
    { rewrite List.Forall_forall.
      iIntros ([[??]?]).
      rewrite -list_elem_of_In.
      rewrite /ls.
      rewrite list_elem_of_lookup.
      iIntros ([k Hsome]).
      rewrite big_sepL2_alt.
      iDestruct "Hlist" as "[_ Hlist]".
      repeat rewrite lookup_zip_Some in Hsome.
      assert (is_Some (zip (zip xιs'.*2 xιs'.*1) (replicate N ([]:list Z)) !! k)).
      { eapply lookup_lt_is_Some_2.
        rewrite !length_zip !length_fmap length_replicate.
        destruct Hsome as [Hsome1 Hsome2].
        apply lookup_replicate in Hsome2.
        lia.
      }
      destruct H as [[[]] H].
      repeat rewrite lookup_zip_Some in H.
      destruct Hsome as [[H1 H2] H3].
      destruct H as [[H4 H5] H6].
      rewrite !list_lookup_fmap in H1, H2, H4, H5.
      rewrite !lookup_replicate in H3, H6. 
      simpl in *.
      destruct!/=.
      destruct (xιs!!k) as [[]|] eqn:K1; try done.
      destruct (xιs'!!k) as [[]|] eqn:K2; try done.
      simpl in *.
      simplify_eq.
      iAssert (⌜_∈zip xιs xιs'⌝)%I as "%H".
      { iPureIntro. eapply list_elem_of_lookup_2.
        erewrite lookup_zip_Some. naive_solver.
      }
      iDestruct (big_sepL_elem_of with "[$]") as "H"; first done.
      simpl.
      iDestruct "H" as "[H ?]".
      by iDestruct (ghost_map_lookup with "Htl1 H") as "%".
    }
    iAssert (⌜Forall (λ '(ι, loc, lis), stapes σ'!!ι = Some (ExpT num (2*den) loc lis)) ls'⌝)%I as "%".
    { rewrite List.Forall_forall.
      iIntros ([[??]?]).
      rewrite -list_elem_of_In.
      rewrite /ls.
      rewrite list_elem_of_lookup.
      iIntros ([k Hsome]).
      rewrite big_sepL2_alt.
      iDestruct "Hlist" as "[_ Hlist]".
      repeat rewrite lookup_zip_Some in Hsome.
      assert (is_Some (zip (zip xιs.*2 xιs.*1) (replicate N ([]:list Z)) !! k)) as H'.
      { eapply lookup_lt_is_Some_2.
        rewrite !length_zip !length_fmap length_replicate.
        destruct Hsome as [Hsome1 Hsome2].
        apply lookup_replicate in Hsome2.
        lia.
      }
      destruct H' as [[[]] H'].
      repeat rewrite lookup_zip_Some in H'.
      destruct Hsome as [[H1 H2] H3].
      destruct H' as [[H4 H5] H6].
      rewrite !list_lookup_fmap in H1, H2, H4, H5.
      rewrite !lookup_replicate in H3, H6. 
      simpl in *.
      destruct!/=.
      destruct (xιs!!k) as [[]|] eqn:K1; try done.
      destruct (xιs'!!k) as [[]|] eqn:K2; try done.
      simpl in *.
      simplify_eq.
      iAssert (⌜_∈zip xιs xιs'⌝%I) as "%H'".
      { iPureIntro. eapply list_elem_of_lookup_2.
        erewrite lookup_zip_Some. naive_solver.
      }
      iDestruct (big_sepL_elem_of with "[$]") as "H"; first done.
      simpl.
      iDestruct "H" as "[? [H ?]]".
      by iDestruct (ghost_map_lookup with "Htl2 H") as "%".
    }
    iAssert (⌜(∀ p, p ∈ zip_with (λ x y, (x.1.2,y.1.2)) ls ls' -> (dZ p.1 p.2 <= 1)%R)⌝)%I as "%".
    {
      iIntros ([z z'] H').
      rewrite elem_of_lookup_zip_with in H'.
      destruct H' as (k&[[]]&[[]]&?&K1 &K2); destruct!/=.
      rewrite big_sepL2_alt.
      rewrite /ls/ls' in K1, K2.
      repeat rewrite lookup_zip_Some in K1, K2.
      rewrite !list_lookup_fmap !lookup_replicate in K1, K2.
      destruct (xιs!!k) as [[]|] eqn:?; last naive_solver.
      destruct (xιs'!!k) as [[]|] eqn:?; last naive_solver.
      destruct!/=.
      iDestruct "Hlist" as "[_ Hlist]".
      iAssert (⌜_∈zip xιs xιs'⌝)%I as "%H'".
      { iPureIntro. eapply list_elem_of_lookup_2.
        erewrite lookup_zip_Some. naive_solver.
      }
      iDestruct (big_sepL_elem_of with "[$]") as "H"; first done.
      simpl.
      by iDestruct "H" as "(?&?&%)".
    }
    iApply (spec_coupl_erasables_weak _ _ _ ε'' ε_now_rest _ 0%NNR δ) => //.
    - apply nnreal_ext. simpl. lra.
    - rewrite Hε''.
      apply exp_state_list_coupl; [| | |done|..]; try done.
      + unfold ls. unfold ls'.
        rewrite !length_zip!length_replicate!length_fmap. lia.
      + unfold ls.
        rewrite !length_zip!length_replicate!length_fmap. lia.
      + unfold ls.
        rewrite fst_zip; last first.
        { rewrite !length_zip!length_replicate!length_fmap. lia. }
        rewrite fst_zip; first done.
        rewrite !length_fmap. lia.
      + unfold ls'.
        rewrite fst_zip; last first.
        { rewrite !length_zip!length_replicate!length_fmap. lia. }
        rewrite fst_zip; first done.
        rewrite !length_fmap. lia.
    - eapply exp_presample_list_erasable; try done.
      unfold ls.
      rewrite !fst_zip; first done.
      + rewrite !length_fmap. lia.
      + rewrite !length_zip!length_replicate!length_fmap. lia.
    - eapply exp_presample_list_erasable; try done.
      unfold ls.
      rewrite !fst_zip; first done.
      + rewrite !length_fmap. lia.
      + rewrite !length_zip!length_replicate!length_fmap. lia.
    - simpl.
      iIntros (σ2 σ2') "(%zs & %zs' &%Hlen4 &%Hlen5&%Hmax&%Hforall1&%Hforall2)".
      iMod (ecm_supply_decrease with "Hε2 Herr") as (????) "H".
      iApply spec_coupl_ret.
      iModIntro.
      subst.
      rewrite /spec_auth/=.
      simpl.
      unfold ls in *.
      rewrite !length_zip !length_fmap !length_replicate in Hlen5.
      destruct σ, σ'.
      rewrite !replace_exp_tape_heap.
      iFrame. 
      iMod (hoare_couple_exp_list_update _ _ zs zs' with "[$][$][$]") as "Hrest"; try done; try lia.
      iDestruct "Hrest" as "(?&?&?)".
      iFrame.
      iMod "Hclose'".
      iModIntro.
      iSplitL "H".
      + iApply ecm_supply_eq; last done. simplify_eq. lra.
      + iApply "HΦ".
        iFrame.
        repeat iSplit; iPureIntro; lia.
  Qed. 
  
End coupling_rule.

End rnme_lemmas.

