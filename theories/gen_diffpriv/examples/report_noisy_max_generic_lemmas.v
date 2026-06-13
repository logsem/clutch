(** Report-noisy-max, NOISE-GENERIC library.  This file factors the ~700 lines of
    argmax + presample/replace-tape machinery shared between the Laplace
    ([report_noisy_max_lemmas]) and one-sided exponential
    ([report_noisy_max_exp_lemmas]) report-noisy-max developments into ONE
    library parametric over the noise distribution [sample : Z → Z → Z → distr Z].

    The development PIVOTS on a single named [Prop],
    [noise_map_correct_statement sample] (the per-distribution argmax-coupling
    fact: the [noise_map]ped lists couple, preserving [list_Z_max], at cost
    [num/den]).  The whole tape layer ([Section tape]) consumes it as a HYPOTHESIS
    [Hmc], so a future NON-per-coordinate noise (e.g. exponential mechanism /
    Gumbel) can discharge [Hmc] its own way.

    The per-coordinate path ([Section draw]) builds [Hmc] from ONE directional
    general-shift draw coupling [Hdraw] (the shape of [DPcoupl_laplace_draw] /
    [DPcoupl_exp_draw]); the constructor is [noise_map_correct_of_draw].  This
    [Hdraw] is the SOLE noise-specific input on that path: the 0-cost location
    isometry and the costly +1 argmax shift are BOTH recovered from it (at
    [k:=loc'-loc, k':=0] and at the doubled rate with [k:=1, k':=2]).

    The noise distribution is presented to the language as [mkZNoise sample mass],
    whose projections reduce DEFINITIONALLY ([sf_out = Z], [sf_inj = LitV ∘ LitInt],
    the standard [(num,den,mean) ↔ PairV] encoding, [sf_sample (n,d,m) = sample n d m]).
    That is exactly what lets the tape notations / [state_step_noise_unfold] /
    [sig_sample_at] go through with NO [sf_out = Z] transport.

    The pure argmax lemmas ([list_Z_max], [pw_list_Z_max_correct],
    [dZ_bounded_cases], [ineq_convert], [list_max_index_eq], …) are
    noise-independent and REUSED by importing [report_noisy_max_lemmas]. *)
From discprob.basic Require Import seq_ext.
From stdpp Require Import list.
From clutch.prelude Require Import tactics.
From clutch.gen_prob_lang Require Import erasure gwp.list znoise.
From clutch.prob Require Import couplings_dp couplings differential_privacy distribution.
From clutch.gen_diffpriv Require Import all.
From clutch.gen_diffpriv.lib Require Import laplace laplace_tapes.
From clutch.gen_diffpriv.examples Require Import report_noisy_max_pure.

(** Unlike [report_noisy_max_lemmas] (whose imported [Set Default Proof Using
    "Type"] leaks in as a global flag), this development genuinely depends on the
    section variables [sample]/[mass]/[Hdraw]/[Hmc], so we let every proof
    generalise over all in-scope section variables. *)
Set Default Proof Using "All".

(** NB: NO global [Open Scope R] here (matching [report_noisy_max_lemmas]); the
    argmax relations use nat [>]/[=] and reals are written with explicit [%R]. *)

(** The shared [inv_distr] (in distribution.v) carries a dedicated [laplace_rat]
    support clause, but none for the abstract [sample] (which we cannot
    case-split on).  This mirror behaves exactly like [inv_distr] but, when it
    meets a [sample]-positivity hypothesis, simply [clear]s it (the
    [noise_map_pos]/erasable bookkeeping never inspects the head draw, only the
    [dbind]/[dret] structure around it).

    IMPORTANT: [inv_distr] is defined in [distribution.v] under [#[local] Open
    Scope R], so all its [_ > 0] match patterns parse as [Rgt].  This file has NO
    global [Open Scope R], so every [> 0] below MUST carry an explicit [%R]. *)
Ltac inv_distr_gen sample :=
  repeat
    match goal with
    | H : (dzero.(pmf) _ > 0)%R |- _ => exfalso; by eapply dzero_supp_empty
    | H : ((dret _).(pmf) _ > 0)%R |- _ => apply dret_pos in H; simplify_eq
    | H : ((dbind _ _).(pmf) _ > 0)%R |- _ => apply dbind_pos in H as (?&?&?)
    | H : ((dmap _ _).(pmf) _ > 0)%R |- _ => apply dmap_pos in H as (?&?&?); simplify_eq
    | H : ((d_proj_Some _).(pmf) _ > 0)%R |- _ => apply d_proj_Some_pos in H
    | H : ((sample _ _ _).(pmf) _ > 0)%R |- _ => clear H
    end.

Section generic.
  Context (sample : Z → Z → Z → distr Z)
          (mass : ∀ num den mean, (SeriesC (sample num den mean) = 1)%R).
  Local Notation D := (mkZNoise sample mass).

(** noise_map *)
Fixpoint noise_map num den (Hproof:(0<IZR num / IZR den)%R) (l:list Z) :=
  match l with
  | [] => dret []
  | loc::l' =>
      dbind (λ z,
               dbind (λ zs, dret (z::zs)) (noise_map num den Hproof l')
        ) (sample num den loc)
  end.

Lemma noise_map_pos num den Hproof l zs:
  (noise_map num den Hproof l zs > 0)%R ->
  length zs = length l.
Proof.
  revert zs.
  induction l as [|?? IHl]; intros zs; simpl; intros H; inv_distr_gen sample; first done.
  all: erewrite <-IHl; done.
Qed.

Lemma noise_map_mass num den Hproof l :
  (SeriesC (noise_map num den Hproof l) =1)%R.
Proof.
  induction l as [|? ? IHl]; first (simpl; rewrite dret_mass //).
  simpl.
  setoid_rewrite dbind_mass.
  erewrite SeriesC_ext; last first.
  { intros. rewrite dbind_mass.
    erewrite SeriesC_ext; last first.
    - intros. rewrite dret_mass.
      by rewrite Rmult_1_r.
    - rewrite IHl. by rewrite Rmult_1_r.
  }
  rewrite mass //.
Qed.

(** The PIVOT, as a named [Prop].  This is the per-distribution argmax-coupling
    fact that the whole tape layer below consumes as a HYPOTHESIS.  Stated over
    the section [sample], so on section-close it becomes a predicate on
    [sample : Z → Z → Z → distr Z] (see [noise_map_correct_statement] in the
    flat namespace).  Mirrors the conclusion of [noise_map_correct] verbatim —
    a future non-per-coordinate noise (e.g. Gumbel / exponential mechanism) can
    discharge it WITHOUT the per-draw [noise_map_correct_of_draw] path. *)
Definition noise_map_correct_statement : Prop :=
  ∀ num den (Hproof : (0 < IZR num / IZR (2 * den))%R) (l l' : list Z),
    length l = length l' → (length l > 0)%nat →
    (∀ p, p ∈ zip_with (λ x y, (x, y)) l l' → (dZ p.1 p.2 <= 1)%R) →
    DPcoupl (noise_map num (2 * den) Hproof l) (noise_map num (2 * den) Hproof l')
      (λ zs zs', length zs = length zs' ∧ (length zs = length l)%nat ∧
                 list_Z_max zs = list_Z_max zs')
      (IZR num / IZR den) 0.

(** ** The per-coordinate constructor of the pivot.  Parametric over the single
    directional draw coupling [Hdraw] — this is the only place the per-draw
    structure of the noise is used; the tape layer never sees it. *)
Section draw.
  (** ONE directional general-shift coupling.  This is exactly the shape of
      [DPcoupl_laplace_draw]/[DPcoupl_exp_draw]: shifting the location by [k]
      costs [|k'|·ε] error when the (directional) shift [k+loc-loc'] lands in
      [0..k'].  We recover BOTH the 0-cost location isometry (at [k := loc'-loc],
      [k' := 0]) and the costly +1 shift at the argmax coordinate (at the
      doubled rate [num/(2·den)], [k := 1], [k' := 2], cost
      [IZR 2 · num/(2·den) = num/den]) from this single hypothesis. *)
  Context (Hdraw : ∀ num den loc loc' (k k' : Z),
             (0 < IZR num / IZR den)%R → (0 ≤ k + loc - loc')%Z → (k + loc - loc' ≤ k')%Z →
             DPcoupl (sample num den loc) (sample num den loc')
                     (λ z z', z + k = z')%Z (IZR k' * (IZR num / IZR den)) 0).

Lemma noise_map_pw_after num den l l' (Hproof: (0 < IZR num / IZR (2 * den))%R):
  length l = length l' ->
  (∀ p, p ∈ zip_with (λ x y, (x,y)) l l' -> (dZ p.1 p.2 <= 1)%R) ->
  DPcoupl (noise_map num (2*den) (Hproof) l)
    (noise_map num (2*den) (Hproof) l')
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
    (* SPOT 1: 0-cost location isometry — [Hdraw] at [k := hd'-hd], [k' := 0],
       so the draw relation [z + (hd'-hd) = z'] is [z - z' = hd - hd']. *)
    { epose proof (Hdraw num (2*den) hd hd' (hd'-hd) 0 ltac:(done) ltac:(lia) ltac:(lia)) as Hd0.
      eapply DPcoupl_mono; last apply Hd0; try done.
      - intros z z' Hzz'.
        apply dZ_bounded_cases'. simpl in *. lia.
      - rewrite Rmult_0_l; lra.
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


Lemma noise_map_pw num den l l' (Hproof: (0 < IZR num / IZR (2 * den))%R) j:
  length l = length l' ->
  (length l > 0)%nat ->
  (j<length l)%nat->
  (∀ p, p ∈ zip_with (λ x y, (x,y)) l l' -> (dZ p.1 p.2 <= 1)%R) ->
  DPcoupl (noise_map num (2*den) (Hproof) l)
    (noise_map num (2*den) (Hproof) l')
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
    (* SPOT 2: the +1 shift at the argmax coordinate — [Hdraw] at the doubled
       rate [num/(2·den)] with [k := 1], [k' := 2], cost [IZR 2 · num/(2·den)],
       brought down to [num/den] by [DPcoupl_mono] (it is an equality). *)
    { unshelve epose proof H4 (hd, hd') _ as H5.
      { rewrite elem_of_cons; naive_solver. }
      apply dZ_bounded_cases in H5. simpl in H5.
      epose proof (Hdraw num (2*den) hd hd' 1 2 ltac:(exact Hproof) ltac:(lia) ltac:(lia)) as Hd1.
      eapply DPcoupl_mono; last apply Hd1; try done.
      simpl. rewrite mult_IZR.
      replace (_/(_*_))%R with (/2 * (IZR num / IZR den))%R;
        last (rewrite Rdiv_mult_distr; lra).
      rewrite -Rmult_assoc.
      rewrite -{2}(Rmult_1_l (IZR num / IZR den)%R).
      apply Rmult_le_compat_r; [left; by apply ineq_convert | simpl; lra].
    }
    intros ?? <-.
    replace 0%R with (0+0)%R by lra.
    eapply DPcoupl_dbind; last apply noise_map_pw_after; try done; last first.
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
    (* SPOT 3: 0-cost isometry (before coordinate j) — same shape as SPOT 1:
       [Hdraw] at [k := hd'-hd], [k' := 0]. *)
    { unshelve epose proof H4 (hd, hd') _ as H5.
      { rewrite elem_of_cons; naive_solver. }
      apply dZ_bounded_cases in H5. simpl in H5.
      epose proof (Hdraw num (2*den) hd hd' (hd'-hd) 0 ltac:(done) ltac:(lia) ltac:(lia)) as Hd0.
      eapply DPcoupl_mono; last apply Hd0; try done.
      - intros z z' Hzz'.
        apply dZ_bounded_cases'. simpl in *. lia.
      - rewrite Rmult_0_l; lra.
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

Lemma noise_map_correct' num den l l' (Hproof: (0 < IZR num / IZR (2 * den))%R):
  length l = length l' ->
  (length l > 0)%nat ->
  (∀ p, p ∈ zip_with (λ x y, (x,y)) l l' -> (dZ p.1 p.2 <= 1)%R) ->
  DPcoupl (noise_map num (2*den) (Hproof) l)
    (noise_map num (2*den) (Hproof) l')
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
      - simpl. intros ? ? [? [?%noise_map_pos ?]].
        intros. subst.
        unshelve epose proof list_Z_max_bound x _; lia.
      - left. by apply ineq_convert.
      - apply noise_map_mass.
      - apply noise_map_mass.
    }
    eapply DPcoupl_mono; last eapply DPcoupl_pos_R; last eapply noise_map_pw; try done.
    simpl.
    intros ?? [H [Hlen%noise_map_pos Hlen'%noise_map_pos]]?.
    destruct!/=. eapply pw_list_Z_max_correct; naive_solver.
Qed. 

Lemma noise_map_correct num den l l' (Hproof: (0 < IZR num / IZR (2 * den))%R):
  length l = length l' ->
  (length l > 0)%nat ->
  (∀ p, p ∈ zip_with (λ x y, (x,y)) l l' -> (dZ p.1 p.2 <= 1)%R) ->
  DPcoupl (noise_map num (2*den) (Hproof) l)
    (noise_map num (2*den) (Hproof) l')
    (λ zs zs', length zs = length zs' /\ (length zs = length l)%nat /\
               list_Z_max zs = list_Z_max zs'
    ) (IZR num / IZR den) 0.
Proof.
  intros.
  eapply DPcoupl_mono; last (eapply DPcoupl_pos_R; eapply noise_map_correct'); try done.
  intros ??[?[?%noise_map_pos ?%noise_map_pos]]. lia.
Qed.

(** The per-coordinate construction of the pivot from the single draw coupling.
    On section-close this becomes
    [noise_map_correct_of_draw : ∀ sample mass Hdraw, noise_map_correct_statement sample]. *)
Lemma noise_map_correct_of_draw : noise_map_correct_statement.
Proof. intros num den Hproof l l'. apply noise_map_correct. Qed.

End draw.

(** ** The tape layer, pivoting on the per-distribution coupling fact as a
    HYPOTHESIS [Hmc].  Independent of how [Hmc] is obtained — the per-coordinate
    [noise_map_correct_of_draw] is ONE way; a future non-per-coordinate noise is
    another. *)
Section tape.
  Context (Hmc : noise_map_correct_statement).
  Context {S : Sig} `{!SampleIn D S} `{!diffprivGS S Σ}.
  Canonical Structure gen_ectxi_lang_rnm := gen_ectxi_lang S.
  Canonical Structure gen_ectx_lang_rnm := gen_ectx_lang S.
  Canonical Structure gen_lang_rnm := gen_lang S.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang S)).
  Local Notation lidx := (@sample_idx D S _).
  (* the generic tape value standing in for [prob_lang]'s [Tape_Laplace] record *)
  Local Notation NoiseT num den mean zs :=
    (sample_idx (D := D), sf_param_to_val D (num, den, mean)%Z,
      ((λ z : Z, LitV (LitInt z)) <$> zs)).

  (** Generic noise tape views, the [mkZNoise]-level analogue of [laplace_tapes]'
      [↪L]/[↪Lₛ] (hardcoded to [laplace_family]).  Here [D = mkZNoise sample mass]
      is section-local, so these are [Local Notation]s off the ambient
      [SampleIn D S] instance; [sf_param_to_val D (num,den,mean)] reduces
      definitionally to the explicit [PairV …] form below. *)
  Local Notation "α ↪N ( num , den , mean ; zs )" :=
    ((α ↪ (sample_idx (D := D),
             PairV (LitV (LitInt num)) (PairV (LitV (LitInt den)) (LitV (LitInt mean))),
             ((λ z : Z, LitV (LitInt z)) <$> zs)))%I)
    (at level 20, format "α  ↪N  ( num ,  den ,  mean ;  zs )") : bi_scope.

  Local Notation "α ↪Nₛ ( num , den , mean ; zs )" :=
    ((α ↪ₛ (sample_idx (D := D),
              PairV (LitV (LitInt num)) (PairV (LitV (LitInt den)) (LitV (LitInt mean))),
              ((λ z : Z, LitV (LitInt z)) <$> zs)))%I)
    (at level 20, format "α  ↪Nₛ  ( num ,  den ,  mean ;  zs )") : bi_scope.

  (** Noise-specific unfold of the generic [state_step]: a noise tape steps by a
      [sample] draw (appending its injection to the tape).  This reduces the
      generic [match sig_sample …] (via [sig_sample_at]) and composes the two
      [dmap]s — the gen analogue of [prob_lang]'s [state_step_laplace_unfold].
      Note [sf_sample D (num,den,mean) = sample num den mean] DEFINITIONALLY. *)
  Lemma state_step_noise_unfold σ α num den mean zs :
    stapes σ !! α = Some (NoiseT num den mean zs) →
    state_step S σ α =
      dmap (λ z : Z, state_upd_stapes (<[α := NoiseT num den mean (zs ++ [z])]>) σ)
        (sample num den mean).
  Proof.
    intros Hlook.
    erewrite state_step_unfold; last exact Hlook.
    rewrite (sig_sample_at D S (num, den, mean)).
    rewrite dmap_comp.
    apply dmap_eq; [|done]. intros z _.
    rewrite /compose fmap_app /=. done.
  Qed.

Fixpoint noise_presample_list σ ls:=
  match ls with
  | [] => dret σ
  | hd :: tl => dbind (λ σ', noise_presample_list σ' tl) (state_step S σ hd)
  end.

Fixpoint replace_noise_tape num den σ ls :=
  match ls with
  | [] => σ
  | hd::tl =>
      let '(ι, mean, ls, z) :=hd in
        state_upd_stapes <[ι := NoiseT num den mean (ls++[z])]> (replace_noise_tape num den σ tl)
  end.

Lemma noise_presample_list_rewrite_notin l tl x σ num den :
  l ∉ tl.*1.*1.*1 ->
  replace_noise_tape num den (state_upd_stapes <[l:=x]> σ)
    tl =
  state_upd_stapes <[l:=x]>
    (replace_noise_tape num den σ tl).
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

Lemma noise_presample_list_rewrite num den l σ (Hproof: (0 < IZR num / IZR (2*den))%R):
  Forall (λ '(ι, loc, lis), stapes σ!!ι = Some (NoiseT num (2*den) loc lis)) l ->
  NoDup (l.*1.*1) ->
  noise_presample_list σ ((l.*1).*1) =
  dbind (λ zs,
           dret (replace_noise_tape num (2*den) σ (zip l zs))
    ) (noise_map num (2*den) (Hproof) (l.*1.*2))
.
Proof.
  revert σ.
  induction l as [|hd tl IHl].
  { simpl. intros. by rewrite dret_id_left. }
  intros σ Hforall Hnodup.
  destruct hd as [[]].
  rewrite !fmap_cons.
  rewrite /noise_presample_list.
  etrans.
  { simpl.
    rewrite Forall_cons in Hforall.
    erewrite state_step_noise_unfold; last naive_solver.
    rewrite /dmap.
    eapply dbind_ext_right_strong.
    intros σ' Hpos.
    apply dbind_pos in Hpos.
    destruct!/=.
    (* [inv_distr_gen sample] substitutes σ' (dret-draw) and clears the abstract
       [sample] positivity hyp; unlike the Laplace [inv_distr] it does NOT
       [decide]-split, so there is no negative-ε branch to discharge here. *)
    inv_distr_gen sample.
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
                           replace_noise_tape num (2*den)
                             x
                             (zip tl a0))
                        (noise_map num (2*den) Hproof tl.*1.*2)).
      done.
  }
  rewrite /noise_map.
  rewrite -/noise_map.
  rewrite -!dbind_assoc'.
  apply dbind_ext_right.
  intros z'.
  rewrite /dmap.
  rewrite dret_id_left.
  rewrite -dbind_assoc'.
  apply dbind_ext_right_strong.
  intros ? Hpos.
  apply noise_map_pos in Hpos.
  rewrite dret_id_left.
  simpl. f_equal.
  rewrite noise_presample_list_rewrite_notin; first done.
  rewrite !length_fmap in Hpos.
  rewrite fst_zip; last lia.
  simpl in Hnodup.
  apply NoDup_cons in Hnodup.
  naive_solver.
Qed. 

(* ls a list of tape loc content*)

Lemma replace_noise_tape_zip ls zs num den σ:
  length ls = length zs ->
  NoDup (ls.*1.*1) ->
  Forall
    (λ '(ι, loc, lis, z),
       stapes (replace_noise_tape num (2 * den) σ (zip ls zs)) !! ι =
       Some (NoiseT num (2 * den) loc (lis ++ [z])))
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
    rewrite noise_presample_list_rewrite_notin; first done.
    rewrite fst_zip; first naive_solver.
    lia.
    Unshelve.
    + lia.
    + naive_solver.
Qed. 

Lemma noise_state_list_coupl num den ls ls' σ σ':
  (0 < IZR num / IZR (2 * den))%R -> 
  length ls = length ls' ->
  (length ls > 0)%nat ->
  (∀ p, p ∈ zip_with (λ x y, (x.1.2,y.1.2)) ls ls' -> (dZ p.1 p.2 <= 1)%R) ->
  (NoDup ls.*1.*1) ->
  (NoDup ls'.*1.*1) ->
  Forall (λ '(ι, loc, lis), stapes σ!!ι = Some (NoiseT num (2*den) loc lis)) ls ->
  Forall (λ '(ι, loc, lis), stapes σ'!!ι = Some (NoiseT num (2*den) loc lis)) ls' ->
  DPcoupl (noise_presample_list σ ls.*1.*1)
    (noise_presample_list σ' ls'.*1.*1)
    (λ σf σf',
       ∃ zs zs', length zs = length zs' /\ (length zs = length ls)%nat /\
                 list_Z_max zs = list_Z_max zs' /\
                 σf = (replace_noise_tape num (2 * den) σ (zip ls zs)) /\ 
                 σf' = (replace_noise_tape num (2 * den) σ' (zip ls' zs'))
    ) (IZR num / IZR den) 0.
Proof.
  intros H1 H2 H3 H4 H5 H6 H7 H8.
  unshelve (repeat erewrite noise_presample_list_rewrite); last first; try done.
  replace (0)%R with (0+0)%R by lra.
  replace (_/_)%R with (IZR num / IZR den + 0)%R by lra.
  eapply DPcoupl_dbind; [done|done| |apply Hmc]; last first.
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

Lemma noise_presample_list_erasable num den σ ls (Hineq:(0 < IZR num / IZR (2 * den))%R):
  NoDup ls.*1.*1->
  Forall (λ '(ι, loc, lis), stapes σ!!ι = Some (NoiseT num (2*den) loc lis)) ls ->
  erasable (Λ := gen_lang S) (noise_presample_list σ ls.*1.*1) σ.
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
    rewrite (state_step_noise_unfold _ _ _ _ _ _ H0) in Hpos.
    simpl in *.
    (* as above: no [decide]-split for the abstract [sample], so no degenerate
       branch — [inv_distr_gen] just clears the [sample] positivity hyp. *)
    inv_distr_gen sample.
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

Lemma replace_noise_tape_heap num den h l ls:
  (heap (replace_noise_tape num (2 * den)
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

  Lemma hoare_couple_noise_list_update xιs xιs' zs zs' ls ls' σ σ' num den:
    length xιs = length xιs' -> 
    NoDup xιs.*2 -> NoDup xιs'.*2 ->
    length zs = length xιs ->
    length zs' = length xιs ->
    ls = zip (zip xιs.*2 xιs.*1) (replicate (length xιs) []) ->
    ls' =zip (zip xιs'.*2 xιs'.*1) (replicate (length xιs) []) ->
    stapes_auth 1 (stapes σ) -∗
    spec_tapes_auth (stapes σ') -∗
    ([∗ list] '(x, ι);'(x', ι') ∈ xιs;xιs', ι ↪N (num,2 * den,x; []) ∗
            ι' ↪Nₛ (num,2 * den,x'; []) ∗ ⌜(Rabs (IZR (x - x')) <= 1)%R⌝)
    ==∗
    (stapes_auth 1 (stapes (replace_noise_tape num (2 * den) σ (zip ls zs)))) ∗
     spec_tapes_auth (stapes (replace_noise_tape num (2 * den) σ' (zip ls' zs'))) ∗
    ([∗ list] k↦'(x, ι);'(x', ι') ∈ xιs;xιs', ι ↪N (num,2 * den,x; [
                                                    zs !!! k]) ∗ ι' ↪Nₛ (num,2 * den,x'; [zs' !!! k]) ∗ ⌜(Rabs (IZR (x - x')) <= 1)%R⌝).
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
  
  Lemma hoare_couple_noise_list num den xιs xιs' N e Φ:
    (0 < IZR num / IZR (2 * den))%R ->
    length xιs = N ->
    length xιs = length xιs' ->
    (length xιs > 0)%nat ->
    NoDup xιs.*2 -> NoDup xιs'.*2 ->
           ↯m (IZR num / IZR den) -∗
           ([∗ list] '(x, ι);'(x', ι') ∈ xιs;xιs', ι ↪N (num, 2 * den,x; []) ∗ ι' ↪Nₛ (num,2 * den,x'; []) ∗ ⌜(dZ x x' <= 1)%R⌝) -∗
             ((∃ zs zs', ([∗ list] k ↦ '(x, ι);'(x', ι') ∈ xιs;xιs',
                            ι ↪N (num, 2 * den,x; [zs !!! k]) ∗
                            ι' ↪Nₛ (num,2 * den,x'; [zs' !!! k]) ∗
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
    iAssert (⌜Forall (λ '(ι, loc, lis), stapes σ!!ι = Some (NoiseT num (2*den) loc lis)) ls⌝)%I as "%".
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
    iAssert (⌜Forall (λ '(ι, loc, lis), stapes σ'!!ι = Some (NoiseT num (2*den) loc lis)) ls'⌝)%I as "%".
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
      apply noise_state_list_coupl; [| | |done|..]; try done.
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
    - eapply noise_presample_list_erasable; try done.
      unfold ls.
      rewrite !fst_zip; first done.
      + rewrite !length_fmap. lia.
      + rewrite !length_zip!length_replicate!length_fmap. lia.
    - eapply noise_presample_list_erasable; try done.
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
      rewrite !replace_noise_tape_heap.
      iFrame. 
      iMod (hoare_couple_noise_list_update _ _ zs zs' with "[$][$][$]") as "Hrest"; try done; try lia.
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

End tape.

End generic.

(** The per-noise instantiations (discharging the single [Hdraw] coupling, then
    feeding [noise_map_correct_of_draw] as the pivot [Hmc]) live in the thin
    [report_noisy_max_lemmas] (Laplace) and [report_noisy_max_exp_lemmas]
    (exponential), each ~40 lines — the payoff of this factoring.  A future
    non-per-coordinate noise can instead supply its own
    [noise_map_correct_statement] proof directly to the [tape] layer. *)
