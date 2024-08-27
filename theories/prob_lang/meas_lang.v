From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From mathcomp.analysis Require Import reals ereal signed normedtype sequences esum numfun measure lebesgue_measure lebesgue_integral.
From clutch.prob Require Export giry.
From clutch.prob_lang Require Import lang.

(*
Reserved Notation "'<<discr' G '>>'"
  (at level 2, format "'<<discr'  G  '>>'").


Section discrete_space.
  Local Open Scope classical_set_scope.

  Definition discrType (T : Type) : Type := T.

  Section discr_salgebra_instance.
    Variables (T: pointedType).
    Definition inhab : discrType T := (@point T).  (* There has to be better way *)

    Definition discr_meas : set (set (discrType T)) := [set: set (discrType T)].

    Lemma discr_meas0 : discr_meas set0.
    Proof. by []. Qed.

    Lemma discr_measC X : discr_meas X -> discr_meas (~` X).
    Proof. by []. Qed.

    Lemma discr_measU (F : sequence (set T)) : (forall i, discr_meas (F i)) -> discr_meas (\bigcup_i F i).
    Proof. by []. Qed.

    HB.instance Definition _ := gen_eqMixin (discrType T).
    HB.instance Definition _ := gen_choiceMixin (discrType T).
    HB.instance Definition _ := isPointed.Build (discrType T) inhab.
    HB.instance Definition _:= @isMeasurable.Build default_measure_display (discrType T) discr_meas
                                 discr_meas0 discr_measC discr_measU.
  End discr_salgebra_instance.

  Notation "'<<discr' G '>>'" := (discrType G) : classical_set_scope.

  (* Check <<discr cfg>>. *)


  Section discrete_space_mapout.
    Context {d2} {T1 : pointedType} {T2 : measurableType d2}.
    Variable (f : <<discr T1>> -> T2).

    Lemma discr_mapout_measurable S : (measurable_fun S f).
    Proof. rewrite /measurable_fun. intros. by rewrite /measurable/=/discr_meas/=. Qed.

  End discrete_space_mapout.
End discrete_space.




Section discrete_space_cfg.
  Local Open Scope classical_set_scope.

  (* Discrete measure on states (OK until we add reals and infinte tapes ) *)

  HB.instance Definition _ := gen_eqMixin cfg.
  HB.instance Definition _ := gen_choiceMixin cfg.
  HB.instance Definition _ := isPointed.Build cfg inhabitant.

  (* Is there some way to copy the sigma algebra from (discrType cfg) to cfg? *)
  (* Check ((discrType cfg) : measurableType _).
  Check (giryM _ (discrType cfg)). *)



  Fail Check (cfg : measurableType _).

  (* Check (fun x : cfg => (x : discrType cfg)). *)

  (*
  Definition cfg_meas : set (set cfg) := [set: set cfg].

  Lemma cfg_meas0 : cfg_meas set0.
  Proof. by []. Qed.

  Lemma cfg_measC X : cfg_meas X -> cfg_meas (~` X).
  Proof. by []. Qed.

  Lemma cfg_measU (F : sequence (set cfg)) : (forall i, cfg_meas (F i)) -> cfg_meas (\bigcup_i F i).
  Proof. by []. Qed.

  #[log]
  HB.instance Definition _:= @isMeasurable.Build default_measure_display cfg cfg_meas
                               cfg_meas0 cfg_measC cfg_measU.
   *)

End discrete_space_cfg.




Section unif_fin_space.
  Local Open Scope ereal_scope.
  Context {R : realType}.
  Variable (m : nat).

  Program Definition Ism_inhabitant : 'I_(S m). eapply (@Ordinal _), leqnn. Defined.

  HB.instance Definition _ := gen_eqMixin ('I_m).
  HB.instance Definition _ := gen_choiceMixin ('I_m).
  HB.instance Definition _ N := isPointed.Build ('I_(S m)) Ism_inhabitant.

  Definition unifM (X : set (discrType 'I_(S m))) : \bar R
    :=  if `[< finite_set X >] then ((#|` fset_set X |)%:R / (S m)%:R)%:E else +oo.

  Lemma unifM0 : unifM set0 = 0. Proof. Admitted.
  Lemma unifM_ge0 (A : set (discrType 'I_(S m))) : 0 <= unifM A. Proof. Admitted.
  Lemma unifM_sigma_additive : semi_sigma_additive unifM. Proof. Admitted.

  HB.instance Definition _ :=
    isMeasure.Build _ _ _ unifM unifM0 unifM_ge0 unifM_sigma_additive.

  Lemma unifM_T : unifM setT <= 1%E. Proof. Admitted.

  HB.instance Definition _ := Measure_isSubProbability.Build _ _ _ unifM unifM_T.

  (* Check (unifM : subprobability _ _).
  Check (unifM : giryType R (discrType ('I_(S m)))).

  Check (discrType ('I_(S m)) : measurableType _). (* Okay so this works *)
  Check (unifM : giryM R (discrType ('I_(S m)))). (* And this works too.... what does wrong withcfg? *) *)

End unif_fin_space.

(* Instead, we may consider restructing the semantics to use 'I_m instead of (fin m) *)
Definition fin_of_Im (m : nat) : 'I_m -> fin m.
Admitted.


Section meas_semantics.
  Local Open Scope classical_set_scope.
  Context {R : realType}.


  (* FIXME: make giryM_ret infer R from context? *)
  (* FIXME: make it so I don't have to annotate cfg everywhere (maybe as simple as changing the
      type to expt * state, but does that break the hierarchy?)*)

  (* FIXME why isn't this notation recognized *)
  (* Fail Check <<discr cfg>>. *)

  (* Check fun f => @giryM_map R _ _ _ _ _ (unifM (Z.to_nat _)) (discr_mapout_measurable f setT).

  Check (giryM _ (giryM _ (discrType cfg))).
  Check (giryM _ (discrType cfg)). *)

  Definition head_stepM (e1 : expr) (σ1 : state) : giryM R (discrType cfg) :=
    match e1 with
    | Rec f x e =>
        giryM_ret R ((Val $ RecV f x e, σ1) : discrType cfg)
    | Pair (Val v1) (Val v2) =>
        giryM_ret R ((Val $ PairV v1 v2, σ1) : discrType cfg)
    | InjL (Val v) =>
        giryM_ret R ((Val $ InjLV v, σ1) : discrType cfg)
    | InjR (Val v) =>
        giryM_ret R ((Val $ InjRV v, σ1) : discrType cfg)
    | App (Val (RecV f x e1)) (Val v2) =>
        giryM_ret R ((subst' x v2 (subst' f (RecV f x e1) e1) , σ1) : discrType cfg)
    | UnOp op (Val v) =>
        match un_op_eval op v with
          | Some w => giryM_ret R ((Val w, σ1) : discrType cfg)
          | _ => mzero
        end
    | BinOp op (Val v1) (Val v2) =>
        match bin_op_eval op v1 v2 with
          | Some w => giryM_ret R ((Val w, σ1) : discrType cfg)
          | _ => mzero
        end
    | If (Val (LitV (LitBool true))) e1 e2  =>
        giryM_ret R ((e1 , σ1) : discrType cfg)
    | If (Val (LitV (LitBool false))) e1 e2 =>
        giryM_ret R ((e2 , σ1) : discrType cfg)
    | Fst (Val (PairV v1 v2)) =>
        giryM_ret R ((Val v1 , σ1) : discrType cfg) (* Syntax error when I remove the space between v1 and , *)
    | Snd (Val (PairV v1 v2)) =>
        giryM_ret R ((Val v2, σ1) : discrType cfg)
    | Case (Val (InjLV v)) e1 e2 =>
        giryM_ret R ((App e1 (Val v), σ1) : discrType cfg)
    | Case (Val (InjRV v)) e1 e2 =>
        giryM_ret R ((App e2 (Val v), σ1) : discrType cfg)
    | AllocN (Val (LitV (LitInt N))) (Val v) =>
        let ℓ := fresh_loc σ1.(heap) in
        if bool_decide (0 < Z.to_nat N)%nat
          then giryM_ret R ((Val $ LitV $ LitLoc ℓ, state_upd_heap_N ℓ (Z.to_nat N) v σ1) : discrType cfg)
          else mzero
    | Load (Val (LitV (LitLoc l))) =>
        match σ1.(heap) !! l with
          | Some v => giryM_ret R ((Val v, σ1) : discrType cfg)
          | None => mzero
        end
    | Store (Val (LitV (LitLoc l))) (Val w) =>
        match σ1.(heap) !! l with
          | Some v => giryM_ret R ((Val $ LitV LitUnit, state_upd_heap <[l:=w]> σ1) : discrType cfg)
          | None => mzero
        end
    (* Uniform sampling from [0, 1 , ..., N] *)
    | Rand (Val (LitV (LitInt N))) (Val (LitV LitUnit)) => mzero
        (* giryM_map
          (unifM (Z.to_nat N))
          (discr_mapout_measurable
             (fun (n : 'I_(S (Z.to_nat N))) => ((Val $ LitV $ LitInt n, σ1) : discrType cfg)) setT) *)
    | AllocTape (Val (LitV (LitInt z))) =>
        let ι := fresh_loc σ1.(tapes) in
        giryM_ret R ((Val $ LitV $ LitLbl ι, state_upd_tapes <[ι := (Z.to_nat z; []) ]> σ1) : discrType cfg)
    (* Labelled sampling, conditional on tape contents *)
    | Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))) =>
        match σ1.(tapes) !! l with
        | Some (M; ns) =>
            if bool_decide (M = Z.to_nat N) then
              match ns  with
              | n :: ns =>
                  (* the tape is non-empty so we consume the first number *)
                  giryM_ret R ((Val $ LitV $ LitInt $ fin_to_nat n, state_upd_tapes <[l:=(M; ns)]> σ1) : discrType cfg)
              | [] => mzero (* FIXME *)
                  (* (* the tape is allocated but empty, so we sample from [0, 1, ..., M] uniformly *)
                  let f := (fun (n : 'I_(S (Z.to_nat M))) => ((Val $ LitV $ LitInt n, σ1) : discrType cfg)) in
                  @giryM_map _ _ _ _ _ _ (unifM (Z.to_nat _)) (discr_mapout_measurable f setT)  *)
              end
            else
              (* bound did not match the bound of the tape *)
              let f :=  (fun (n : 'I_(S (Z.to_nat M))) => ((Val $ LitV $ LitInt n, σ1) : discrType cfg)) in
              mzero
              (* @giryM_map _ _ _ _ _ _ (unifM (Z.to_nat M)) (discr_mapout_measurable f setT)  *)
        | None => mzero
        end
    | Tick (Val (LitV (LitInt n))) => giryM_ret R ((Val $ LitV $ LitUnit, σ1) : discrType cfg)
    | _ => mzero
    end.


  (** * Monadic itereration  *)
  Section giry_iterM.

    Context {d} {T : measurableType d}.

    (* Strangely enough, the fixpoint hangs my coq server when I admit the last obligation *)
    Local Definition unsound_meas_obligation d1 d2 T1 T2 f: @measurable_fun d1 d2 T1 T2 setT f.
    Proof. Admitted.

    (* Fixpoint giry_iterM (n : nat) (f : T -> (giryM R T)) (mf : measurable_fun setT f) (a : T) : giryM R T
      := match n with
           O => giryM_ret R a
         | (S n) =>
             let next : T -> giryM R T := giry_iterM n f mf in
             let next_mf : measurable_fun _ next := unsound_meas_obligation _ _ _ _ _ in
             giryM_bind (f a) next_mf
         end.
         *)

  End giry_iterM.







  (** NEXT: *)
  (* Connect the steps together with bind to get exec_n and exec *)
  (* Port state_step (easy) *)





  (* Change sigma algebra on expression to be generated from discrete sets on some parts, borel space on others *)
  (* Show that sampling a real value is measurable (map over unif. space on [0, 1] is measurable) *)
  (* Add random real sampling head step *)

  (* Change sigma algeba to measure real tapes (Borel of infinite product spaces)*)
  (* Add sample infinite tape step *)


  (** To port below *)


(*
Definition state_step (σ1 : state) (α : loc) : distr state :=
  if bool_decide (α ∈ dom σ1.(tapes)) then
    let: (N; ns) := (σ1.(tapes) !!! α) in
    dmap (λ n, state_upd_tapes (<[α := (N; ns ++ [n])]>) σ1) (dunifP N)
  else dzero.

*)
End meas_semantics.
*)
