From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From mathcomp.analysis Require Import reals ereal signed normedtype sequences esum numfun measure lebesgue_measure lebesgue_integral.
From clutch.prob Require Export giry.
From clutch.prob_lang Require Import lang.



Section discrete_space_cfg.
  Local Open Scope classical_set_scope.

  (* Discrete measure on states (OK until we add reals and infinte tapes ) *)

  Definition cfg_meas : set (set cfg) := [set: set cfg].

  Lemma cfg_meas0 : cfg_meas set0.
  Proof. by []. Qed.

  Lemma cfg_measC X : cfg_meas X -> cfg_meas (~` X).
  Proof. by []. Qed.

  Lemma cfg_measU (F : sequence (set cfg)) : (forall i, cfg_meas (F i)) -> cfg_meas (\bigcup_i F i).
  Proof. by []. Qed.

  #[log]
  HB.instance Definition _ := gen_eqMixin cfg.
  HB.instance Definition _ := gen_choiceMixin cfg.
  HB.instance Definition _ := isPointed.Build cfg inhabitant.

  #[log]
  HB.instance Definition _:= @isMeasurable.Build default_measure_display cfg cfg_meas
                               cfg_meas0 cfg_measC cfg_measU.

End discrete_space_cfg.



Section meas_semantics.
  Context {R : realType}.

  (* FIXME: make giryM_ret infer R from context? *)
  (* FIXME: make it so I don't have to annotate cfg everywhere (maybe as simple as changing the
      type to expt * state, but does that break the hierarchy?)*)

  Definition head_stepM (e1 : expr) (σ1 : state) : giryType R cfg :=
    match e1 with
    | Rec f x e =>
        giryM_ret R ((Val $ RecV f x e, σ1) : cfg)
    | Pair (Val v1) (Val v2) =>
        giryM_ret R ((Val $ PairV v1 v2, σ1) : cfg)
    | InjL (Val v) =>
        giryM_ret R ((Val $ InjLV v, σ1) : cfg)
    | InjR (Val v) =>
        giryM_ret R ((Val $ InjRV v, σ1) : cfg)
    | App (Val (RecV f x e1)) (Val v2) =>
        giryM_ret R ((subst' x v2 (subst' f (RecV f x e1) e1) , σ1) : cfg)
    | UnOp op (Val v) =>
        match un_op_eval op v with
          | Some w => giryM_ret R ((Val w, σ1) : cfg)
          | _ => mzero
        end
    | BinOp op (Val v1) (Val v2) =>
        match bin_op_eval op v1 v2 with
          | Some w => giryM_ret R ((Val w, σ1) : cfg)
          | _ => mzero
        end
    | If (Val (LitV (LitBool true))) e1 e2  =>
        giryM_ret R ((e1 , σ1) : cfg)
    | If (Val (LitV (LitBool false))) e1 e2 =>
        giryM_ret R ((e2 , σ1) : cfg)
(*
    | Fst (Val (PairV v1 v2)) =>
        giryM_ret R ((Val v1, σ1) : cfg) *)     (* Syntax error? what the hell? *)
    | Snd (Val (PairV v1 v2)) =>
        giryM_ret R ((Val v2, σ1) : cfg)
    | Case (Val (InjLV v)) e1 e2 =>
        giryM_ret R ((App e1 (Val v), σ1) : cfg)
    | Case (Val (InjRV v)) e1 e2 =>
        giryM_ret R ((App e2 (Val v), σ1) : cfg)
    | AllocN (Val (LitV (LitInt N))) (Val v) =>
        let ℓ := fresh_loc σ1.(heap) in
        if bool_decide (0 < Z.to_nat N)%nat
          then giryM_ret R ((Val $ LitV $ LitLoc ℓ, state_upd_heap_N ℓ (Z.to_nat N) v σ1) : cfg)
          else mzero
    | Load (Val (LitV (LitLoc l))) =>
        match σ1.(heap) !! l with
          | Some v => giryM_ret R ((Val v, σ1) : cfg)
          | None => mzero
        end
    | Store (Val (LitV (LitLoc l))) (Val w) =>
        match σ1.(heap) !! l with
          | Some v => giryM_ret R ((Val $ LitV LitUnit, state_upd_heap <[l:=w]> σ1) : cfg)
          | None => mzero
        end
    (* Rand *)
    | AllocTape (Val (LitV (LitInt z))) =>
        let ι := fresh_loc σ1.(tapes) in
        giryM_ret R ((Val $ LitV $ LitLbl ι, state_upd_tapes <[ι := (Z.to_nat z; []) ]> σ1) : cfg)
    (* Labelled Rand *)
    | Tick (Val (LitV (LitInt n))) => giryM_ret R ((Val $ LitV $ LitUnit, σ1) : cfg)
    | _ => mzero
    end.


  (** NEXT: *)
  (* Define dunif (means defining the discrete SA on 0..N), maybe do it in general (behind an alias ofc)? *)
  (* Show all functions from discrete types are measurable *)
  (* Fill in the rest of the holes *)
  Check giryM_map _.
  (* Connect the steps together with bind to get exec_n and exec *)


  (* Change sigma algebra on expression to be generated from discrete sets on some parts, borel space on others *)
  (* Show that sampling a real value is measurable (map over unif. space on [0, 1] is measurable) *)
  (* Add random real sampling head step *)

  (* Change sigma algeba to measure real tapes (Borel of infinite product spaces)*)
  (* Add sample infinite tape step *)


  (** To port below *)


    (*

    (* Since our language only has integers, we use Z.to_nat, which maps positive
       integers to the corresponding nat, and the rest to 0. We sample from
       [dunifP N = dunif (1 + N)] to avoid the case [dunif 0 = dzero]. *)
    (* Uniform sampling from [0, 1 , ..., N] *)
    | Rand (Val (LitV (LitInt N))) (Val (LitV LitUnit)) =>
        dmap (λ n : fin _, (Val $ LitV $ LitInt n, σ1)) (dunifP (Z.to_nat N))

    *)

  (*

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
*)

(*
Definition state_step (σ1 : state) (α : loc) : distr state :=
  if bool_decide (α ∈ dom σ1.(tapes)) then
    let: (N; ns) := (σ1.(tapes) !!! α) in
    dmap (λ n, state_upd_tapes (<[α := (N; ns ++ [n])]>) σ1) (dunifP N)
  else dzero.

*)
End meas_semantics.
