From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From mathcomp.analysis Require Import reals ereal signed normedtype sequences esum numfun measure lebesgue_measure lebesgue_integral.
From clutch.prob.monad Require Export laws.
From clutch.prob_lang Require Import lang.

Section cfg_sigma_algebra.
  (** Defines the sigma algebra on configurations *)
  (* Currently OK with a discrete space, until we add real-valued primitives to the langauge *)

  Local Open Scope classical_set_scope.

  (* Fail Check (<<discr cfg>> : measurableType _). *)
  HB.instance Definition _ := gen_eqMixin cfg.
  HB.instance Definition _ := gen_choiceMixin cfg.
  HB.instance Definition _ := isPointed.Build cfg inhabitant.
  (* Check (<<discr cfg>> : measurableType _). *)

End cfg_sigma_algebra.

Section meas_semantics.
  Local Open Scope classical_set_scope.
  Context {R : realType}.
  Notation giryM := (giryM (R := R)).

  Definition head_stepM_def (c : cfg) : giryM <<discr cfg>> :=
    let (e1, σ1) := c in
    match e1 with
    | Rec f x e =>
        giryM_ret R ((Val $ RecV f x e, σ1) : <<discr cfg>>)
    | Pair (Val v1) (Val v2) =>
        giryM_ret R ((Val $ PairV v1 v2, σ1) : <<discr cfg>>)
    | InjL (Val v) =>
        giryM_ret R ((Val $ InjLV v, σ1) : <<discr cfg>>)
    | InjR (Val v) =>
        giryM_ret R ((Val $ InjRV v, σ1) : <<discr cfg>>)
    | App (Val (RecV f x e1)) (Val v2) =>
        giryM_ret R ((subst' x v2 (subst' f (RecV f x e1) e1) , σ1) : <<discr cfg>>)
    | UnOp op (Val v) =>
        match un_op_eval op v with
          | Some w => giryM_ret R ((Val w, σ1) : <<discr cfg>>)
          | _ => giryM_zero
        end
    | BinOp op (Val v1) (Val v2) =>
        match bin_op_eval op v1 v2 with
          | Some w => giryM_ret R ((Val w, σ1) : <<discr cfg>>)
          | _ => giryM_zero
        end
    | If (Val (LitV (LitBool true))) e1 e2  =>
        giryM_ret R ((e1 , σ1) : <<discr cfg>>)
    | If (Val (LitV (LitBool false))) e1 e2 =>
        giryM_ret R ((e2 , σ1) : <<discr cfg>>)
    | Fst (Val (PairV v1 v2)) =>
        giryM_ret R ((Val v1 , σ1) : <<discr cfg>>) (* Syntax error when I remove the space between v1 and , *)
    | Snd (Val (PairV v1 v2)) =>
        giryM_ret R ((Val v2, σ1) : <<discr cfg>>)
    | Case (Val (InjLV v)) e1 e2 =>
        giryM_ret R ((App e1 (Val v), σ1) : <<discr cfg>>)
    | Case (Val (InjRV v)) e1 e2 =>
        giryM_ret R ((App e2 (Val v), σ1) : <<discr cfg>>)
    | AllocN (Val (LitV (LitInt N))) (Val v) =>
        let ℓ := fresh_loc σ1.(heap) in
        if bool_decide (0 < Z.to_nat N)%nat
          then giryM_ret R ((Val $ LitV $ LitLoc ℓ, state_upd_heap_N ℓ (Z.to_nat N) v σ1) : <<discr cfg>>)
          else giryM_zero
    | Load (Val (LitV (LitLoc l))) =>
        match σ1.(heap) !! l with
          | Some v => giryM_ret R ((Val v, σ1) : <<discr cfg>>)
          | None => giryM_zero
        end
    | Store (Val (LitV (LitLoc l))) (Val w) =>
        match σ1.(heap) !! l with
          | Some v => giryM_ret R ((Val $ LitV LitUnit, state_upd_heap <[l:=w]> σ1) : <<discr cfg>>)
          | None => giryM_zero
        end
    (* Uniform sampling from [0, 1 , ..., N] *)
    | Rand (Val (LitV (LitInt N))) (Val (LitV LitUnit)) =>
        giryM_map
          (m_discr (fun (n : 'I_(S (Z.to_nat N))) => ((Val $ LitV $ LitInt n, σ1) : <<discr cfg>>)))
          (giryM_unif (Z.to_nat N))
    | AllocTape (Val (LitV (LitInt z))) =>
        let ι := fresh_loc σ1.(tapes) in
        giryM_ret R ((Val $ LitV $ LitLbl ι, state_upd_tapes <[ι := (Z.to_nat z; []) ]> σ1) : <<discr cfg>>)
    (* Labelled sampling, conditional on tape contents *)
    | Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))) =>
        match σ1.(tapes) !! l with
        | Some (M; ns) =>
            if bool_decide (M = Z.to_nat N) then
              match ns  with
              | n :: ns =>
                  (* the tape is non-empty so we consume the first number *)
                  giryM_ret R ((Val $ LitV $ LitInt $ fin_to_nat n, state_upd_tapes <[l:=(M; ns)]> σ1) : <<discr cfg>>)
              | [] =>
                  giryM_map
                    (m_discr (fun (n : 'I_(S (Z.to_nat M))) => ((Val $ LitV $ LitInt n, σ1) : <<discr cfg>>)))
                    (giryM_unif (Z.to_nat _))
              end
            else
              (* bound did not match the bound of the tape *)
              giryM_map
                (m_discr (fun (n : 'I_(S (Z.to_nat M))) => ((Val $ LitV $ LitInt n, σ1) : <<discr cfg>>)))
                  (giryM_unif (Z.to_nat _))
        | None => mzero
        end
    | Tick (Val (LitV (LitInt n))) => giryM_ret R ((Val $ LitV $ LitUnit, σ1) : <<discr cfg>>)
    | _ => giryM_zero
    end.

  (* head_stepM is a measurable map because it is a function out of a discrete space.

     After we add continuous varaibles this argument gets more complex. It is not
     true in general that the match-wise composition of measurable maps is measurable. *)

  Definition head_stepM : measurable_map <<discr cfg>> (giryM <<discr cfg>>)
    := m_discr head_stepM_def.


  (** * Monadic itereration  *)
  Section giry_iterM.
    Local Open Scope classical_set_scope.
    Context {d} {T : measurableType d}.

    Fixpoint giry_iterM (n : nat) (f : measurable_map T (giryM T)) : measurable_map T (giryM T)
      := match n with
           O => giryM_ret R
         | (S n) => m_cmp (giryM_bind f) (giry_iterM n f)
         end.
  End giry_iterM.

  (* Check giry_iterM _ head_stepM. *)





  (** NEXT: *)
  (* Connect the steps together with bind to get exec_n and exec *)
  (* Port state_step (easy) *)


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
