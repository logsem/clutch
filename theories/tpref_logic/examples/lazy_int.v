From Coq Require Import Reals Psatz.
From clutch.prob_lang Require Import lang notation.
From clutch.tpref_logic Require Import weakestpre spec primitive_laws proofmode adequacy.
From clutch.prob Require Import distribution markov.
From clutch.tpref_logic.examples Require Import flip.
#[local] Open Scope R.

Section lazy_int.
  (* Context (CHUNCK_SIZE : nat). *)

  Lemma SeriesC_fin2 (f : fin 2 → R) :
    SeriesC f = f 0%fin + f 1%fin.
  Proof.
    rewrite (SeriesC_ext _ (λ b, (if bool_decide (b = 0%fin) then f 0%fin else 0) +
                                  if bool_decide (b = 1%fin) then f 1%fin else 0)).
    { rewrite SeriesC_plus; [|eapply ex_seriesC_singleton..].
      rewrite 2!SeriesC_singleton //. }
    intros n; inv_fin n; [simpl; lra|].
    intros n; inv_fin n; [simpl; lra|].
    intros n; inv_fin n.
  Qed.

  Lemma state_step_fair_coin_coupl σ α bs :
    σ.(tapes) !! α = Some ((1%nat; bs) : tape) →
    Rcoupl
      (state_step σ α)
      fair_coin
      (λ σ' b, σ' = state_upd_tapes (<[α := (1%nat; bs ++ [bool_to_fin b])]>) σ).
  Proof.
    intros Hα.
    exists (dmap (λ b, (state_upd_tapes (<[α := (1%nat; bs ++ [bool_to_fin b]) : tape]>) σ, b)) fair_coin).
    repeat split.
    - rewrite /lmarg dmap_comp /state_step.
      rewrite bool_decide_eq_true_2; [|by eapply elem_of_dom_2].
      rewrite lookup_total_alt Hα /=.
      eapply distr_ext=> σ'.
      rewrite /dmap /= /pmf /= /dbind_pmf.
      rewrite SeriesC_bool SeriesC_fin2 /=.
      rewrite {1 3 5 7}/pmf /= /fair_coin_pmf.
      destruct (decide (state_upd_tapes <[α:=(1%nat; bs ++ [1%fin])]> σ = σ')); subst.
      + rewrite {1 2}dret_1_1 // dret_0; [lra|].
        intros [= H%(insert_inv (tapes σ))]. simplify_eq.
      + destruct (decide (state_upd_tapes <[α:=(1%nat; bs ++ [0%fin])]> σ = σ')); subst.
        * rewrite {1 2}dret_0 // dret_1_1 //. lra.
        * rewrite !dret_0 //. lra.
    - rewrite /rmarg dmap_comp.
      assert ((snd ∘ (λ b : bool, _)) = Datatypes.id) as -> by f_equal.
      rewrite dmap_id //.
    - by intros [σ' b] (b' & [=-> ->] & ?)%dmap_pos=>/=.
  Qed.

  Lemma state_steps_fair_coins_coupl (σ : state) (α1 α2 : loc) (bs1 bs2 : list (fin 2)):
    α1 ≠ α2 →
    σ.(tapes) !! α1 = Some ((1%nat; bs1) : tape) →
    σ.(tapes) !! α2 = Some ((1%nat; bs2) : tape) →
    Rcoupl
      (state_step σ α1 ≫= (λ σ', state_step σ' α2))
      (dprod fair_coin fair_coin)
      (λ σ' '(b1, b2),
        σ' = (state_upd_tapes (<[α1 := (1%nat; bs1 ++ [bool_to_fin b1])]>)
             (state_upd_tapes (<[α2 := (1%nat; bs2 ++ [bool_to_fin b2])]>) σ))).
  Proof.
    intros Hneq Hα1 Hα2.
    rewrite /dprod.
    rewrite -(dret_id_right (state_step _ _ ≫= _)) -dbind_assoc.
    eapply Rcoupl_dbind; [|by eapply state_step_fair_coin_coupl].
    intros σ' b1 ->.
    eapply Rcoupl_dbind; [|eapply state_step_fair_coin_coupl]; last first.
    { rewrite lookup_insert_ne //. }
    intros σ' b2 ->.
    eapply Rcoupl_dret.
    rewrite /state_upd_tapes insert_commute //.
  Qed.


  Definition mstep (bs : bool * bool) : distr (bool * bool) :=
    let '(b1, b2) := bs in
    if bool_decide (b1 ≠ b2) then
      dzero
    else
      dprod fair_coin fair_coin.

  Definition mto_final (bs : bool * bool) : option (bool * bool) :=
    let '(b1, b2) := bs in
    if bool_decide (b1 ≠ b2) then Some (b1, b2) else None.

  Definition random_walks_mixin : MarkovMixin mstep mto_final.
  Proof.
    constructor.
    move=> [? ?]=>/= [[[? ?] ?] [? ?]].
    case_bool_decide; simplify_eq=>//.
  Qed.

  Canonical Structure random_walks : markov := Markov _ _ random_walks_mixin.

  (** Program *)
  Definition get_chunk : val :=
    λ: "chnk",
      match: !"chnk" with
      | NONE =>
          let: "b" := rand #1 in
          let: "next"  := ref NONEV in
          let: "val" := ("b", "next") in
          "chnk" <- SOME "val";;
          "val"
      | SOME "val" => "val"
      end.

  Definition cmp_Z : val :=
    λ: "z1" "z2",
      if: "z1" < "z2" then #(-1)
      else
        if: "z2" < "z1" then #1
        else #0.

  Definition cmp_list : val :=
    rec: "cmp_list" "cl1" "cl2" :=
      let: "c1n" := get_chunk "cl1" in
      let: "c2n" := get_chunk "cl2" in
      let: "res" := cmp_Z (Fst "c1n") (Fst "c2n") in
      if: "res" = #0 then
        "cmp_list" (Snd "c1n") (Snd "c2n")
      else
        "res".

  Definition sample_lazy_no : val :=
    λ: <>,
      let: "hd" := ref NONEV in
      "hd".

  Definition cmp_lazy_no : val :=
    λ: "lz1" "lz2",
      (* We short-circuit if the two locations are physically equal to avoid forcing sampling *)
      if: "lz1" = "lz2" then
        #0
      else
        cmp_list "lz1" "lz2".


  Context `{tprG random_walks Σ}.

  Fixpoint chunk_list (l : loc) (zs : list Z) : iProp Σ :=
    match zs with
    | [] => l ↦ NONEV
    | z :: zs =>
        ∃ l' : loc, l ↦ SOMEV (#z, #l') ∗ chunk_list l' zs
  end.

  Definition lazy_no (v : val) : iProp Σ :=
    ∃ (l : loc) (zs : list Z), ⌜v = #l⌝ ∧ chunk_list l zs .

  Definition comparison2z c : Z :=
    match c with
    | Eq => 0
    | Lt => -1
    | Gt => 1
    end.

  Lemma wp_cmp_Z (z1 z2 : Z) E :
    ⟨⟨⟨ True ⟩⟩⟩
      cmp_Z #z1 #z2 @ E
    ⟨⟨⟨ RET #(comparison2z (Z.compare z1 z2)); True%I ⟩⟩⟩.
  Proof.
    iIntros (Φ) "_ HΦ". rewrite /cmp_Z.
    destruct (Z.compare_spec z1 z2).
    - wp_pures; case_bool_decide; [lia|].
      wp_pures; case_bool_decide; [lia|].
      wp_pures. iApply "HΦ"; eauto.
    - wp_pures; case_bool_decide; [|lia].
      wp_pures. iApply "HΦ"; eauto.
    - wp_pures; case_bool_decide; [lia|].
      wp_pures; case_bool_decide; [|lia].
      wp_pures. iApply "HΦ"; eauto.
  Qed.

End lazy_int.
