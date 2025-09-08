From Coq Require Import Reals Psatz.
From Coq.ssr Require Import ssreflect.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy.
From stdpp Require Export countable finite.
From Coq.Logic Require Import ClassicalEpsilon.
From clutch.prelude Require Export base stdpp_ext Reals_ext Coquelicot_ext Series_ext classical uniform_list.
From clutch.prob Require Export countable_sum distribution.
From discprob.prob Require Import countable.

#[local] Open Scope R.

Section CntSubtypes.

  Global Instance eqdec_all {A : Type} : EqDecision A.
  Proof. by move => ??; apply make_decision. Qed.

  Local Lemma or_sumbool {P Q} : P ∨ Q -> {P} + {Q}.
  Proof. 
    intros.
    destruct (excluded_middle_informative P); first by econstructor.
    right. destruct H; auto.
    exfalso. by apply n.
  Qed.

  Context {A : Type}.

  Implicit Types (P : A -> Prop) (Q : A -> Prop).

  (* Definition EqDec_subtype_mono P Q `{EqDecision (sig Q)}: (∀ x, P x -> Q x) -> EqDecision (sig P).
  Proof. move => _ x y. by apply make_decision. Qed. *)
  (* move => H [a Ha] [b Hb].
    set af := exist Q a (H a Ha).
    set bf := exist Q b (H b Hb).
    destruct (decide (af = bf)).
    - left; by eapply classic_proof_irrel.PIT.subset_eq_compat, eq_sig_fst, e. 
    - right. unfold not. move => Hn. apply n.
      by eapply classic_proof_irrel.PIT.subset_eq_compat, eq_sig_fst, Hn.
  Qed. *)

  Definition Countable_subtype_mono P Q `{Countable (sig Q)} `{EqDecision (sig P)}: (∀ x, P x -> Q x) -> Countable (sig P).
  Proof.
    intro.
    destruct H.
    set enc := λ x : sig P, encode ((`x) ↾ (H0 _ $ proj2_sig x): sig Q).
    set dec := λ n : positive, match (decode n : option (sig Q)) with 
      | None => None
      | Some (x ↾ _) => match (excluded_middle_informative (P x)) with
        | left Hgx => Some (x ↾ Hgx : sig P)
        | right _ => None
      end
    end.
    econstructor.
    Unshelve. 
    2 : exact enc. 2: exact dec.
    rewrite /enc. rewrite /dec.
    intros.
    rewrite decode_encode.
    destruct (excluded_middle_informative (P (`x))); last by exfalso; apply n, (proj2_sig x).
    f_equal. 
    destruct x.
    by apply classic_proof_irrel.PIT.subset_eq_compat. 
  Qed.

  (* Definition EqDec_subtype_union P Q `{EqDecision (sig Q)} `{EqDecision (sig P)} : EqDecision (sig (fun x => P x ∨ Q x)).
  Proof. move => x y. by apply make_decision. Qed. *)

  Definition Countable_subtype_union P Q `{Countable (sig Q)} `{Countable (sig P)} `{EqDecision (sig (fun x => P x ∨ Q x))} : Countable (sig (fun x => P x ∨ Q x)).
  Proof. 
    destruct H. 
    destruct H0. 
    set enc := λ x : {x : A | P x ∨ Q x}, match or_sumbool $ proj2_sig x with
      | left Hp => xI $ encode0 ((`x) ↾ Hp)
      | right Hq => xO $ encode ((`x) ↾ Hq)
    end. 
    set dec : positive -> option {x : A | P x ∨ Q x} := λ nn : positive, match nn with
      | xH => None
      | xI n => match decode0 n with
        | None => None
        | Some (x ↾ Hx) => Some (x ↾ or_introl Hx) 
        end
      | xO n => match decode n with
        | None => None
        | Some (x ↾ Hx) => Some (x ↾ or_intror Hx) 
        end
    end. 
    econstructor. 
    Unshelve. 2: exact enc. 2: exact dec. 
    intro. rewrite /dec /enc. 
    destruct (or_sumbool (proj2_sig x)). 
    - rewrite decode_encode0; f_equal; destruct x => //=; by apply classic_proof_irrel.PIT.subset_eq_compat. 
    - rewrite decode_encode; f_equal; destruct x => //=; by apply classic_proof_irrel.PIT.subset_eq_compat. 
  Qed.

End CntSubtypes.

Definition support {X} (v: X → R) := { x : X | v x ≠ 0 }.

Definition inj_partial_inv {A B : Type} (f : A -> B) {H : Inj eq eq f} (b : B):= 
  match excluded_middle_informative (∃ a, f a = b) with
  | left P => Some $ proj1_sig (constructive_indefinite_description _ P)
  | right _ => None
  end.

Section CntSupp_inj.

  Context {A : Type}.

  Class CntSupp_inj (f : A -> R) := {
    SuppT : Type;
    supp_eqdec : EqDecision SuppT;
    supp_countable : Countable SuppT;
    supp_map : SuppT -> A;
    supp_map_inj : Inj eq eq supp_map;
    supp_is_supp : ∀ a, f a ≠ 0 -> ∃ x, supp_map x = a
  }.

End CntSupp_inj.

Section CntSupp.
  Context {A : Type}.

  Class CntSupp (f : A -> R) := MkCntSupp {
    (* existence is used for distribution extensionality *)
    CountableSupp : ∃ c : Countable (support f), True
  }. 

  Arguments CountableSupp {_}.

  Global Instance CntSupp_CountableSupp f {H : CntSupp f} : Countable (support f) := epsilon (CountableSupp H).

  Definition CntSupp_ext f `(CntSupp f) g : (∀ x, f x = g x) -> CntSupp g.
  Proof.
    intros.
    rewrite (functional_extensionality g f) => //.
  Qed.

  Global Instance CntSupp_equiv f `{CntSupp_inj A f} : CntSupp f.
  Proof.
    destruct H.
    constructor. 
    set sc := λ x : (support f), epsilon $ supp_is_supp0 (`x) (proj2_sig x).
    destruct supp_countable0.
    set enc := encode ∘ sc.
    set dec := λ x, match decode x with
      | None => None
      | Some x => match decide (f $ supp_map0 x = 0) with
        | left _ => None
        | right Hx => Some (supp_map0 x ↾ Hx) : option (support f)
      end
      end.
    econstructor => //=.
    exists enc dec.
    intros.
    rewrite /dec /enc /sc //= decode_encode. 
    specialize (epsilon_correct _ (supp_is_supp0 (`x) (proj2_sig x))) => //= H'.
    case_decide.
    - rewrite H' in H; exfalso; by apply (proj2_sig x). 
    - f_equal; destruct x; simpl in *; by apply classic_proof_irrel.PIT.subset_eq_compat.
  Qed.

  Definition CntSupp_incl f `(CntSupp f) g : (∀ x, g x ≠ 0 -> f x ≠ 0) -> CntSupp g.
  Proof.
    intros.
    do 2 econstructor; last auto. 
    by eapply (Countable_subtype_mono _ _ H0).
  Qed.

  Global Instance CntSupp_cst0 : CntSupp (λ _ : A, 0).
  Proof. 
    eapply CntSupp_equiv. 
    econstructor. 
    - eapply Empty_set_countable.
    - move => ??? //=.
    - intros. lra.
    Unshelve. tauto.
  Qed.

  Global Instance CntSupp_dirac a {hd} r : CntSupp (λ a' : A, if @bool_decide (a = a') (hd a') then r else 0).
  Proof. 
    eapply CntSupp_equiv. 
    econstructor.
    Unshelve. 5 : exact (fun x : () => a).
    - eapply unit_countable.
    - move => [][]? //=.
    - intro. case_bool_decide.
      + intro. by econstructor.
      + intro. lra.
  Qed.

  Global Instance CntSupp_dirac' a {hd} r : CntSupp (λ a' : A, if @bool_decide (a' = a) (hd a') then r else 0).
  Proof. 
    eapply CntSupp_ext; first apply (CntSupp_dirac a).
    simpl. intros. do 2 case_bool_decide; auto; by exfalso.
  Qed.

  Global Instance CntSupp_restrict {P} {Hdp} `{CntSupp h} : CntSupp (λ a' : A, if @bool_decide (P a') (Hdp a') then h a' else 0).
  Proof. 
    do 2 econstructor => //=.
    destruct H as [H']. pose proof (epsilon H') as H.
    eapply Countable_subtype_mono; first apply H.
    intros. by case_bool_decide.
  Qed.

  Global Instance CntSupp_add f g `{CntSupp f, CntSupp g} : CntSupp (λ x, f x + g x).
  Proof. 
    do 2 econstructor => //=.
    eapply (Countable_subtype_mono _ (λ x, f x ≠ 0 ∨ g x ≠ 0)).
    intros.
    destruct (decide (f x = 0)); last by left.
    rewrite e in H1. right. lra.
    Unshelve.
    eapply Countable_subtype_union; by apply CntSupp_CountableSupp.
  Qed.

  Global Instance CntSupp_scal_l f r `{CntSupp f} : CntSupp (λ x, r * f x).
  Proof. eapply CntSupp_incl => //= a /Rmult_neq_0_reg [??] //=. Qed.

  Global Instance CntSupp_scal_r f r `{CntSupp f} : CntSupp (λ x, f x * r).
  Proof. eapply CntSupp_incl => //= a /Rmult_neq_0_reg [??] //=. Qed.

  Global Instance CntSupp_mul_r f g `{CntSupp f} : CntSupp (λ x, g x * f x).
  Proof. eapply CntSupp_incl => //= a /Rmult_neq_0_reg [??] //=. Qed.

  Global Instance CntSupp_mul_l f g `{CntSupp f} : CntSupp (λ x, f x * g x).
  Proof. eapply CntSupp_incl => //= a /Rmult_neq_0_reg [??] //=. Qed.

  Global Instance CntSupp_sub f g `{CntSupp f, CntSupp g} : CntSupp (λ x, f x - g x).
  Proof. 
    eapply (CntSupp_ext (fun x => f x + (-1) * g x)); last by real_solver.
    apply CntSupp_add => //=; apply CntSupp_mul_r => //=.
  Qed.

End CntSupp.


Global Instance CntSupp_cnt `{Countable A} (f : A -> R) : CntSupp f.
Proof.
  eapply CntSupp_equiv.
  econstructor; eauto.
  - apply id_inj.
  - intros. by eexists.
Qed.


Section SeriesCS.
  Context {A : Type}.

  Implicit Types h g : A -> R.

  Definition is_seriesCS h `{CntSupp _ h} := is_seriesC (λ (x : support h), h $ proj1_sig x).
  Definition ex_seriesCS h `{CntSupp _ h} := ex_seriesC (λ (x : support h), h $ proj1_sig x).
  Definition SeriesCS h `{CntSupp _ h} := SeriesC (λ (x : support h), h $ proj1_sig x).

  Lemma ex_seriesCS_countable `{Countable A} h : ex_seriesCS h ↔ ex_seriesC h.
  Proof.
  Admitted.

  Lemma SeriesCS_countable `{Countable A} h : SeriesC h = SeriesCS h.
  Proof.
  Admitted.

  Lemma SeriesCS_singleton (a : A) {hd} r : SeriesCS (λ a', if @bool_decide (a' = a) (hd a') then r else 0) = r.  
  Proof.
  Admitted.

  Lemma SeriesCS_singleton' (a : A) {hd} r: SeriesCS (λ a', if @bool_decide (a = a') (hd a') then r else 0) = r.  
  Proof.
  Admitted.

  Lemma ex_seriesCS_singleton (a : A) {hd} r: ex_seriesCS (λ a', if @bool_decide (a' = a) (hd a') then r else 0).  
  Proof.
  Admitted.

  Lemma ex_seriesCS_singleton' (a : A) {hd} r: ex_seriesCS (λ a', if @bool_decide (a = a') (hd a') then r else 0).  
  Proof.
  Admitted.

  Lemma ex_seriesCS_ext h g `{CntSupp _ h} `{CntSupp _ g} : 
    (∀ x, h x = g x)
    → ex_seriesCS h 
    → ex_seriesCS g.
  Proof.
  Admitted.

  Lemma SeriesCS_ext h g `{CntSupp _ h} `{CntSupp _ g} : 
    (∀ x, h x = g x)
    → SeriesCS h = SeriesCS g.
  Proof.
  Admitted.

  Lemma ex_seriesCS_le `{CntSupp _ h} `{CntSupp _ g} : 
    (∀ x , 0 <= h x <= g x)
    → ex_seriesCS g
    → ex_seriesCS h.
  Proof.
    intros.
    rewrite /SeriesCS.
  Admitted.

  Lemma SeriesCS_le `{CntSupp _ h} `{CntSupp _ g} : 
    (∀ x , 0 <= h x <= g x)
    → ex_seriesCS g
    → SeriesCS h <= SeriesCS g.
  Proof.
    intros.
    rewrite /SeriesCS.
  Admitted.

  Lemma SeriesCS_ge_elem `{CntSupp _ h} (a : A) : 
    (∀ x : A, 0 <= h x) 
    → ex_seriesCS h 
    → h a <= SeriesCS h.
  Proof.
  Admitted.

  Lemma SeriesCS_split_elem h `{CntSupp _ h} (a0 : A):
    (∀ a : A, 0 <= h a)
    → ex_seriesCS h
    → SeriesCS h =
      SeriesCS (λ a : A, if bool_decide (a = a0) then h a else 0) +
      SeriesCS (λ a : A, if bool_decide (a ≠ a0) then h a else 0).
  Proof.
  Admitted.

  Lemma SeriesCS_ge_0 h `{CntSupp _ h} :
    (∀ a, 0 <= h a)
    → ex_seriesCS h
    → 0 <= SeriesCS h. 
  Proof.
  Admitted.  

  Lemma ex_seriesCS_scal_r c h `{CntSupp _ h} : 
    ex_seriesCS h ->
    ex_seriesCS (λ x, h x * c).
  Admitted.

  Lemma SeriesCS_scal_r c h `{CntSupp _ h} : 
    SeriesCS (λ x, h x * c) = SeriesCS h * c.
  Admitted.

End SeriesCS.


Section cdistr.

  Record cdistr (A : Type) := MkCDistr {
    cpmf :> A -> R;
    cpmf_cntsupp : CntSupp cpmf;
    cpmf_pos : ∀ a, 0 <= cpmf a;
    cpmf_ex_seriesCS : ex_seriesCS cpmf;
    cpmf_SeriesC : SeriesCS cpmf <= 1;
  }.

  Global Arguments MkCDistr {_}.
  Global Arguments cpmf {_} _ : simpl never.
  Global Arguments cpmf_cntsupp {_}.
  Global Arguments cpmf_pos {_}.
  Global Arguments cpmf_ex_seriesCS {_}.
  Global Arguments cpmf_SeriesC {_}.

  Global Instance cdistr_cntsupp {A : Type} (μ : cdistr A) : CntSupp μ := cpmf_cntsupp μ. 
End cdistr.

Program Coercion distr_cdistr `{Countable A} (μ : distr A) : cdistr A := @MkCDistr A (μ.(pmf)) _ _ _ _.
Next Obligation. real_solver. Qed.
Next Obligation. intros. by apply ex_seriesCS_countable. Qed.
Next Obligation. intros. by rewrite -SeriesCS_countable. Qed.

Lemma distr_cdistr_eq `{Countable A} (μ : distr A) : ∀ a, distr_cdistr μ a = μ a.
Proof. rewrite /distr_cdistr //=. Qed.

#[global] Hint Resolve cpmf_pos cpmf_ex_seriesCS cpmf_SeriesC distr_cdistr_eq : core.
Section distributions.
  Context {A : Type}.

  Implicit Types μ d : cdistr A.

  Global Instance cdistr_dec μ1 μ2 : Decision (μ1 = μ2).
  Proof. apply make_decision. Qed.

  Lemma cpmf_le_1 μ a : μ a <= 1.
  Proof.
    assert (SeriesCS (λ a', if bool_decide (a' = a) then μ a else 0) = μ a) as <-;
    first by rewrite SeriesCS_singleton.
    etransitivity; [|eapply (cpmf_SeriesC μ)].
    apply SeriesCS_le; [|done].
    real_solver.
  Qed.

  Lemma cpmf_SeriesC_ge_0 μ : 0 <= SeriesCS μ.
  Proof.
    transitivity (SeriesCS (λ (_ : A), 0)).
    { apply SeriesC_ge_0; [done|]. apply ex_seriesC_0. }
    apply SeriesCS_le; by [split|].
  Qed.

  Hint Resolve cpmf_le_1 : core.
  Hint Resolve cpmf_SeriesC_ge_0 : core.

  Lemma cpmf_ex_seriesC_mult_fn μ (f : A → R) :
    (∃ n, ∀ a, 0 <= f a <= n) →
    ex_seriesCS (λ a, μ a * f a).
  Proof.
    intros [n Hf].
    apply (ex_seriesCS_le (g := λ a, μ a * n)); first by real_solver.
    by apply ex_seriesCS_scal_r.
  Qed.
  
  Lemma cpmf_ex_seriesC_mult (μ1 μ2 : cdistr A) :
    ex_seriesCS (λ a, μ1 a * μ2 a).
  Proof.
    eapply cpmf_ex_seriesC_mult_fn.
    exists 1. real_solver.
  Qed.

  Lemma cpmf_le_SeriesC (μ : cdistr A) (a : A) :
    μ a <= SeriesCS μ.
  Proof. by eapply SeriesCS_ge_elem. Qed.

  Lemma cpmf_1_eq_SeriesC (μ : cdistr A) (a : A) :
    μ a = 1 → μ a = SeriesCS μ.
  Proof.
    intros Hμ. rewrite Hμ.
    apply Rle_antisym => //=.
    { rewrite -Hμ. eapply cpmf_le_SeriesC. }
  Qed.

  Lemma cpmf_plus_neq_SeriesC (μ : cdistr A) (a a' : A) :
    a ≠ a' → μ a + μ a' <= SeriesCS μ.
  Proof.
    intros Ha.
    rewrite (SeriesCS_split_elem _ a); [|done|done].
    eapply Rle_plus_plus.
    - erewrite (SeriesCS_ext _ (λ a0 : A, if bool_decide (a0 = a) then μ a else 0)); first by erewrite SeriesCS_singleton. 
      real_solver.
    - rewrite (SeriesCS_split_elem _ a'); last first.
      + eapply ex_seriesCS_le; [|eapply (cpmf_ex_seriesCS μ)].
        real_solver.
      + real_solver.
      + apply Rle_plus_l.
        * erewrite (SeriesCS_ext _ (λ a0 : A, if bool_decide (a0 = a') then μ a' else 0)); [by erewrite SeriesCS_singleton| real_solver].
        * eapply SeriesCS_ge_0; first real_solver.
          eapply ex_seriesCS_le; [|eapply (cpmf_ex_seriesCS μ)].
          real_solver.
  Qed.

  Lemma cpmf_1_supp_eq (μ : cdistr A) (a a' : A) :
    μ a = 1 → μ a' > 0 → a = a'.
  Proof.
    intros Ha Ha'.
    destruct (decide (a = a')) as [|Hneq]; [done|].
    pose proof (cpmf_le_SeriesC μ a').
    pose proof (cpmf_1_eq_SeriesC _ _ Ha).
    pose proof (cpmf_plus_neq_SeriesC μ a a' Hneq).
    lra.
  Qed.

  (* N.B. uses [functional_extensionality] and [proof_irrelevance] axioms  *)
  Lemma cdistr_ext (d1 d2 : cdistr A) :
    (∀ a, d1.(cpmf) a = d2.(cpmf) a) → d1 = d2.
  Proof.
    destruct d1 as [pmf1 ?], d2 as [pmf2 ?] =>/=. intros Ha.
    assert (pmf1 = pmf2) as ->; [by extensionality b|].
    assert (cpmf_cntsupp0 = cpmf_cntsupp1) as ->; [by apply proof_irrelevance|].
    f_equal; apply proof_irrelevance.
  Qed.

  Lemma cdistr_ext_pmf (d1 d2 : cdistr A) :
    d1.(cpmf)  = d2.(cpmf) → d1 = d2.
  Proof.
    destruct d1 as [pmf1 ?], d2 as [pmf2 ?] =>/=.
    rewrite /cpmf. intros ->.
    assert (cpmf_cntsupp0 = cpmf_cntsupp1) as ->; [by apply proof_irrelevance|].
    f_equal; apply proof_irrelevance.
  Qed.

  Lemma cpmf_eq_0_le (μ : cdistr A) (a : A):
    μ a <= 0 → μ a = 0.
  Proof. by intros [Hlt%(Rle_not_gt _ _ (cpmf_pos μ a)) |]. Qed.

  Lemma cpmf_eq_0_not_gt_0 (μ : cdistr A) (a : A):
    ¬ (μ a > 0) → μ a = 0.
  Proof. intros ?%Rnot_gt_ge%Rge_le. by apply cpmf_eq_0_le. Qed.

  Lemma cpmf_mult_eq_0 {B} (μ : cdistr A) (μ' : cdistr B) a b:
    (μ a > 0 -> μ a * μ' b = 0) -> μ a * μ' b = 0.
  Proof.
    intros. destruct (cpmf_pos μ a) as [|<-]; last lra.
    naive_solver.
  Qed. 
End distributions.

#[global] Hint Resolve cpmf_le_1 : core.
#[global] Hint Resolve cpmf_SeriesC_ge_0 : core.

Global Instance distr_double_cntsupp_a {A B} (f : A → cdistr B) (μ : cdistr A) :
  CntSupp (λ a : A, SeriesCS (λ b : B, μ a * f a b)).
Proof.
Admitted.

Global Instance distr_double_cntsupp_b {A B} (f : A → cdistr B) (μ : cdistr A) :
  CntSupp (λ b : B, SeriesCS (λ a : A, μ a * f a b)).
Proof.
Admitted.


(** * Sum-swapping equalities for distributions *)
Lemma cdistr_double_swap_ex {A B} (f : A → cdistr B) (μ : cdistr A) :
  ex_seriesCS (λ a : A, SeriesCS (λ b : B, μ a * f a b)) ->
  ex_seriesCS (λ b : B, SeriesCS (λ a : A, μ a * f a b)).
Proof.
(*
  intro Hex.
  apply (fubini_pos_seriesC_ex_double (λ '(a, b), μ a * f a b)); [| |done].
  - real_solver.
  - intros. apply (ex_seriesC_le _ (f a)); [|done].
    real_solver.
Qed. *)
Admitted.

Lemma cdistr_double_swap {A B} (f : A → cdistr B) (μ : cdistr A):
  SeriesCS (λ b : B, SeriesCS (λ a : A, μ a * f a b)) =
  SeriesCS (λ a : A, SeriesCS (λ b : B, μ a * f a b)).
Proof.
  (* apply (fubini_pos_seriesC (λ '(a, b), μ a * f a b)).
  - real_solver.
  - intros a. apply (ex_seriesC_le _ (f a)); [|done].
    real_solver.
  - eapply (ex_seriesC_ext (λ j, μ j * SeriesC (λ k, f j k))).
    { intros a. rewrite SeriesC_scal_l //. }
    apply (ex_seriesC_le _ (λ a : A, μ a * 1)); [|by apply ex_seriesC_scal_r].
    real_solver. *)
Admitted.

(* 



Lemma distr_double_lr `{Countable A, Countable B} (f : A → distr B) (μ : distr A) :
  SeriesC (λ '(a, b), μ a * f a b) =
  SeriesC (λ a : A, SeriesC (λ b : B, μ a * f a b)).
Proof.
  apply (fubini_pos_seriesC_prod_lr (λ '(a, b), μ a * f a b)).
  - real_solver.
  - apply ex_seriesC_prod.
    + real_solver.
    + intro. by apply ex_seriesC_scal_l.
    + setoid_rewrite SeriesC_scal_l.
      apply (ex_seriesC_le _ μ); [|done].
      real_solver.
Qed.

Lemma distr_double_rl `{Countable A, Countable B} (f : A → distr B) (μ : distr A) :
  SeriesC (λ '(a, b), μ a * f a b) =
  SeriesC (λ b : B, SeriesC (λ a : A, μ a * f a b)).
Proof.
  apply (fubini_pos_seriesC_prod_rl (λ '(a, b), μ a * f a b)).
  - real_solver.
  - apply ex_seriesC_prod.
    + real_solver.
    + intro. by apply ex_seriesC_scal_l.
    + setoid_rewrite SeriesC_scal_l.
      apply (ex_seriesC_le _ μ); [|done].
      real_solver.
Qed.

Lemma distr_double_swap_rmarg_ex `{Countable A, Countable B, Countable B'}
  (f : A → distr (B * B')) (μ : distr A) b' :
  ex_seriesC (λ a : A, SeriesC (λ b : B, μ a * f a (b, b'))) →
  ex_seriesC (λ b : B, SeriesC (λ a : A, μ a * f a (b, b'))).
Proof.
  intro Hex.
  apply (fubini_pos_seriesC_ex_double (λ '(a, b), μ a * f a (b, b'))); [| |done].
  - real_solver.
  - intros a. apply ex_seriesC_scal_l.
    apply (ex_seriesC_rmarg (f a)); [|done].
    real_solver.
Qed.

Lemma distr_double_swap_rmarg `{Countable A, Countable B, Countable B'}
  (f : A → distr (B * B')) (μ : distr A) b' :
  SeriesC (λ a : A, SeriesC (λ b : B, μ a * f a (b, b'))) =
  SeriesC (λ b : B, SeriesC (λ a : A, μ a * f a (b, b'))).
Proof.
  rewrite (fubini_pos_seriesC (λ '(a, b), μ a * f a (b, b'))); [done| | |].
  - real_solver.
  - intros. apply ex_seriesC_scal_l.
    apply (ex_seriesC_rmarg (f a)); [real_solver|done].
  - setoid_rewrite SeriesC_scal_l.
    apply (ex_seriesC_le _ μ); [|done].
    intro a; split.
    + apply Rmult_le_pos; [done|].
      apply SeriesC_ge_0; [done|].
      by apply (ex_seriesC_rmarg (f a)).
    + rewrite -{2}(Rmult_1_r (μ _)).
      apply Rmult_le_compat_l; [done|].
      apply (Rle_trans _ (SeriesC (f a))); [|done].
      apply (seriesC_rmarg_le (f a)); [real_solver|done].
Qed.

Lemma distr_double_swap_lmarg_ex `{Countable A, Countable B, Countable B'}
  (f : A → distr (B * B')) (μ : distr A) (b : B) :
  ex_seriesC (λ a : A, SeriesC (λ b' : B', μ a * f a (b, b'))) →
  ex_seriesC (λ b' : B', SeriesC (λ a : A, μ a * f a (b, b'))).
Proof.
  intro Hex.
  apply (fubini_pos_seriesC_ex_double (λ '(a, b'), μ a * f a (b, b'))); auto.
  - real_solver.
  - intros. apply ex_seriesC_scal_l.
    apply (ex_seriesC_lmarg (f a)); [real_solver|done].
Qed.

Lemma distr_double_swap_lmarg `{Countable A, Countable B, Countable B'}
  (f : A → distr (B * B')) (μ : distr A) (b : B) :
  SeriesC (λ a : A, SeriesC (λ b' : B', μ a * f a (b, b'))) =
  SeriesC (λ b' : B', SeriesC (λ a : A, μ a * f a (b, b'))).
Proof.
  rewrite (fubini_pos_seriesC (λ '(a, b'), μ a * f a (b, b'))); [done| | |].
  - real_solver.
  - intros . apply ex_seriesC_scal_l.
    apply (ex_seriesC_lmarg (f a)); [real_solver|done].
  - setoid_rewrite SeriesC_scal_l.
    apply (ex_seriesC_le _ μ); [|done].
    intro a; split.
    + apply Rmult_le_pos; [done|].
      apply SeriesC_ge_0; [done|].
      by apply (ex_seriesC_lmarg (f a)).
    + rewrite -{2}(Rmult_1_r (μ _)).
      apply Rmult_le_compat_l; [done|].
      apply (Rle_trans _ (SeriesC (f a))); [|done].
      apply (seriesC_lmarg_le (f a)); [real_solver|done].
Qed.
 *)

Section cdret.
  (** * Monadic return  *)

  Context {A : Type}.

  Definition cdret_pmf {A : Type} a : A → R :=
    λ (a' : A), if bool_decide (a' = a) then 1 else 0.

  Program Definition cdret (a : A) : cdistr A := MkCDistr (cdret_pmf a) _ _ _ _.
  Next Obligation. intros. rewrite /cdret_pmf. case_bool_decide; nra. Qed.
  Next Obligation. intros. rewrite /cdret_pmf. apply (ex_seriesCS_singleton a). Qed.
  Next Obligation. intros. rewrite SeriesCS_singleton //. Qed.


  Lemma cdret_pmf_unfold (a a' : A):
    cdret a a' = if bool_decide (a' = a) then 1%R else 0%R.
  Proof. done. Qed. 

  Lemma cdret_1 (a a' : A) :
    a = a' ↔ cdret a a' = 1.
  Proof.
    split.
    - intros ->. rewrite /cpmf /= /cdret_pmf bool_decide_eq_true_2 //.
    - rewrite /cpmf /= /cdret_pmf. case_bool_decide; [done|lra].
  Qed.

  Lemma cdret_1_1 (a a' : A) :
    a = a' → cdret a a' = 1.
  Proof. apply cdret_1. Qed.

  Lemma cdret_1_2 (a a' : A) :
    cdret a a' = 1 → a = a'.
  Proof. apply cdret_1. Qed.

  Lemma cdret_0 (a a' : A) :
    a' ≠ a → cdret a a' = 0.
  Proof. intros ?. rewrite /cpmf /= /cdret_pmf bool_decide_eq_false_2 //. Qed.

  Lemma cdret_pos (a a' : A) :
    cdret a a' > 0 → a' = a.
  Proof. rewrite /cpmf /= /cdret_pmf. intros ?. case_bool_decide; [done|lra]. Qed.

  Lemma cdret_pmf_map (f : A → A)  `{Inj A A (=) (=) f} (a a' : A) :
    cdret (f a) (f a') = cdret a a'.
  Proof.
    rewrite /cpmf /= /cdret_pmf. case_bool_decide as Hcase.
    - apply (inj f) in Hcase as ->. rewrite bool_decide_eq_true_2 //.
    - case_bool_decide; [|done]. simplify_eq.
  Qed.
  
  Lemma cpmf_1_eq_dret (μ : cdistr A) (a : A) :
    μ a = 1 → μ = cdret a.
  Proof.
    intros Hμ.
    apply cdistr_ext.
    intros a'.
    destruct (decide (a = a')) as [<- | Hneq].
    { rewrite cdret_1_1 //. }
    rewrite cdret_0 //.
    destruct (decide (μ a' > 0)) as [Ha'|].
    - rewrite (cpmf_1_supp_eq _ _ _ Hμ Ha') // in Hneq.
    - by apply cpmf_eq_0_not_gt_0.
  Qed.

  Lemma cpmf_1_not_eq (μ : cdistr A) (a a' : A) :
    a ≠ a' → μ a = 1 → μ a' = 0.
  Proof.
    intros Hneq ->%cpmf_1_eq_dret. by apply cdret_0.
  Qed.

  Lemma cdret_mass (a : A) :
    SeriesCS (cdret a) = 1.
  Proof. rewrite SeriesCS_singleton //. Qed.
  
End cdret.

Lemma cdret_dret `{Countable A} (a : A) : cdret a = dret a.
Proof. apply cdistr_ext => ? //=. rewrite cdret_pmf_unfold distr_cdistr_eq dret_pmf_unfold. real_solver. Qed.

Section cdbind.
  Context {A B : Type}.
  Implicit Types (f : A → cdistr B) (μ : cdistr A) . 
  
  (** * Monadic bind  *)
  Definition cdbind_pmf (f : A → cdistr B) (μ : cdistr A) : B → R :=
    λ (b : B), SeriesCS (λ (a : A), μ a * f a b).

  Program Definition cdbind f μ : cdistr B :=
    MkCDistr (cdbind_pmf f μ) _ _ _ _.
  Next Obligation.
    intros. rewrite /cdbind_pmf.
    apply SeriesCS_ge_0; first real_solver.
    eapply (ex_seriesCS_le (g := λ a, μ a * 1)); [|by apply ex_seriesCS_scal_r].
    real_solver.
  Qed.
  Next Obligation.
    intros. rewrite /cdbind_pmf.
  Admitted.
  Next Obligation.
  Admitted.

  Lemma cdbind_unfold_pmf f μ (b : B):
    (cdbind f μ) b = SeriesCS (λ a : A, μ a * f a b).
  Proof. done. Qed.

  (* Program Definition dbind `{Countable A, Countable B} (f : A → distr B) (μ : distr A) : distr B :=
    MkDistr (dbind_pmf f μ) _ _ _.
  Next Obligation.
    intros ?????? f μ b. rewrite /dbind_pmf.
    apply SeriesC_ge_0.
    - real_solver.
    - eapply (ex_seriesC_le _ (λ a, μ a * 1)); [|by apply ex_seriesC_scal_r].
      real_solver.
  Qed.
  Next Obligation.
    intros ?????? f μ. rewrite /dbind_pmf.
    apply (distr_double_swap_ex f μ).
    eapply (ex_seriesC_ext (λ j, μ j * SeriesC (λ k, f j k))).
    { intros a. rewrite SeriesC_scal_l //. }
    apply (ex_seriesC_le _ (λ a : A, μ a * 1)); [|by apply ex_seriesC_scal_r].
    real_solver.
  Qed.
  Next Obligation.
    intros ?????? f μ. rewrite /dbind_pmf.
    rewrite distr_double_swap.
    rewrite -(SeriesC_ext (λ k, μ k * SeriesC (λ j, f k j))); last first.
    { intros a. rewrite SeriesC_scal_l //. }
    transitivity (SeriesC μ); [|done].
    eapply SeriesC_le; [|done].
    real_solver.
  Qed. *)
End cdbind.

Lemma cdbind_dbind `{Countable A, Countable B} (f : A -> cdistr B) (f' : A -> distr B) (μ : distr A) (b : B) : 
  (∀ a , f a = f' a) → 
  cdbind f μ b = dbind f' μ b.
Proof. intros. rewrite cdbind_unfold_pmf dbind_unfold_pmf SeriesCS_countable. apply SeriesCS_ext => ?. by rewrite distr_cdistr_eq H1. Qed.
(* 


Lemma dbind_pmf_ext `{Countable A, Countable B} (μ1 μ2 : distr A) (f g : A → distr B) (b1 b2 : B) :
  (∀ a b, f a b = g a b) →
  μ1 = μ2 →
  b1 = b2 →
  dbind f μ1 b1 = dbind g μ2 b2.
Proof.
  intros Hfg -> ->=>/=. rewrite /pmf /= /dbind_pmf.
  eapply SeriesC_ext=>a. rewrite Hfg //.
Qed.

Lemma dbind_ext_right `{Countable A, Countable B} (μ : distr A) (f g : A → distr B) :
  (∀ a, f a = g a) →
  dbind f μ = dbind g μ.
Proof.
  intro Heq.
  apply distr_ext=> a.
  apply dbind_pmf_ext; [|done|done].
  intros.
  rewrite Heq //.
Qed.

Lemma dbind_ext_right_strong `{Countable A, Countable B} (μ : distr A) (f g : A → distr B) :
  (∀ a, μ a > 0 -> f a = g a) →
  dbind f μ = dbind g μ.
Proof.
  intro Heq.
  apply distr_ext=> a.
  rewrite /dbind/dbind_pmf{1 4}/pmf.
  apply SeriesC_ext.
  intros n.
  pose proof pmf_pos μ n as [|<-]; last lra.
  by rewrite Heq.
Qed.

Lemma dbind_ext_right' `{Countable A, Countable B} (μ1 μ2 : distr A) (f g : A → distr B) :
  (∀ a, f a = g a) →
  μ1 = μ2 ->
  dbind f μ1 = dbind g μ2.
Proof.
  intros Heq ->.: A
  by apply dbind_ext_right.
Qed.

Lemma dbind_const `{Countable A, Countable B} (μ1:distr A) (μ2:distr B) :
  SeriesC μ1 = 1 ->
  dbind (λ _, μ2) μ1 = μ2.
Proof.
  intros Hmass. 
  apply distr_ext => b.
  rewrite /dbind/dbind_pmf{1}/pmf.
  rewrite SeriesC_scal_r Hmass.
  lra.
Qed. 

#[global] Instance Proper_dbind `{Countable A, Countable B} :
  Proper (pointwise_relation A (=) ==> (=) ==> (=)) (@dbind A _ _ B _ _).
Proof. intros ?? Hp ?? ->. f_equal. extensionality a. done. Qed.

(* TODO: generalize to distributions with countable support so that we can use
   the [stdpp] typeclasses *)
Notation "m ≫= f" := (dbind f m) (at level 60, right associativity) : stdpp_scope.
Notation "( m ≫=.)" := (λ f, dbind f m) (only parsing) : stdpp_scope.
Notation "(.≫= f )" := (dbind f) (only parsing) : stdpp_scope.
Notation "(≫=)" := (λ m f, dbind f m) (only parsing) : stdpp_scope.

Notation "x ← y ; z" := (y ≫= (λ x : _, z))
  (at level 20, y at level 100, z at level 200, only parsing) : stdpp_scope.

Notation "' x ← y ; z" := (y ≫= (λ x : _, z))
  (at level 20, x pattern, y at level 100, z at level 200, only parsing) : stdpp_scope.

(** * Lemmas about the interplay of monadic bind and return  *)
Section monadic.
  Context `{Countable A}.

  Lemma dret_id_right_pmf (μ : distr A) (a : A) :
    (a ← μ; dret a) a = μ a.
  Proof.
    rewrite {1}/pmf /= /dbind_pmf {2}/pmf /= /dret_pmf.
    rewrite (SeriesC_ext _ (λ a', if bool_decide (a' = a) then μ a else 0)).
    { rewrite SeriesC_singleton //. }
    real_solver.
  Qed.

  Lemma dret_id_right (μ : distr A) :
    (a ← μ; dret a) = μ.
  Proof. apply distr_ext, dret_id_right_pmf. Qed.

  Context `{Countable B}.

  Lemma dbind_unfold_pmf μ1 (μ2 : A -> distr B) (b : B):
    (μ1 ≫= μ2) b = SeriesC (λ a : A, μ1 a * μ2 a b).
  Proof.
    done.
  Qed.
  
  Lemma dret_id_left_pmf (f : A → distr B) (a : A) (b : B) :
    (a' ← dret a; f a') b = f a b.
  Proof.
    rewrite {1}/pmf /= /dbind_pmf {1}/pmf /= /dret_pmf.
    rewrite (SeriesC_ext _ (λ a', if bool_decide (a' = a) then f a b else 0)).
    { rewrite SeriesC_singleton //. }
    real_solver.
  Qed.

  Lemma dret_id_left (f : A → distr B) (a : A) :
    (a' ← dret a; f a') = f a.
  Proof. apply distr_ext, dret_id_left_pmf. Qed.

  Lemma dret_id_left' (f : A → distr B) (a : A) :
    (dret a ≫= f) = f a.
  Proof. apply distr_ext, dret_id_left_pmf. Qed.

  Lemma dret_const (μ : distr A) (b : B) :
    SeriesC μ = 1 →
    (a ← μ; dret b) = dret b.
  Proof.
    intro HSeries.
    apply distr_ext; intro a.
    rewrite {1}/pmf/=/dbind_pmf.
    rewrite SeriesC_scal_r HSeries; lra.
  Qed.

  Lemma dbind_dret_pmf_map (μ : distr A) (a : A) (f : A → B) `{Inj A B (=) (=) f} :
    (μ ≫= (λ a', dret (f a'))) (f a) = μ a.
  Proof.
    rewrite {1}/pmf /= /dbind_pmf {2}/pmf /= /dret_pmf.
    rewrite (SeriesC_ext _ (λ a', if bool_decide (a' = a) then μ a else 0)).
    { rewrite SeriesC_singleton //. }
    real_solver.
  Qed.

  Lemma dbind_dret_pmf_map_ne (μ : distr A) (b : B) (f : A → B) `{Inj A B (=) (=) f} :
    ¬ (∃ a, μ a > 0 ∧ f a = b) →
    (μ ≫= (λ a, dret (f a))) b = 0.
  Proof.
    intros Hnex.
    rewrite {1}/pmf /= /dbind_pmf {2}/pmf /= /dret_pmf.
    apply SeriesC_0.
    intros a'.
    case_bool_decide; [|lra].
    destruct (decide (μ a' > 0)) as [|Hn]; [exfalso; eauto|].
    apply pmf_eq_0_not_gt_0 in Hn as ->; lra.
  Qed.

  Lemma dbind_assoc_pmf `{Countable B'} (f : A → distr B) (g : B → distr B') (μ : distr A) c :
    (a ← μ ; b ← f a; g b) c = (b ← (a ← μ; f a); g b) c.
  Proof.
    rewrite !/pmf /= /dbind_pmf.
    assert (SeriesC (λ a, μ a * SeriesC (λ a0 : B, f a a0 * g a0 c)) =
            SeriesC (λ a, SeriesC (λ a0 : B, μ a * f a a0 * g a0 c))) as Heq1.
    { apply SeriesC_ext=> a.
      rewrite -SeriesC_scal_l.
      apply SeriesC_ext; real_solver. }
    rewrite Heq1.
    rewrite -(fubini_pos_seriesC (λ '(a ,a0), μ a * f a a0 * g a0 c)).
    - apply SeriesC_ext=> b.
      rewrite {4}/pmf /= /dbind_pmf.
      rewrite -SeriesC_scal_r //.
    - real_solver.
    - intro; apply (ex_seriesC_le _ (f a)); [|done].
      real_solver.
    - setoid_rewrite Rmult_assoc.
      setoid_rewrite SeriesC_scal_l.
      apply (ex_seriesC_le _ μ); [|done].
      intro; split.
      + apply Rmult_le_pos; [done|].
        apply SeriesC_ge_0'=> b. real_solver.
      + transitivity (μ n * (SeriesC (f n))).
        * apply Rmult_le_compat; [done| |done|].
          -- apply SeriesC_ge_0'=>b. real_solver.
          -- apply SeriesC_le; [|done]. real_solver.
        * real_solver.
  Qed.

  Lemma dbind_assoc `{Countable B'} (f : A → distr B) (g : B → distr B') (μ : distr A) :
    (a ← μ ; b ← f a; g b) = (b ← (a ← μ; f a); g b).
  Proof. apply distr_ext, dbind_assoc_pmf. Qed.

  Lemma dbind_assoc' `{Countable B'} (f : A → distr B) (g : B → distr B') (μ : distr A) :
    μ ≫= (λ a, f a ≫= g) = (μ ≫= f) ≫= g.
  Proof. rewrite dbind_assoc //. Qed.

  Lemma dbind_comm `{Countable B'} (f : A → B → distr B') (μ1 : distr A) (μ2 : distr B):
    (a ← μ1 ; b ← μ2; f a b) = (b ← μ2; a ← μ1; f a b).
  Proof.
    apply distr_ext=> b'. rewrite /pmf/=/dbind_pmf.
    erewrite SeriesC_ext; last first.
    { intro; rewrite {2}/pmf/=/dbind_pmf/=.
      rewrite -SeriesC_scal_l //. }
    symmetry.
    erewrite SeriesC_ext; last first.
    { intro b; rewrite {2}/pmf/=/dbind_pmf/=.
      rewrite -SeriesC_scal_l.
      setoid_rewrite <-Rmult_assoc at 1.
      setoid_rewrite (Rmult_comm (μ2 _) (μ1 _)) at 1.
      setoid_rewrite Rmult_assoc at 1.
      done. }
    apply (fubini_pos_seriesC (λ '(a, b), μ1 a * (μ2 b * f a b b'))).
    - real_solver.
    - intros a.
      apply (ex_seriesC_le _ μ2); [|done].
      real_solver.
    - apply (ex_seriesC_le _ μ1); [|done].
      intro a; split.
      + apply SeriesC_ge_0'=> b. real_solver.
      + rewrite SeriesC_scal_l.
        rewrite -{2}(Rmult_1_r (μ1 _)).
        apply Rmult_le_compat; [done| |done|].
        * apply SeriesC_ge_0'=> b. real_solver.
        * apply (Rle_trans _ (SeriesC μ2)); [|done].
          apply SeriesC_le; [|done].
          real_solver.
   Qed.

  Lemma dbind_pos (f : A → distr B) (μ : distr A) (b : B) :
    dbind f μ b > 0 ↔ ∃ a, f a b > 0 ∧ μ a > 0.
  Proof.
    rewrite {1}/pmf /= /dbind_pmf. split.
    - eapply contrapositive. intros Hna.
      assert (∀ a, μ a * f a b = 0) as Hz.
      { intros a.
        pose proof (not_exists_forall_not _ _ Hna a) as [Hne | Hne]%not_and_or_not.
        - pose proof (pmf_pos (f a) b). assert (f a b = 0) as ->; lra.
        - pose proof (pmf_pos μ a). assert (μ a = 0) as ->; lra. }
      apply Rge_not_gt. rewrite SeriesC_0 //.
    - intros (a & Hf & Hμ). eapply Rlt_gt.
      eapply (Rlt_le_trans _ (SeriesC (λ a', if bool_decide (a' = a) then μ a * f a b else 0))).
      { rewrite SeriesC_singleton. real_solver. }
      eapply SeriesC_le.
      + real_solver.
      + apply (ex_seriesC_le _ (λ a : A, μ a * 1)); [|by apply ex_seriesC_scal_r].
        real_solver.
  Qed.

  Lemma dbind_eq (f g : A → distr B) (μ1 μ2 : distr A) :
    (∀ a, μ1 a > 0 → f a = g a) →
    (∀ a, μ1 a = μ2 a) →
    dbind f μ1 = dbind g μ2.
  Proof.
    intros Heq Hμ.
    eapply distr_ext. intros b.
    rewrite /pmf /= /dbind_pmf. eapply SeriesC_ext.
    intros a. rewrite -Hμ.
    destruct (decide (μ1 a > 0)) as [|Hngt].
    { rewrite Heq //. }
    apply pmf_eq_0_not_gt_0 in Hngt as ->.
    lra.
  Qed.

  Lemma dbind_inhabited (f : A → distr B) (μ : distr A) :
    SeriesC μ > 0 →
    (∀ a, SeriesC (f a) > 0) →
    SeriesC (dbind f μ) > 0.
  Proof.
    intros Hμ Hf.
    rewrite /pmf /= /dbind_pmf.
    rewrite (distr_double_swap f μ).
    setoid_rewrite SeriesC_scal_l.
    apply Rlt_gt. rewrite -(SeriesC_0 (λ _ : A, 0)); [|done].
    eapply SeriesC_lt.
    - real_solver.
    - apply SeriesC_gtz_ex in Hμ as [a Ha]; [|done].
      exists a. real_solver.
    - eapply pmf_ex_seriesC_mult_fn. eauto.
  Qed.


  Lemma dbind_inhabited_ex (f : A → distr B) (μ : distr A) :
    (exists a, μ a > 0 /\ SeriesC (f a) > 0) →
    SeriesC (dbind f μ) > 0.
  Proof.
    intros [a [Ha1 Ha2]].
    rewrite /pmf /= /dbind_pmf.
    rewrite (distr_double_swap f μ).
    setoid_rewrite SeriesC_scal_l.
    apply Rlt_gt. rewrite -(SeriesC_0 (λ _ : A, 0)); [|done].
    eapply SeriesC_lt.
    - real_solver.
    - exists a. nra.
    - eapply pmf_ex_seriesC_mult_fn. eauto.
  Qed.

  Lemma dbind_dret_pair_left `{Countable A'}
    (μ : distr A) (a' : A') (b : A) :
    (μ ≫= (λ a, dret (a, a'))) (b, a') = μ b.
  Proof.
    rewrite {1}/pmf/=/dbind_pmf.
    erewrite SeriesC_ext; [apply SeriesC_singleton'|].
    intros a. rewrite {2}/pmf/=/dret_pmf.
    real_solver.
  Qed.

  Lemma dbind_dret_pair_right `{Countable A'}
    (μ : distr A') (a : A) (b : A') :
    (μ ≫= (λ a', dret (a, a'))) (a, b) = μ b.
  Proof.
    rewrite {1}/pmf/=/dbind_pmf.
    erewrite SeriesC_ext; [apply SeriesC_singleton'|].
    intro. rewrite {2}/pmf/=/dret_pmf.
    real_solver.
  Qed.

  Lemma dbind_mass (μ : distr A) (f : A → distr B) :
    SeriesC (μ ≫= f) = SeriesC (λ a, μ a * SeriesC (f a)).
  Proof.
    rewrite {1}/pmf /= /dbind_pmf.
    rewrite distr_double_swap.
    eapply SeriesC_ext. intros. rewrite SeriesC_scal_l //.
  Qed.

  Lemma dbind_det (μ : distr A) (f : A → distr B) :
    SeriesC μ = 1 →
    (∀ a, μ a > 0 → SeriesC (f a) = 1) →
    SeriesC (μ ≫= f) = 1.
  Proof.
    intros Hμ Hf.
    rewrite {1}/pmf /= /dbind_pmf.
    rewrite dbind_mass.
    rewrite -Hμ.
    eapply SeriesC_ext => a.
    destruct (decide (μ a > 0)) as [Hgt | ->%pmf_eq_0_not_gt_0]; [|lra].
    rewrite Hf //. lra.
  Qed.

  Lemma dbind_det_inv_l (μ1 : distr A) (f : A → distr B) (b : B) :
    (μ1 ≫= f) b = 1 →
    SeriesC μ1 = 1.
  Proof.
    rewrite {1}/pmf /= /dbind_pmf.
    intros Hbind.
    apply Rle_antisym; [done|].
    rewrite -Hbind.
    apply SeriesC_le; [|done].
    real_solver.
  Qed.

  Lemma dbind_det_inv_r (μ1 : distr A) (f : A → distr B) (b : B) :
    (μ1 ≫= f) b = 1 →
    (∀ a, μ1 a > 0 → f a b = 1).
  Proof.
    rewrite {1}/pmf /= /dbind_pmf.
    intros Hbind a Ha.
    assert (SeriesC (λ a', μ1 a' * (if bool_decide (a' = a) then 1 else f a' b )) =
            SeriesC (λ a' : A, μ1 a' * f a' b)) as Haux.
    { apply Rle_antisym.
      - rewrite Hbind.
        transitivity (SeriesC μ1); [|done].
        apply SeriesC_le; [|done].
        real_solver.
      - apply SeriesC_le.
        + real_solver.
        + apply (ex_seriesC_le _ μ1); [|done]. real_solver. }
    rewrite (SeriesC_split_elem _ a) in Haux; first last.
    - apply (ex_seriesC_le _ μ1); [|done]. real_solver.
    - real_solver.
    - rewrite (SeriesC_split_elem (λ a', μ1 a' * f a' b) a) in Haux; first last.
      + apply (ex_seriesC_le _ μ1); [|done]. real_solver.
      + real_solver.
      + (* We do this kind of rewrite often enough that it could be a lemma *)
        assert (SeriesC (λ a0 : A, if bool_decide (a0 = a) then μ1 a0 * f a0 b else 0)
              = SeriesC (λ a0 : A, if bool_decide (a0 = a) then μ1 a * f a b else 0)) as Hrw1.
        { apply SeriesC_ext. real_solver. }
        rewrite Hrw1 in Haux.
        rewrite SeriesC_singleton in Haux.
        assert (SeriesC (λ a0 : A, if bool_decide (a0 = a) then μ1 a0 * (if bool_decide (a0 = a) then 1 else f a0 b) else 0) =
                SeriesC (λ a0 : A, if bool_decide (a0 = a) then μ1 a else 0)) as Hrw2.
        { apply SeriesC_ext; real_solver. }
        rewrite Hrw2 in Haux.
        rewrite SeriesC_singleton in Haux.
        assert (SeriesC (λ a0 : A, if bool_decide (a0 ≠ a) then μ1 a0 * (if bool_decide (a0 = a) then 1 else f a0 b) else 0) =
                SeriesC (λ a0 : A, if bool_decide (a0 ≠ a) then μ1 a0 * f a0 b else 0)) as Hrw3.
        { apply SeriesC_ext; real_solver. }
        rewrite Hrw3 in Haux.
        real_solver.
  Qed.

End monadic.

Section probabilities.
  Context `{Countable A}.
  Implicit Types μ d : distr A.

  Definition prob (μ : distr A) (P : A → bool) : R :=
    SeriesC (λ a : A, if (P a) then μ a else 0).

  Lemma prob_le_1 (μ : distr A) (P : A → bool) :
    prob μ P <= 1.
  Proof.
    transitivity (SeriesC μ); [|done].
    apply SeriesC_le; [|done].
    real_solver.
  Qed.

  Lemma prob_ge_0 (μ : distr A) (P : A → bool) :
    0 <= prob μ P.
  Proof. apply SeriesC_ge_0'=> a. real_solver. Qed.

End probabilities.

Section probability_lemmas.
  Context `{Countable A}.

  Lemma prob_dret_true (a : A) (P : A → bool) :
    P a = true → prob (dret a) P = 1.
  Proof.
    intro HP.
    rewrite /prob/pmf/=/dret_pmf/=.
    erewrite SeriesC_ext; [apply SeriesC_singleton|].
    real_solver.
  Qed.

  Lemma prob_dret_false (a : A) (P : A → bool) :
    P a = false → prob (dret a) P = 0.
  Proof.
    intro HP.
    rewrite /prob/pmf/=/dret_pmf/=.
    apply SeriesC_0. real_solver.
  Qed.

  Lemma prob_dbind `{Countable B} (μ : distr A) (f : A → distr B) (P : B → bool) :
    prob (dbind f μ) P = SeriesC (λ a, μ a * prob (f a) P).
  Proof.
    rewrite /prob{1}/pmf/=/dbind_pmf/=.
    assert (∀ a,
               (if P a then SeriesC (λ a0 : A, μ a0 * f a0 a) else 0) =
                 SeriesC (λ a0 : A, if P a then μ a0 * f a0 a else 0)) as Haux.
    {intro a. destruct (P a); [done|]. rewrite SeriesC_0 //. }
    setoid_rewrite Haux.
    rewrite -(fubini_pos_seriesC (λ '(a, a0), if P a then μ a0 * f a0 a else 0)).
    - apply SeriesC_ext=> a.
      rewrite -SeriesC_scal_l.
      apply SeriesC_ext; intro b.
      real_solver.
    - real_solver.
    - intro b.
      apply (ex_seriesC_le _ μ); [|done].
      real_solver.
    - apply (ex_seriesC_le _ (λ a : B, SeriesC (λ b : A, μ b * f b a))).
      + intro b; split.
        * apply SeriesC_ge_0'. real_solver.
        * apply SeriesC_le; [real_solver|].
          apply pmf_ex_seriesC_mult_fn.
          exists 1. real_solver.
      + apply (pmf_ex_seriesC (dbind f μ)).
  Qed.



  Lemma union_bound (μ : distr A) (P Q : A → bool) :
    prob μ (λ a, orb (P a) (Q a)) <= prob μ P + prob μ Q.
  Proof.
    rewrite /prob.
    rewrite -SeriesC_plus.
    - apply SeriesC_le.
      + intro n.
        pose proof (pmf_pos μ n).
        destruct (P n); destruct (Q n); real_solver.
      + apply (ex_seriesC_le _ (λ x, 2 * μ x)).
        * intro n.
          pose proof (pmf_pos μ n).
          destruct (P n); destruct (Q n); real_solver.
        * by apply ex_seriesC_scal_l.
    - by apply ex_seriesC_filter_bool_pos.
    - by apply ex_seriesC_filter_bool_pos.
  Qed.

End probability_lemmas. *)

Definition cdprod {A B} (μ1 : cdistr A) (μ2 : cdistr B) : cdistr (A * B) :=
  cdbind (λ a, cdbind (λ b, cdret (a, b)) μ2) μ1.

Lemma cdprod_pmf {A B} (μ1 : cdistr A) (μ2 : cdistr B) a b :
  cdprod μ1 μ2 (a, b) = μ1 a * μ2 b.
Proof.
Admitted.

Section dprod.
  Context {A B : Type}.
  Variable (μ1 : cdistr A) (μ2 : cdistr B).

  Lemma cdprod_pos (a : A) (b : B) :
    cdprod μ1 μ2 (a, b) > 0 ↔ μ1 a > 0 ∧ μ2 b > 0.
  Proof.
    rewrite cdprod_pmf /=.
    split; [|real_solver].
    destruct (decide (μ1 a > 0)) as [| ->%cpmf_eq_0_not_gt_0]; [|lra].
    destruct (decide (μ2 b > 0)) as [| ->%cpmf_eq_0_not_gt_0]; [|lra].
    done.
  Qed.

  Lemma dprod_mass :
    SeriesCS (cdprod μ1 μ2) = SeriesCS μ1 * SeriesCS μ2.
  Proof.
  Admitted.
  (*   rewrite {1}(SeriesC_ext _ (λ '(a, b), μ1 a * μ2 b)); last first.
    { intros [a' b']. rewrite dprod_pmf //. }
    rewrite distr_double_lr.
    erewrite SeriesC_ext; [|intro; rewrite SeriesC_scal_l //].
    rewrite SeriesC_scal_r //.
  Qed. *)

End dprod.

Section exp_val.

  Context {A : Type}.
  Implicit Types μ : cdistr A.
  Implicit Types f : A -> R.

  Definition ex_expvalC μ f :=
    ex_seriesCS (λ a, μ a * f a).

  Definition ExpvalC μ f :=
    SeriesCS (λ a, μ a * f a).

End exp_val.