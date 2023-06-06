(* A small self-contained definition of groups and Clutch implementations of
   groups. *)


From clutch.program_logic Require Import weakestpre.
From clutch.prob_lang Require Import spec_ra notation proofmode primitive_laws spec_tactics locations lang.
From clutch.logrel Require Import model rel_rules rel_tactics adequacy.
From clutch.typing Require Import types.
From clutch.prelude Require Import base.
Set Default Proof Using "Type*".


Class group_struct t :=
  { e : t ; inv : t → t ; mult : t → t → t }.

Class is_group `{G : group_struct} :=
  { _ : Assoc (=) mult
  ; _ : LeftId (=) e mult
  ; _ : RightId (=) e mult
  ; _ : ∀ x, mult x (inv x) = e
  ; _ : ∀ x, mult (inv x) x = e
  }.

Definition exp `{G : group_struct t} (b : t) (k : Z) :=
  match k with
  | Zneg _ =>
      let n := Z.abs_nat k in
      inv (PeanoNat.Nat.iter n
             (λ r, mult b r) e)
  | 0%Z => e
  | Zpos p =>
      let n := Z.abs_nat k in
      (PeanoNat.Nat.iter n (λ r, mult b r) e)
  end.

Definition is_generator `{G : group_struct T} (g : T) :=
  forall a, { n : nat & a = exp g n}%type.

Definition cyclic `{G : group_struct T} := {g & is_generator g}.

Section EGroupDef.
  Context `{!clutchRGS Σ}.
  (* TODO: landing in Prop is annoying because when defining the group
  operations we want to eliminate back into Set; when is that legal? *)
  Context `{P : ! val → Prop}.
  (* We restrict implementations of groups to work over a syntactic type τ with
  respect to which the operations are well-typed. This is not strictly
  necessary in order to define the rest of the interface, but it has the
  advantage that we can use reflexivity of the logical relation when
  appropriate. *)
  Context {typ : type}.
  (* The semantic type of group elements is the subset of values satisfying P. *)
  Definition vt := {v : val | P v}.
  (* The group implementation is defined with respect to a semantic group on
  vt. *)
  Context `{G : !group_struct vt}.
  (* we don't actually care whether G satisfies the group laws *)
  (* Context `{G_group : !@is_group vt G}. *)
  Coercion vvt := (λ x, `x) : vt → val.
  (* Are all of these needed? *)
  Coercion evt := λ (x : vt), of_val (vvt x).
  Coercion inG := (fun (G : group_struct vt) => vt).

  Definition is_id (v : vt) := v = e.

  Definition is_inv (i : val) := ∀ (x : vt),
    {{{ True }}}
      i x
    {{{ v, RET v; ⌜vvt (inv x) = v⌝ }}}.

  Definition is_mult (m : val) := ∀ (x y : vt),
    {{{ True }}}
      m x y
    {{{ v, RET v; ⌜v = vvt (mult x y)⌝ }}}.

  Record egroup_laws vid vinv vmult :=
      { is_id_eid : is_id vid
      ; is_inv_einv : is_inv vinv
      ; is_mult_emult : is_mult vmult
      }.

  Definition is_id' (v : val) := forall (p : P v), (v↾p) = e.

  Lemma is_id_id' v : is_id v <-> is_id' v.
  Proof.
    rewrite /is_id /is_id'. split.
    all: intuition (auto; subst) ; unfold vvt in *.
    - rewrite (proof_irrelevance _ p (proj2_sig e)).
      by rewrite -sig_eta.
    - destruct v. rewrite (H _). done.
  Qed.

  Definition is_mult' (m : val) :=
    ∀ (x y : val) (p : P x) (q : P y),
      (⊢ {{{ ⌜True⌝ }}}
           m x y
           {{{ v, RET v; ⌜v = vvt (mult (x ↾ p) (y ↾ q))⌝ }}}).

  Lemma is_mult_mult' (m : val) :
    is_mult m <-> is_mult' m.
  Proof.
    unfold is_mult, is_mult' ; split.
    - intro H ; intros.
      iIntros (?) "_ !> Hlog".
      iApply (H (x ↾ p) (y ↾ q)) => //.
    - intro H ; intros.
      iIntros "_ Hlog".
      iApply (H _ _ (proj2_sig x) (proj2_sig y)) => //.
      by rewrite -?sig_eta.
  Qed.

  Definition is_inv' (i : val) := ∀ (x : val) (p : P x),
    {{{ True }}}
      i x
    {{{ v, RET v; ⌜vvt (inv (x ↾ p)) = v⌝ }}}.

  Lemma is_inv_inv' (m : val) :
    is_inv m <-> is_inv' m.
  Proof.
    unfold is_inv, is_inv'. split.
    - intro H ; intros.
      iIntros "_ Hlog".
      iApply (H (x ↾ p)) => //.
    - intro H ; intros.
      iIntros "_ Hlog".
      iApply (H _ (proj2_sig x)) => //.
      by rewrite -?sig_eta.
  Qed.

  Definition is_exp (eexp : val) := ∀ (b : vt) (x : Z),
      {{{ True }}}
        eexp b (#x)
        {{{ v, RET v; ⌜v = vvt (@exp _ G b x)⌝ }}}.
  Definition is_spec_exp (eexp : val) := ∀ (b : vt) (x : Z),
    ∀ K, refines_right K (eexp b (#x))
         ={⊤}=∗
         refines_right K (vvt (@exp _ G b x)).

  Definition is_egroup e i m := is_id e /\ is_inv i /\ is_mult m.
End EGroupDef.

Class EGroup `{!clutchRGS Σ} :=
  { P : val -> Prop
  ; G : group_struct (@vt P)
  ; vid : vt
  ; vinv : val
  ; vmult : val
  ; laws : @egroup_laws _ _ P G vid vinv vmult
  }.

Section EZ2.
  Context `{!clutchRGS Σ}.

Definition Z2 := {z : nat | (z < 2)}.
Instance Z2_group_struct : group_struct Z2.
Proof.
  constructor.
  - unshelve econstructor.
    + exact 0.
    + lia.
  - intros [z hz].
    exists ((2-z) `mod` 2).
    apply Nat.mod_upper_bound. done.
  - intros [x hx].
    intros [y hy].
    exists ((x + y) `mod` 2).
    apply Nat.mod_upper_bound. done.
Defined.

Lemma Z2_set (x y : Z2) : `x = `y → x = y.
  apply eq_sig_hprop.
  intros.
  apply Nat.lt_pi.
Qed.

Instance Z2_group : @is_group Z2 Z2_group_struct.
Proof.
  constructor.
  - intros [x hx] [y hy] [z hz].
    apply Z2_set.
    rewrite /proj1_sig.
    rewrite /mult. rewrite /Z2_group_struct.
    rewrite PeanoNat.Nat.add_mod_idemp_r => //.
    rewrite PeanoNat.Nat.add_mod_idemp_l => //.
    rewrite assoc. done.
  - intros [x hx].
    apply Z2_set.
    rewrite /proj1_sig.
    rewrite /e /mult. rewrite /Z2_group_struct.
    by apply PeanoNat.Nat.mod_small.
  - intros [x hx].
    apply Z2_set.
    rewrite /proj1_sig.
    rewrite /e /mult. rewrite /Z2_group_struct.
    replace (x + 0) with x by lia.
    by apply PeanoNat.Nat.mod_small.
  - intros [x hx].
    apply Z2_set.
    rewrite /proj1_sig.
    rewrite /e /mult /inv. rewrite /Z2_group_struct.
    rewrite PeanoNat.Nat.add_mod_idemp_r => //.
    replace (x + (2 - x)) with 2 by lia.
    done.
  - intros [x hx].
    apply Z2_set.
    rewrite /proj1_sig.
    rewrite /e /mult /inv. rewrite /Z2_group_struct.
    rewrite PeanoNat.Nat.add_mod_idemp_l => //.
    replace (2 - x + x) with 2 by lia.
    done.
Qed.

Definition PZ2 v := exists n : nat, v = #n /\ n < 2.
Definition EZ2 := {v : val | PZ2 v}.
Instance EZ2_group_struct : group_struct EZ2.
Proof.
  constructor.
  - unshelve econstructor.
    + exact #0.
    + unfold PZ2. exists 0. auto with lia.
  - intros (?&Hn).
    unfold PZ2 in Hn.
    pose proof (epsilon Hn) as n.
    pose proof (epsilon_correct _ Hn).
    (* destruct n. *)
    (* intros (?&n&->&hn). *)
    unfold EZ2.
    exists #((2-n) `mod` 2)%nat.
    unfold PZ2.
    exists (((2 - n) `mod` 2)).
    split => //.
    apply Nat.mod_upper_bound. done.
  - (* intros (?&x&->&hx). *)
    (* intros (?&y&->&hy). *)
    intros (x&hx) (y&hy).
    pose proof (epsilon hx) as nx.
    pose proof (epsilon hy) as ny.
    unfold EZ2, PZ2.
    exists #((nx + ny) `mod` 2)%nat.
    exists ((nx + ny) `mod` 2)%nat.
    split => //.
    apply Nat.mod_upper_bound. done.
Defined.

(* Lemma EZ2_set (x y : EZ2) : `x = `y → x = y. *)
(*   intros h. *)
(*   unfold EZ2, PZ2 in x,y. *)

(*   unshelve eapply (eq_sig_hprop _ _ _ h). *)
(*   intros v p q. *)
(*   unfold PZ2 in p,q. *)

(*   unshelve eapply (eq_ex_hprop _ _ _) ; last first. *)
(*   (* unshelve eapply eq_sig. *) *)
(*   - destruct p as [n [en hn]] eqn:hp. *)
(*     destruct q as [k [ek hk]] eqn:hq. *)
(*     assert (n = k) as hnk. *)
(*     { clear hq hp. subst. inversion ek as [enk]. *)
(*       by apply Nat2Z.inj in enk. *)
(*     } *)
(*     simpl. *)
(*     exact hnk. *)
(*   - simpl. intros n p' q'. *)
(*     (* apply eq_sig_uncurried. *) *)
(*     destruct p' as [en hn]. *)
(*     destruct q' as [en' hn']. *)
(*     subst. *)
(*     f_equal. *)
(*     2: apply Nat.lt_pi. *)
(*     clear -en'. *)
(*     epose val_eq_dec. *)
(*     unfold EqDecision, Decision in X. *)
(*     by apply Eqdep_dec.UIP_dec. *)
(* Qed. *)

Definition emodulo : val :=
  rec: "mod" "x" "y" :=
    if: "x" < "y" then
      "x"
    else
      "mod" ("x" - "y") "y"
.


Definition ee : EZ2.            (* EZ2_group_struct *)
Proof.
  exists #0.
  unfold PZ2. exists 0. auto with lia.
Defined.

Definition einv : val :=
  λ:"x", emodulo (#2 - "x") #2.
Definition emult : val :=
  λ:"x" "y", emodulo ("x" + "y") #2.

Lemma mod_correct Φ : ∀ (x y : Z),
    (∀ (v : val), ⌜#(x `mod` y) = v⌝ -∗ Φ v)
    -∗
    WP emodulo #x #y {{ v, Φ v }}.
Proof.
  iIntros (??) "Hlog".
Admitted.

Lemma EZ2_group : @is_egroup Σ _ PZ2 EZ2_group_struct
                    ee einv emult.
Proof.
  do 2 constructor.
  - apply (@is_inv_inv' Σ _ PZ2 EZ2_group_struct einv).
    rewrite /PZ2 /einv /is_inv'.
    iIntros (x p Φ) "_ H".
    wp_pure.
    rewrite /inv /EZ2_group_struct => /=.
    replace (1 - _) with ((2 - epsilon p) `mod` 2) => //.
    destruct (epsilon_correct _ p) as [H He].
    replace (Val x) with (Val #(epsilon p)) by by destruct H.
    wp_pures.
    iApply (mod_correct Φ (2 - Z.of_nat (epsilon p))%Z 2%Z).
    iIntros (v) "%hv".
    iSpecialize ("H" $! v).
    rewrite -hv.
    iApply "H".
    iPureIntro.
    repeat f_equal.
    set (n := epsilon p).
    clear -He.
    rewrite Nat2Z.inj_mod.
    f_equal.
    lia.
  - apply (@is_mult_mult' _ _ PZ2 EZ2_group_struct emult).
    rewrite /PZ2 /emult /is_mult'.
    iIntros (x y p q Φ) "!> _ H".
    wp_pures.
    rewrite /mult /EZ2_group_struct => /=.
    replace (1 - _) with ((epsilon p + epsilon q) `mod` 2) => //.
    destruct (epsilon_correct _ p) as [H Hp].
    destruct (epsilon_correct _ q) as [H' Hq].
    replace (Val x) with (Val #(epsilon p)) by by destruct H.
    replace (Val y) with (Val #(epsilon q)) by by destruct H'.
    wp_pures.
    iApply (mod_correct Φ _ 2%Z).
    iIntros (v) "%hv".
    iSpecialize ("H" $! v).
    rewrite -hv.
    iApply "H".
    iPureIntro.
    repeat f_equal.
    set (n := epsilon p).
    set (m := epsilon q).
    clear.
    rewrite Nat2Z.inj_mod.
    f_equal.
    lia.
Qed.

Definition G_EZ2 : EGroup.
  econstructor.
  destruct EZ2_group as [hid [hinv hmult]].
  constructor ; eassumption.
Defined.

End EZ2.
