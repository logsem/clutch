From iris.proofmode Require Import base proofmode classes.
From iris.algebra.lib Require Import dfrac_agree.
From iris.base_logic.lib Require Import na_invariants.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode
  spec_rules spec_ra class_instances.
From clutch.prob_eff_lang.probblaze Require Import tactics.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_judgement sem_def.
From clutch.prob_eff_lang.probblaze.examples.secure_add Require Import secure_add_bijection.
From iris.bi Require Import monpred.
From iris.proofmode Require Import monpred.
From clutch.prob_eff_lang.probblaze.examples.secure_add3 Require Import
  add3_def add3_tbl add3_net.
From clutch.prob_eff_lang.probblaze.eq Require Import eq_logic eq_valgroup eq_handlers eq_compat.

Import fingroup.
Import fingroup.fingroup.
Import valgroup_notation.
Import valgroup_tactics.

(** * Write-once ghost slots

    A slot is allocated empty (with a token) and later set, once, to a
    value; afterwards everybody can know its value. *)

Section slots.
  Context `{!probblazeRGS Σ, !inG Σ (dfrac_agreeR valO)}.

  Definition slot_tok (γ : gname) : iProp Σ := ∃ v, own γ (to_dfrac_agree (DfracOwn 1) v).
  Definition slot (γ : gname) (v : val) : iProp Σ := own γ (to_dfrac_agree DfracDiscarded v).

  Global Instance slot_persistent γ v : Persistent (slot γ v).
  Proof. apply _. Qed.
  Global Instance slot_timeless γ v : Timeless (slot γ v).
  Proof. apply _. Qed.
  Global Instance slot_tok_timeless γ : Timeless (slot_tok γ).
  Proof. apply _. Qed.

  Lemma slot_alloc : ⊢ |==> ∃ γ, slot_tok γ.
  Proof.
    iMod (own_alloc (to_dfrac_agree (DfracOwn 1) #()%V)) as (γ) "H"; first done.
    by iExists γ, _.
  Qed.

  Lemma slot_set γ v : slot_tok γ ==∗ slot γ v.
  Proof.
    iIntros "[%w H]". iApply (own_update with "H").
    by apply cmra_update_exclusive.
  Qed.

  Lemma slot_agree γ v w : slot γ v -∗ slot γ w -∗ ⌜v = w⌝.
  Proof.
    iIntros "H1 H2". iCombine "H1 H2" gives %Hv.
    by apply dfrac_agree_op_valid_L in Hv as [_ ?].
  Qed.

  Lemma slot_tok_excl γ v : slot_tok γ -∗ slot γ v -∗ False.
  Proof.
    iIntros "[%w H1] H2". iCombine "H1 H2" gives %Hv.
    apply dfrac_agree_op_valid_L in Hv as [Hv _]. done.
  Qed.

End slots.

(** * Group identities *)

Section algebra.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  Local Open Scope group_scope.

  Lemma mulgAC (a b d : vgG) : a * b * d = a * d * b.
  Proof using All. by rewrite -mulgA (vgG_comm b d) mulgA. Qed.

  Lemma mulgCA (a b d : vgG) : a * (b * d) = b * (a * d).
  Proof using All. by rewrite !mulgA (vgG_comm a b). Qed.

  (* [h]'s sum in the simulation: dummy input, [h']'s share shifted. *)
  Lemma sum_h_alg (x x' a b u v : vgG) :
    1 * (a * (1 * b))^-1 * (x'^-1 * u) * v = (x * x')^-1 * (x * (a * b)^-1 * u * v).
  Proof using All.
    rewrite !mul1g !invMg -!mulgA mulKg.
    by rewrite (mulgCA a^-1) (mulgCA b^-1).
  Qed.

  (* [h']'s sum in the simulation: dummy input, its share to [h] shifted. *)
  Lemma sum_h'_alg (x a b u v : vgG) :
    1 * (a * (x^-1 * b))^-1 * u * v = x * (a * b)^-1 * u * v.
  Proof using All.
    rewrite !mul1g !invMg invgK -!mulgA.
    by rewrite (mulgCA b^-1).
  Qed.

  (* The three sums multiply to the product of the inputs. *)
  Lemma sums_alg (x xp xq rip riq rpi rqi rpq rqp : vgG) :
    x * (rip * riq)^-1 * rpi * rqi *
    (xp * (rpq * rpi)^-1 * rqp * rip) *
    (xq * (rqi * rqp)^-1 * riq * rpq) = x * xp * xq.
  Proof using All.
    rewrite !invMg -!mulgA.
    (* pull out the inputs *)
    rewrite (mulgCA rqi xp) (mulgCA rpi xp) (mulgCA rip^-1 xp) (mulgCA riq^-1 xp).
    do 2 f_equal.
    rewrite !(mulgCA _ xq).
    transitivity (xq * 1); [|by rewrite mulg1]. f_equal.
    (* the samples cancel pairwise *)
    rewrite !(mulgCA _ riq) mulKVg !(mulgCA _ rip) mulKVg !(mulgCA _ rpi^-1) mulKVg mulKg.
    by rewrite !(mulgCA _ rqi^-1) mulKg mulVg.
  Qed.

End algebra.

(** * What the parties know, and how the two worlds' messages relate *)

Section party_defs.
  Context `{!probblazeRGS Σ, !inG Σ (dfrac_agreeR valO)}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.

  (* The corrupt party [c], the honest party [h] whose sum to [c] the
     simulator patches, and the other honest party [h']. *)
  Context (c : nat) (Hc : (c < 3)%nat).
  Local Open Scope Z_scope.
  Definition cz : Z := Z.of_nat c.
  Definition hz : Z := Z.of_nat (hon c).
  Definition hz' : Z := Z.of_nat ((c + 2) mod 3).

  (* The peers of party [i], as computed by [party]. *)
  Definition nxt (i : Z) : Z := Z.rem (i + 1) 3.
  Definition nxt2 (i : Z) : Z := Z.rem (i + 2) 3.

  (** Index arithmetic. *)
  Lemma roles_spec :
    nxt cz = hz ∧ nxt2 cz = hz' ∧ nxt hz = hz' ∧ nxt2 hz = cz ∧ nxt hz' = cz ∧ nxt2 hz' = hz ∧
    hz ≠ cz ∧ hz' ≠ cz ∧ hz' ≠ hz ∧ 0 ≤ cz < 3 ∧ 0 ≤ hz < 3 ∧ 0 ≤ hz' < 3.
  Proof using Hc.
    rewrite /nxt /nxt2 /hz /hz' /cz /hon.
    destruct c as [|[|[|c']]]; [simpl; repeat split; done.. | lia].
  Qed.

  Lemma nxt_spec (i : Z) : 0 ≤ i < 3 →
    0 ≤ nxt i < 3 ∧ 0 ≤ nxt2 i < 3 ∧ nxt i ≠ i ∧ nxt2 i ≠ i ∧ nxt2 i ≠ nxt i ∧
    nxt (nxt i) = nxt2 i ∧ nxt2 (nxt i) = i ∧ nxt (nxt2 i) = i ∧ nxt2 (nxt2 i) = nxt i.
  Proof using.
    rewrite /nxt /nxt2. intros Hi.
    assert (i = 0 ∨ i = 1 ∨ i = 2) as [ -> | [ -> | -> ] ] by (clear -Hi; lia); simpl; repeat split; done.
  Qed.

  Lemma roles_cases (i : Z) : 0 ≤ i < 3 → i = cz ∨ i = hz ∨ i = hz'.
  Proof using Hc.
    rewrite /hz /hz' /cz /hon. intros Hi.
    destruct c as [|[|[|c']]]; [simpl; lia.. | lia].
  Qed.

  (* Slots for each party's (real) input, and for its two (real) samples. *)
  Context (γx : Z → gname) (γr : Z → Z → gname).
  Definition xk (i : Z) (x : vgG) : iProp Σ := slot (γx i) (vgval x).
  Definition rk (i j : Z) (r : vgG) : iProp Σ := slot (γr i j) (vgval r).

  (* The real-world message from [s] to [d] with tag [t]: a share [r_{s→d}],
     or the sum [x_s · (r_{s→p} · r_{s→q})⁻¹ · r_{p→s} · r_{q→s}]. *)
  Definition lval (s d t : Z) (m : vgG) : iProp Σ :=
    (if bool_decide (t = 0) then rk s d m ∗ ∃ x, xk s x
    else ∃ x xp xq a b u v,
      xk s x ∗ xk (nxt s) xp ∗ xk (nxt2 s) xq ∗
      rk s (nxt s) a ∗ rk s (nxt2 s) b ∗ rk (nxt s) s u ∗ rk (nxt2 s) s v ∗
      ⌜(m = x * (a * b)^-1 * u * v)%g⌝)%I.

  (* The simulator's copy of that message: [h']'s share to [h] is shifted by
     [x_{h'}⁻¹], and [h]'s sums by [(x_h · x_{h'})⁻¹]; the patch undoes the
     latter on [h]'s sum to [c]. *)
  Definition raw_adj (s d t : Z) (m m' : vgG) : iProp Σ :=
    (if bool_decide ((s, d, t) = (hz', hz, 0)) then ∃ x', xk hz' x' ∗ ⌜(m' = x'^-1 * m)%g⌝
    else if bool_decide ((s, t) = (hz, 1)) then
      ∃ x x', xk hz x ∗ xk hz' x' ∗ ⌜(m' = (x * x')^-1 * m)%g⌝
    else ⌜m' = m⌝)%I.
  Definition del_adj (s d t : Z) (m m' : vgG) : iProp Σ :=
    (if bool_decide ((s, d, t) = (hz, cz, 1)) then ⌜m' = m⌝ else raw_adj s d t m m')%I.

  Definition msg_rel (adj : Z → Z → Z → vgG → vgG → iProp Σ) (k : Z) (v1 v2 : val) : iProp Σ :=
    (∃ s d t (m m' : vgG),
      ⌜hdr_ok s d t ∧ k = key s d t ∧ v1 = vgval m ∧ v2 = vgval m'⌝ ∗
      lval s d t m ∗ adj s d t m m')%I.

  Definition Rmsg : Z → val → val → iProp Σ := msg_rel raw_adj.
  Definition Rdeliv : Z → val → val → iProp Σ := msg_rel del_adj.

  Global Instance lval_persistent s d t m : Persistent (lval s d t m).
  Proof. rewrite /lval. case_bool_decide; apply _. Qed.
  Global Instance lval_timeless s d t m : Timeless (lval s d t m).
  Proof. rewrite /lval. case_bool_decide; apply _. Qed.
  Global Instance raw_adj_persistent s d t m m' : Persistent (raw_adj s d t m m').
  Proof. rewrite /raw_adj. repeat case_bool_decide; apply _. Qed.
  Global Instance raw_adj_timeless s d t m m' : Timeless (raw_adj s d t m m').
  Proof. rewrite /raw_adj. repeat case_bool_decide; apply _. Qed.
  Global Instance del_adj_persistent s d t m m' : Persistent (del_adj s d t m m').
  Proof. rewrite /del_adj. case_bool_decide; apply _. Qed.
  Global Instance del_adj_timeless s d t m m' : Timeless (del_adj s d t m m').
  Proof. rewrite /del_adj. case_bool_decide; apply _. Qed.
  Global Instance Rmsg_persistent k v1 v2 : Persistent (Rmsg k v1 v2).
  Proof. apply _. Qed.
  Global Instance Rmsg_timeless k v1 v2 : Timeless (Rmsg k v1 v2).
  Proof. apply _. Qed.
  Global Instance Rdeliv_persistent k v1 v2 : Persistent (Rdeliv k v1 v2).
  Proof. apply _. Qed.
  Global Instance Rdeliv_timeless k v1 v2 : Timeless (Rdeliv k v1 v2).
  Proof. apply _. Qed.

End party_defs.

(** * The party's run *)

Section party.
  Context `{!probblazeRGS Σ, !inG Σ (dfrac_agreeR valO)}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  Context (c : nat) (Hc : (c < 3)%nat).
  Context (γx : Z → gname) (γr : Z → Z → gname).
  Local Open Scope Z_scope.

  Local Notation xk := (xk γx).
  Local Notation rk := (rk γr).
  Local Notation Rmsg := (Rmsg c γx γr).
  Local Notation Rdeliv := (Rdeliv c γx γr).

  (* The simulator's sample, against the real sample [r], is [shift i j x * r]:
     only [h']'s share to [h] is shifted, by [x_{h'}⁻¹]. *)
  Definition shift (i j : Z) (x : vgG) : vgG :=
    if bool_decide ((i, j) = (hz' c, hz c)) then (x^-1)%g else 1%g.

  (* What the corrupt party leaks: a sample, or a received message. *)
  Definition leak_ok (v : val) : Prop :=
    (∃ r : vgG, v = InjLV (vgval r)) ∨ (∃ (s t : Z) (m : vgG), v = InjRV ((#s, #t), vgval m)).

  (* What the corrupt party leaks has the type of the leak operation's argument. *)
  Lemma leak_ok_typed v : leak_ok v → ⊢ τ_view v v.
  Proof.
    rewrite /τ_view /sem_ty_sum /sem_ty_prod.
    intros [[r ->] | (s & t & m & ->)].
    - iExists _, _. iLeft. repeat iSplit; try done. by iExists r.
    - iExists _, _. iRight. repeat iSplit; try done.
      iExists _, _, _, _. repeat iSplit; try done.
      + iExists _, _, _, _. repeat iSplit; try done; by iExists _.
      + by iExists m.
  Qed.

  Local Notation lval := (lval γx γr).
  Local Notation raw_adj := (raw_adj c γx).
  Local Notation del_adj := (del_adj c γx).

  (* Decide the role comparisons in the goal. *)
  Local Ltac roles :=
    destruct (roles_spec c Hc) as (? & ? & ? & ? & ? & ? & ? & ? & ? & _);
    repeat match goal with
      | |- context [bool_decide ?P] =>
          (rewrite (bool_decide_eq_true_2 P); [|done]) ||
          (rewrite (bool_decide_eq_false_2 P); [|intros ?; simplify_eq; congruence])
      end.

  (** Facts about messages *)

  Lemma rk_agree i j a b : rk i j a -∗ rk i j b -∗ ⌜a = b⌝.
  Proof using.
    iIntros "H1 H2". iDestruct (slot_agree with "H1 H2") as %Hv.
    iPureIntro. by apply vgval_inj.
  Qed.

  Lemma xk_agree i a b : xk i a -∗ xk i b -∗ ⌜a = b⌝.
  Proof using.
    iIntros "H1 H2". iDestruct (slot_agree with "H1 H2") as %Hv.
    iPureIntro. by apply vgval_inj.
  Qed.

  Lemma shift_nxt i x : shift i (nxt i) x = 1%g.
  Proof using Hc.
    destruct (roles_spec c Hc) as (_ & _ & _ & _ & Hh'n & _ & Hhc & _).
    rewrite /shift bool_decide_eq_false_2 //. intros [= -> Hn]. congruence.
  Qed.

  (* A share, as sent. *)
  Lemma share_rmsg i j x r :
    hdr_ok i j 0 →
    xk i x -∗ rk i j r -∗ Rmsg (key i j 0) (vgval r) (vgval (shift i j x * r)%g).
  Proof using Hc.
    iIntros (Hhdr) "#Hx #Hr".
    iExists i, j, 0, r, _. iSplit; first done.
    rewrite /= /add3_party.lval /add3_party.raw_adj /shift. iSplit; first by iFrame "#".
    destruct (decide ((i, j) = (hz' c, hz c))) as [[= -> ->] | Hne].
    - roles. iExists x. by iFrame "#".
    - rewrite (bool_decide_eq_false_2 ((i, j, 0) = _)); last by intros [= -> ->].
      rewrite (bool_decide_eq_false_2 ((i, 0) = _)); last by intros [=].
      rewrite bool_decide_eq_false_2 //. by rewrite mul1g.
  Qed.

  Lemma lval_share s d m : lval s d 0 m -∗ rk s d m.
  Proof using. rewrite /add3_party.lval bool_decide_eq_true_2 //. by iIntros "[$ _]". Qed.

  (* What a delivery tells the receiver. *)
  Lemma deliv_inv s d t u1 u2 :
    hdr_ok s d t →
    Rdeliv (key s d t) u1 u2 -∗
    ∃ m m', ⌜u1 = vgval m ∧ u2 = vgval m'⌝ ∗ lval s d t m ∗ del_adj s d t m m'.
  Proof using.
    iIntros (Hhdr) "(%s' & %d' & %t' & %m & %m' & (%Hhdr' & %Hk & -> & ->) & Hl & Hadj)".
    destruct (key_inj _ _ _ _ _ _ Hhdr Hhdr' Hk) as (-> & -> & ->).
    iExists m, m'. by iFrame.
  Qed.

  (* Party [i]'s sum, as sent, in both worlds. *)
  Lemma sum_rmsg i j x rp rq bp bp' bq bq' :
    0 ≤ i < 3 → j = nxt i ∨ j = nxt2 i →
    xk i x -∗ rk i (nxt i) rp -∗ rk i (nxt2 i) rq -∗
    lval (nxt i) i 0 bp -∗ del_adj (nxt i) i 0 bp bp' -∗
    lval (nxt2 i) i 0 bq -∗ del_adj (nxt2 i) i 0 bq bq' -∗
    Rmsg (key i j 1) (vgval (x * (rp * rq)^-1 * bp * bq)%g)
      (vgval ((if bool_decide (i = cz c) then x else 1) *
              (rp * (shift i (nxt2 i) x * rq))^-1 * bp' * bq')%g).
  Proof using All.
    intros Hi Hj.
    destruct (nxt_spec i Hi) as (Hp & Hq & Hpi & Hqi & Hqp & _).
    assert (hdr_ok i j 1) as Hhdr by (rewrite /hdr_ok; destruct Hj as [-> | ->]; lia).
    rewrite /Rmsg /msg_rel /add3_party.lval /add3_party.del_adj /add3_party.raw_adj /shift.
    destruct (roles_spec c Hc) as (Hcn & Hcn2 & Hhn & Hhn2 & Hh'n & Hh'n2 & _).
    destruct (roles_cases c Hc i Hi) as [-> | [-> | ->]].
    - (* the corrupt party: nothing shifted *)
      rewrite Hcn Hcn2. roles.
      iIntros "#Hx #Hrp #Hrq [#Hbp [%xp #Hxp]] %Hbp' [#Hbq [%xq #Hxq]] %Hbq'". subst.
      iExists (cz c), j, 1, _, _. rewrite Hcn Hcn2. roles. iSplit; first done.
      iSplit; first (iExists x, xp, xq, rp, rq, bp, bq; by iFrame "#").
      iPureIntro. by rewrite !mul1g.
    - (* [h]: dummy input, and [h']'s share was shifted *)
      rewrite Hhn Hhn2. roles.
      iIntros "#Hx #Hrp #Hrq [#Hbp [%xp #Hxp]] [%x' [#Hx' %Hbp']] [#Hbq [%xq #Hxq]] %Hbq'". subst.
      iExists (hz c), j, 1, _, _. rewrite Hhn Hhn2. roles. iSplit; first done.
      iSplit; first (iExists x, xp, xq, rp, rq, bp, bq; by iFrame "#").
      iExists x, x'. iFrame "#". iPureIntro. apply sum_h_alg.
    - (* [h']: dummy input, and its own share to [h] was shifted *)
      rewrite Hh'n Hh'n2. roles.
      iIntros "#Hx #Hrp #Hrq [#Hbp [%xp #Hxp]] %Hbp' [#Hbq [%xq #Hxq]] %Hbq'". subst.
      iExists (hz' c), j, 1, _, _. rewrite Hh'n Hh'n2. roles. iSplit; first done.
      iSplit; first (iExists x, xp, xq, rp, rq, bp, bq; by iFrame "#").
      iPureIntro. apply sum_h'_alg.
  Qed.

  (* A party's output, from its sum and its peers'. *)
  Lemma output_post i x rp rq bp bq sp sq :
    0 ≤ i < 3 →
    xk i x -∗ rk i (nxt i) rp -∗ rk i (nxt2 i) rq -∗
    rk (nxt i) i bp -∗ rk (nxt2 i) i bq -∗
    lval (nxt i) i 1 sp -∗ lval (nxt2 i) i 1 sq -∗
    ∃ x0 x1 x2, xk 0 x0 ∗ xk 1 x1 ∗ xk 2 x2 ∗
      ⌜(x * (rp * rq)^-1 * bp * bq * sp * sq = x0 * x1 * x2)%g⌝.
  Proof using All.
    iIntros (Hi) "#Hx #Hrp #Hrq #Hbp #Hbq Hsp Hsq".
    destruct (nxt_spec i Hi) as (Hp & Hq & Hpi & Hqi & Hqp & Hpp & Hpq & Hqp' & Hqq).
    rewrite /add3_party.lval !bool_decide_eq_false_2 //.
    rewrite Hpp Hpq Hqp' Hqq.
    iDestruct "Hsp" as (xp xpp xpq a' b' u' v') "(#Hxp & _ & _ & #Ha' & #Hb' & #Hu' & #Hv' & ->)".
    iDestruct "Hsq" as (xq xqp xqq a'' b'' u'' v'') "(#Hxq & _ & _ & #Ha'' & #Hb'' & #Hu'' & #Hv'' & ->)".
    iDestruct (rk_agree with "Hb' Hbp") as %->.
    iDestruct (rk_agree with "Hv' Hrp") as %->.
    iDestruct (rk_agree with "Ha'' Hbq") as %->.
    iDestruct (rk_agree with "Hb'' Hu'") as %->.
    iDestruct (rk_agree with "Hu'' Hrq") as %->.
    iDestruct (rk_agree with "Hv'' Ha'") as %->.
    rewrite (sums_alg x xp xq).
    assert (i = 0 ∨ i = 1 ∨ i = 2) as [ -> | [ -> | -> ] ] by (clear -Hi; lia).
    - iExists x, xp, xq. by iFrame "#".
    - iExists xq, x, xp. iFrame "#". iPureIntro.
      by rewrite (vgG_comm _ xq) mulgA.
    - iExists xp, xq, x. iFrame "#". iPureIntro.
      by rewrite -mulgA (vgG_comm x).
  Qed.

  (** The honest operations. *)
  Definition send_v (i : Z) (l : label) : val := (λ: "msg", do: l (InjL (#i, "msg")))%V.
  Definition recv_v (i : Z) (l : label) : val := (λ: "h", do: l (InjR (#i, "h")))%V.

  (** The corrupt party's operations, as [leaky] builds them. *)
  Definition leaky_recv (r lk : val) : val :=
    (λ: "h", let: "m" := r "h" in lk (InjR ("h", "m"));; "m")%V.
  Definition leaky_smp (s lk : val) : val :=
    (λ: <>, let: "r" := s #()%V in lk (InjL "r");; "r")%V.

  (* After its run, a party has output the product of the (real) inputs. *)
  Definition party_post (v1 v2 : val) : iProp Σ :=
    ∃ x0 x1 x2, xk 0 x0 ∗ xk 1 x1 ∗ xk 2 x2 ∗ ⌜v1 = vgval (x0 * x1 * x2)%g⌝.

  (* What [c] receives is the same in both worlds. *)
  Lemma deliv_to_c s d t u1 u2 :
    d = cz c → hdr_ok s d t → Rdeliv (key s d t) u1 u2 -∗ ∃ m : vgG, ⌜u1 = vgval m ∧ u2 = vgval m⌝.
  Proof using Hc.
    iIntros (-> Hhdr) "Hu".
    iDestruct (deliv_inv with "Hu") as (m m') "([-> ->] & _ & Hadj)"; first done.
    iExists m. rewrite /add3_party.del_adj /add3_party.raw_adj.
    destruct (roles_spec c Hc) as (_ & _ & _ & _ & _ & _ & Hhc & Hh'c & _).
    case_bool_decide as H1; [by iDestruct "Hadj" as %->|].
    rewrite (bool_decide_eq_false_2 ((s, cz c, t) = _)); last by intros [= _ ? _].
    case_bool_decide as H2; [simplify_eq; by destruct H1|].
    by iDestruct "Hadj" as %->.
  Qed.

End party.

(** * A party's run, in both directions *)

Section party_eq.
  Context `{!probblazeRGS Σ, !inG Σ (dfrac_agreeR valO)}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  Context (c : nat) (Hc : (c < 3)%nat).
  Context (γx : Z → gname) (γr : Z → Z → gname).
  #[local] Open Scope bi_scope.
  Local Open Scope Z_scope.

  Local Notation xk := (xk γx).
  Local Notation Rmsg := (Rmsg c γx γr).
  Local Notation Rdeliv := (Rdeliv c γx γr).
  Local Notation share_rmsg := (share_rmsg c Hc γx γr).
  Local Notation sum_rmsg := (sum_rmsg c Hc γx γr).
  Local Notation output_post := (output_post c Hc γx γr).
  Local Notation deliv_to_c := (deliv_to_c c Hc γx γr).

  Local Existing Instance NeutralEctx_app.

  (* Focus on the argument of an application in contexts [Kl], [Kr]. *)
  Local Ltac bind_app Kl Kr :=
    lazymatch goal with
    | |- environments.envs_entails _ (eq_rel _ (fill Kl (App ?f ?e)) (fill Kr (App ?f' ?e')) _ _) =>
        rewrite -(fill_app Kl [AppRCtx f] e) -(fill_app Kr [AppRCtx f'] e')
    end.

  (** Party [i]'s operations, related as the protocol needs. *)
  Section ops.
    Context (ll lr : label) (θ L : sem_row Σ) (i : Z) (x : vgG).
    Local Notation X := (iLblSig_to_iLblThy (sem_row_union (¡ θ)%R L)).
    Local Notation T := (eq_thy_cons [ll] [lr] (net_thy Rmsg Rdeliv ll lr) X).

    Definition send_spec (sl sr : val) : iPropD Σ :=
      □ ∀ Kl Kr (d t : Z) (ml mr : val) S,
        ⌜NeutralEctx [ll] Kl⌝ → ⌜NeutralEctx [lr] Kr⌝ →
        ⌜ectx_labels Kl ⊆ [ll]⌝ → ⌜ectx_labels Kr ⊆ [lr]⌝ →
        ⎡Rmsg (key i d t) ml mr⎤ -∗
        EQ fill Kl #()%V ≈ fill Kr #()%V <|T|> {{S}} -∗
        EQ fill Kl (sl ((#d, #t), ml)%V) ≈ fill Kr (sr ((#d, #t), mr)%V) <|T|> {{S}}.

    Definition recv_spec (rl rr : val) : iPropD Σ :=
      □ ∀ Kl Kr (s t : Z) S,
        ⌜NeutralEctx [ll] Kl⌝ → ⌜NeutralEctx [lr] Kr⌝ →
        ⌜ectx_labels Kl ⊆ [ll]⌝ → ⌜ectx_labels Kr ⊆ [lr]⌝ → ⌜hdr_ok s i t⌝ →
        (∀ ul ur, ⎡Rdeliv (key s i t) ul ur⎤ -∗ EQ fill Kl ul ≈ fill Kr ur <|T|> {{S}}) -∗
        EQ fill Kl (rl (#s, #t)%V) ≈ fill Kr (rr (#s, #t)%V) <|T|> {{S}}.

    (* The two samples are coupled along [σ]; the corrupt party's samples
       only identically. *)
    Definition smp_spec (ml mr : val) : iPropD Σ :=
      □ ∀ Kl Kr (σ : vgG) S,
        ⌜ectx_labels Kl ⊆ [ll]⌝ → ⌜ectx_labels Kr ⊆ [lr]⌝ → ⌜i ≠ cz c ∨ σ = 1%g⌝ →
        (∀ r : vgG, EQ fill Kl (vgval r) ≈ fill Kr (vgval (σ * r)%g) <|T|> {{S}}) -∗
        EQ fill Kl (ml #()%V) ≈ fill Kr (mr #()%V) <|T|> {{S}}.

    Lemma party_core_spec (sl sr rl rr ml mr : val) Φ :
      0 ≤ i < 3 →
      ⊢ send_spec sl sr -∗ recv_spec rl rr -∗ smp_spec ml mr -∗
        ⎡xk i x⎤ -∗ ⎡slot_tok (γr i (nxt i))⎤ -∗ ⎡slot_tok (γr i (nxt2 i))⎤ -∗
        (∀ vl vr, ⎡party_post γx vl vr⎤ -∗ Φ vl vr) -∗
        EQ party #i (vgval x) ((sl, rl), ml)%V
         ≈ party #i (vgval (if bool_decide (i = cz c) then x else 1%g)) ((sr, rr), mr)%V
          <|T|> {{Φ}}.
    Proof using All.
      iIntros (Hi) "#Hsend #Hrecv #Hsmp #Hx Htp Htq HΦ".
      destruct (nxt_spec i Hi) as (Hp & Hq & Hpi & Hqi & Hqp & _).
      rewrite /party /Shr /Sum. eq_pures'. rewrite -/(nxt i) -/(nxt2 i).
      (* the two samples; only [h']'s share to [h] is shifted *)
      iApply ("Hsmp" $! [AppRCtx _] [AppRCtx _] 1%g);
        [iPureIntro; simpl; set_solver | iPureIntro; simpl; set_solver | iPureIntro; by right |].
      iIntros (rp). rewrite mul1g.
      iMod (slot_set _ (vgval rp) with "Htp") as "#Hrp". simpl. eq_pures'.
      iApply ("Hsmp" $! [AppRCtx _] [AppRCtx _] (shift c i (nxt2 i) x));
        [iPureIntro; simpl; set_solver | iPureIntro; simpl; set_solver | |].
      { iPureIntro. rewrite /shift. case_bool_decide as Hs; [left | by right].
        simplify_eq. by destruct (roles_spec c Hc) as (_&_&_&_&_&_&_&?&_). }
      iIntros (rq).
      iMod (slot_set _ (vgval rq) with "Htq") as "#Hrq". simpl. eq_pures'.
      (* sending the shares *)
      iApply ("Hsend" $! [AppRCtx _] [AppRCtx _] (nxt i) 0 (vgval rp) (vgval rp));
        [iPureIntro; tc_solve | iPureIntro; tc_solve |
         iPureIntro; simpl; set_solver | iPureIntro; simpl; set_solver | |].
      { iPoseProof (share_rmsg i (nxt i) x rp with "Hx Hrp") as "H";
          first (rewrite /hdr_ok; lia).
        by rewrite (shift_nxt c Hc) mul1g. }
      simpl. eq_pures'.
      iApply ("Hsend" $! [AppRCtx _] [AppRCtx _] (nxt2 i) 0 (vgval rq)
                (vgval (shift c i (nxt2 i) x * rq)%g));
        [iPureIntro; tc_solve | iPureIntro; tc_solve |
         iPureIntro; simpl; set_solver | iPureIntro; simpl; set_solver | |].
      { iApply (share_rmsg with "Hx Hrq"). rewrite /hdr_ok; lia. }
      simpl. eq_pures'.
      (* receiving the shares *)
      iApply ("Hrecv" $! [AppRCtx _] [AppRCtx _] (nxt i) 0);
        [iPureIntro; tc_solve | iPureIntro; tc_solve |
         iPureIntro; simpl; set_solver | iPureIntro; simpl; set_solver |
         iPureIntro; rewrite /hdr_ok; lia |].
      iIntros (u1 u2) "Hu".
      iDestruct (deliv_inv with "Hu") as (bp bp') "([-> ->] & #Hbp & #Hbp')";
        first (rewrite /hdr_ok; lia).
      simpl. eq_pures'.
      iApply ("Hrecv" $! [AppRCtx _] [AppRCtx _] (nxt2 i) 0);
        [iPureIntro; tc_solve | iPureIntro; tc_solve |
         iPureIntro; simpl; set_solver | iPureIntro; simpl; set_solver |
         iPureIntro; rewrite /hdr_ok; lia |].
      iIntros (u1 u2) "Hu2".
      iDestruct (deliv_inv with "Hu2") as (bq bq') "([-> ->] & #Hbq & #Hbq')";
        first (rewrite /hdr_ok; lia).
      simpl. eq_pures'.
      (* sending the sums *)
      iApply ("Hsend" $! [AppRCtx _] [AppRCtx _] (nxt i) 1);
        [iPureIntro; tc_solve | iPureIntro; tc_solve |
         iPureIntro; simpl; set_solver | iPureIntro; simpl; set_solver | |].
      { iApply (sum_rmsg with "Hx Hrp Hrq Hbp Hbp' Hbq Hbq'"); [done | by left]. }
      simpl. eq_pures'.
      iApply ("Hsend" $! [AppRCtx _] [AppRCtx _] (nxt2 i) 1);
        [iPureIntro; tc_solve | iPureIntro; tc_solve |
         iPureIntro; simpl; set_solver | iPureIntro; simpl; set_solver | |].
      { iApply (sum_rmsg with "Hx Hrp Hrq Hbp Hbp' Hbq Hbq'"); [done | by right]. }
      simpl. eq_pures'.
      (* receiving the peers' sums *)
      iApply ("Hrecv" $! [AppRCtx _] [AppRCtx _] (nxt i) 1);
        [iPureIntro; tc_solve | iPureIntro; tc_solve |
         iPureIntro; simpl; set_solver | iPureIntro; simpl; set_solver |
         iPureIntro; rewrite /hdr_ok; lia |].
      iIntros (u1 u2) "Hu3".
      iDestruct (deliv_inv with "Hu3") as (sp sp') "([-> ->] & #Hsp & _)";
        first (rewrite /hdr_ok; lia).
      simpl. eq_pures'.
      iApply ("Hrecv" $! [AppRCtx _] [AppRCtx _] (nxt2 i) 1);
        [iPureIntro; tc_solve | iPureIntro; tc_solve |
         iPureIntro; simpl; set_solver | iPureIntro; simpl; set_solver |
         iPureIntro; rewrite /hdr_ok; lia |].
      iIntros (u1 u2) "Hu4".
      iDestruct (deliv_inv with "Hu4") as (sq sq') "([-> ->] & #Hsq & _)";
        first (rewrite /hdr_ok; lia).
      simpl. eq_pures'.
      (* the output *)
      iDestruct (output_post with "Hx Hrp Hrq [Hbp] [Hbq] Hsp Hsq") as (x0 x1 x2) "(H0 & H1 & H2 & %Heq)";
        [done | by iApply lval_share | by iApply lval_share |].
      iApply eq_value. iModIntro. iApply "HΦ".
      iExists x0, x1, x2. iFrame "H0 H1 H2". iPureIntro. by f_equal.
    Qed.

    Lemma net_send_spec : ⊢ send_spec (send_v i ll) (send_v i lr).
    Proof using.
      iIntros "!>" (Kl Kr d t ml mr S HKl HKr _ _) "Hm Hk".
      rewrite /send_v. eq_pures'.
      by iApply (eq_net_send with "Hm Hk").
    Qed.

    Lemma net_recv_spec : ⊢ recv_spec (recv_v i ll) (recv_v i lr).
    Proof using.
      iIntros "!>" (Kl Kr s t S HKl HKr _ _ Hhdr) "Hk".
      rewrite /recv_v. eq_pures'.
      by iApply (eq_net_recv with "Hk").
    Qed.

    Lemma smp_smp_spec : ⊢ smp_spec smp smp.
    Proof using All.
      iIntros "!>" (Kl Kr σ S _ _ _) "Hk".
      rewrite /smp /sample. eq_pures'.
      eq_focus_l (rand #_)%E. eq_focus_r (rand #_)%E.
      iApply (eq_couple_rand_rand_bij _ _ (add_coupling_nat σ)); first apply add_coupling_nat_bound.
      iIntros (k) "%Hk". rewrite !fill_app /=. eq_pures'.
      rewrite add_coupling_nat_mult; last lia.
      iApply "Hk".
    Qed.

    Lemma leaky_recv_spec lkl lkr :
      i = cz c → ⊢ ⟪ τ_view -{ θ }-> 𝟙 ⟫ lkl lkr -∗
      recv_spec (leaky_recv (recv_v i ll) lkl) (leaky_recv (recv_v i lr) lkr).
    Proof using Hc.
      iIntros (Hic) "#Hlk !>". iIntros (Kl Kr s t S HKl HKr HLl HLr Hhdr) "Hk".
      rewrite /leaky_recv /recv_v. eq_pures'.
      bind_app Kl Kr.
      iApply eq_net_recv; [done.. |].
      iIntros (ul ur) "#Hu". rewrite !fill_app /=.
      iDestruct (deliv_to_c with "Hu") as (m) "[-> ->]"; [done | done |].
      eq_pures'.
      bind_app Kl Kr.
      iApply (eq_env_call with "Hlk [] [Hk]");
        [rewrite ectx_labels_app /=; set_solver.. | iApply eq_lift_same; iApply leak_ok_typed; right; by eexists _, _, _ |].
      iIntros (wl wr) "Hw". rewrite eq_lift_unit. iDestruct "Hw" as %[-> ->].
      rewrite !fill_app /=. eq_pures'.
      by iApply "Hk".
    Qed.

    Lemma leaky_smp_spec lkl lkr :
      i = cz c → ⊢ ⟪ τ_view -{ θ }-> 𝟙 ⟫ lkl lkr -∗
      smp_spec (leaky_smp smp lkl) (leaky_smp smp lkr).
    Proof using All.
      iIntros (Hic) "#Hlk !>". iIntros (Kl Kr σ S HLl HLr [Hσ | ->]) "Hk"; first done.
      rewrite /leaky_smp. eq_pures'.
      bind_app Kl Kr.
      iApply (smp_smp_spec $! _ _ 1%g);
        [iPureIntro; rewrite ectx_labels_app /=; set_solver.. | by iPureIntro; right |].
      iIntros (r). rewrite mul1g !fill_app /=. eq_pures'.
      bind_app Kl Kr.
      iApply (eq_env_call with "Hlk [] [Hk]");
        [rewrite ectx_labels_app /=; set_solver.. | iApply eq_lift_same; iApply leak_ok_typed; left; by eexists |].
      iIntros (wl wr) "Hw". rewrite eq_lift_unit. iDestruct "Hw" as %[-> ->].
      rewrite !fill_app /=. eq_pures'.
      iSpecialize ("Hk" $! r). by rewrite mul1g.
    Qed.

    Lemma run_party_spec lkl lkr Φ :
      0 ≤ i < 3 →
      ⊢ ⟪ τ_view -{ θ }-> 𝟙 ⟫ lkl lkr -∗
        ⎡xk i x⎤ -∗ ⎡slot_tok (γr i (nxt i))⎤ -∗ ⎡slot_tok (γr i (nxt2 i))⎤ -∗
        (∀ vl vr, ⎡party_post γx vl vr⎤ -∗ Φ vl vr) -∗
        EQ run_party c lkl (net_eps ll) #i (vgval x)
         ≈ run_party c lkr (net_eps lr) #i (if bool_decide (i = cz c) then vgval x else vunit)
          <|T|> {{Φ}}.
    Proof using All.
      iIntros (Hi) "#Hlk #Hx Htp Htq HΦ".
      rewrite /run_party. eq_pures'.
      iApply (eq_sel3_net [AppRCtx _] [AppRCtx _]); first done.
      rewrite /net_ep /=. eq_pures'.
      case_bool_decide as Hic.
      - (* the corrupt party *)
        assert (i = cz c) as Hic' by (inversion Hic; rewrite /cz; lia).
        rewrite (bool_decide_eq_true_2 (i = cz c)) //.
        rewrite /leaky. eq_pures'.
        iPoseProof (party_core_spec (send_v i ll) (send_v i lr)
          (leaky_recv (recv_v i ll) lkl) (leaky_recv (recv_v i lr) lkr)
          (leaky_smp smp lkl) (leaky_smp smp lkr) _ Hi
          with "[] [] [] Hx Htp Htq HΦ") as "H".
        { iApply net_send_spec. }
        { by iApply leaky_recv_spec. }
        { by iApply leaky_smp_spec. }
        iEval (rewrite (bool_decide_eq_true_2 (i = cz c)) //) in "H".
        iApply "H".
      - (* an honest party *)
        assert (i ≠ cz c) as Hic' by (intros Heq; apply Hic; by rewrite Heq).
        rewrite (bool_decide_eq_false_2 (i = cz c)) // is_unit. eq_pures'.
        iPoseProof (party_core_spec (send_v i ll) (send_v i lr) (recv_v i ll) (recv_v i lr) smp smp _ Hi
          with "[] [] [] Hx Htp Htq HΦ") as "H".
        { iApply net_send_spec. }
        { iApply net_recv_spec. }
        { iApply smp_smp_spec. }
        iEval (rewrite (bool_decide_eq_false_2 (i = cz c)) //) in "H".
        iApply "H".
    Qed.

    (* The corrupt party runs on its input in both worlds, an honest one on
       the dummy input in the simulation. *)
    Lemma eq_run_party_c lkl lkr Φ :
      0 ≤ i < 3 → i = cz c →
      ⊢ ⟪ τ_view -{ θ }-> 𝟙 ⟫ lkl lkr -∗
        ⎡xk i x⎤ -∗ ⎡slot_tok (γr i (nxt i))⎤ -∗ ⎡slot_tok (γr i (nxt2 i))⎤ -∗
        (∀ vl vr, ⎡party_post γx vl vr⎤ -∗ Φ vl vr) -∗
        EQ run_party c lkl (net_eps ll) #i (vgval x) ≈ run_party c lkr (net_eps lr) #i (vgval x)
          <|T|> {{Φ}}.
    Proof using All.
      iIntros (Hi Hic) "Hlk Hx Htp Htq HΦ".
      iPoseProof (run_party_spec with "Hlk Hx Htp Htq HΦ") as "H"; first done.
      by rewrite bool_decide_eq_true_2.
    Qed.

    Lemma eq_run_party_h lkl lkr Φ :
      0 ≤ i < 3 → i ≠ cz c →
      ⊢ ⟪ τ_view -{ θ }-> 𝟙 ⟫ lkl lkr -∗
        ⎡xk i x⎤ -∗ ⎡slot_tok (γr i (nxt i))⎤ -∗ ⎡slot_tok (γr i (nxt2 i))⎤ -∗
        (∀ vl vr, ⎡party_post γx vl vr⎤ -∗ Φ vl vr) -∗
        EQ run_party c lkl (net_eps ll) #i (vgval x) ≈ run_party c lkr (net_eps lr) #i vunit
          <|T|> {{Φ}}.
    Proof using All.
      iIntros (Hi Hic) "Hlk Hx Htp Htq HΦ".
      iPoseProof (run_party_spec with "Hlk Hx Htp Htq HΦ") as "H"; first done.
      by rewrite bool_decide_eq_false_2.
    Qed.
  End ops.

End party_eq.
