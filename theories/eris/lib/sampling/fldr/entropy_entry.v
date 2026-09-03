(** * Entry-point closure: Tachis specs for FLDR's real entry points.

    [entropy_cost.v] proves the expected flip-cost bound for [fldr_loop]
    GIVEN an already-built DDG table ([wp_fldr_loop_flip_cost]).  The real
    entry points ([fldr], [fldr_sample]) build that table themselves, by
    calling [fldr_table] (defined in [implementation.v], specified for Eris
    in [preprocessing.v]).  This file closes that gap; [entropy_bound.v]
    then bounds [flip_cost ws] itself by the Shannon entropy of [ws].

    Scope discipline: Tachis + Eris only (this development targets the
    Tachis-FLDR paper's minimal dependencies).

    Why a SEPARATE Tachis proof of the (entirely zero-cost) preprocessing
    layer, instead of reusing [preprocessing.v]'s Eris triples directly?
    Eris's total-WP judgment [ [[{ }]] ] and Tachis's partial-WP judgment
    [ {{{ }}} ] are built over different resource algebras ([erisGS] carries
    Eris's error credit [↯], [tachisGS _ CostEntropy_2] carries Tachis's
    expected-cost credit [⧖]); there is no generic lemma turning an Eris
    triple into a Tachis triple, so every preprocessing step needs its own
    Tachis-side proof.  The proof *scripts* port essentially verbatim
    (preprocessing never touches [rand], so every step costs 0 under
    [CostEntropy_2], exactly like [entropy_cost.v]'s own
    [wp_list_length_row]/[wp_list_nth_row] port) -- only the target judgment
    changes.  [is_list]/[inject] (Eris's generic list representation, from
    [clutch.eris.lib.list]) are GS-free (no [erisGS] anywhere in their
    statement or proof, which is exactly what lets the whole development
    below go through with only [tachisGS Σ CostEntropy_2] in scope), so we
    build the whole preprocessing chain over them exactly as
    [preprocessing.v] does, and only bridge to [entropy_cost.v]'s own
    bespoke [is_row]/[is_rows] representation at the very last step
    (Section 3 below), right before invoking [wp_fldr_loop_flip_cost].

    Iris's WP notations ([{{{ }}}], [wp_apply], ...) are typeclass-generic:
    with only [tachisGS Σ CostEntropy_2] in scope (no [erisGS] instance),
    they resolve to Tachis's own WP, even though the Eris library modules
    ([list], [preprocessing], ...) are imported for their pure definitions
    and lemmas -- [entropy_cost.v] already relies on exactly this. *)

From Coq Require Import Arith.PeanoNat Lists.List Reals Psatz Lia ZArith NArith.
From clutch.tachis Require Import expected_time_credits ert_weakestpre
  problang_wp proofmode derived_laws ert_rules cost_models adequacy.
From clutch.prob_lang Require Import notation tactics metatheory lang.
From clutch.common Require Import inject.
From clutch.eris.lib Require Import list.
From clutch.eris.lib.sampling.fldr Require Import model implementation walk pure
  distribution entropy_cost preprocessing interface.
From Coquelicot Require Import Rbar.
Import ListNotations.

Set Default Proof Using "Type*".
(** NOTE: [clutch.tachis.expected_time_credits] opens [Scope R] itself
    (non-locally, inside a Section, which does not close a bare [Open
    Scope]), so [Scope R] is already active throughout this file from the
    imports above.  Sections 1-2 below are ported from [preprocessing.v],
    which never opens [Scope R] and is entirely about [nat]-valued
    computation ([-], [^], [<=], ... all mean the [nat] operation there);
    to port those statements unchanged we explicitly [Close] the scope for
    their duration and [Open] it again (as [entropy_cost.v] does) only
    once real-valued statements ([flip_cost], [⧖], the ERT corollaries)
    start, at the end of Section 2. *)
#[local] Close Scope R.

(** * 1. Tachis-side list-library specs over Eris's [is_list]/[inject].

    Direct ports of [clutch.eris.lib.list]'s own partial-WP ([{{{ }}}])
    lemmas (NOT the total-WP [twp_list_*] ones used internally by
    [preprocessing.v]; those differ from these by later-modality
    bookkeeping specific to total WP, matching how [entropy_cost.v]'s
    [wp_list_length_row]/[wp_list_nth_row] are themselves ports of
    [list.v]'s [wp_list_length]/[wp_list_nth], not of any total-WP
    counterpart).  Named [wp_fldr_list_*] (rather than [wp_list_*]) purely
    to avoid shadowing the identically-named Eris lemmas already in scope
    from the [list] import; the proof scripts are otherwise verbatim. *)

Section FldrListHelpers.
  Context `{!tachisGS Σ CostEntropy_2}.
  Context `[!Inject A val].

  Lemma wp_fldr_list_cons a l lv E :
    {{{ ⌜is_list l lv⌝ }}}
      list_cons (inject a) lv @ E
    {{{ v, RET v; ⌜is_list (a::l) v⌝}}}.
  Proof.
    iIntros (Φ) "% HΦ". wp_lam. wp_pures.
    iApply "HΦ". iPureIntro; by eexists.
  Qed.

  Local Lemma wp_fldr_list_rev_aux E l lM r rM:
   {{{ ⌜is_list lM l ∧ is_list rM r⌝ }}}
     list_rev_aux (Val l) (Val r) @ E
   {{{ v, RET v; ⌜is_list (rev_append lM rM) v⌝ }}}.
  Proof.
    iIntros (? [Hl Hr]) "H".
    iInduction lM as [|a lM] "IH" forall (l r rM Hl Hr).
    - simpl in *; subst. rewrite /list_rev_aux. wp_pures. by iApply "H".
    - destruct Hl as [l' [Hl'eq Hl']]; subst.
      wp_rec; wp_pures.
      wp_apply wp_fldr_list_cons; [done|].
      iIntros (w Hw).
      wp_pures. by iApply "IH".
  Qed.

  Lemma wp_fldr_list_rev E l lM :
    {{{ ⌜is_list lM l⌝ }}}
      list_rev (Val l) @ E
    {{{ v, RET v; ⌜is_list (reverse lM) v⌝ }}}.
  Proof.
    iIntros (??) "H". rewrite /list_rev. wp_pures.
    by iApply (wp_fldr_list_rev_aux _ _ _ NONEV []).
  Qed.

  Lemma wp_fldr_list_append E l lM r rM :
    {{{ ⌜is_list lM l⌝ ∗ ⌜is_list rM r⌝}}}
      list_append (Val l) (Val r) @ E
    {{{ v, RET v; ⌜is_list (lM ++ rM) v⌝ }}}.
  Proof.
    iIntros (Φ) "[%Hl %Hr] HΦ". rewrite /list_append.
    iInduction lM as [|a lM] "IH" forall (l r Hl Hr Φ).
    - simpl in Hl; subst. wp_pures. by iApply "HΦ".
    - destruct Hl as [l' [Hl'eq Hl']]; subst.
      do 12 wp_pure _.
      wp_bind (((rec: "list_append" _ _:= _)%V _ _)).
      iApply "IH"; [done..|].
      iIntros "!>" (v Hv).
      by wp_apply wp_fldr_list_cons.
  Qed.

  Lemma wp_fldr_list_fold P Φ Ψ E handler (l : list A) acc lv :
    (∀ (a : A) acc lacc lrem,
        {{{ ⌜l = lacc ++ a :: lrem⌝ ∗ P lacc acc ∗ Φ a }}}
          (Val handler) (Val acc) (inject a) @ E
        {{{v, RET v; P (lacc ++ [a]) v ∗ Ψ a }}}) -∗
    {{{ ⌜is_list l lv⌝ ∗ P [] acc ∗ [∗ list] a∈l, Φ a }}}
      list_fold handler acc lv @ E
    {{{v, RET v; P l v ∗ [∗ list] a∈l, Ψ a }}}.
  Proof.
    iIntros "#Hcl". iIntros (Ξ) "!# (Hl & Hacc & HΦ) HΞ".
    change l with ([] ++ l) at 1 4.
    generalize (@nil A) at 1 3 4 as lproc => lproc.
    iInduction l as [|x l] "IHl" forall (Ξ lproc acc lv) "Hacc Hl HΞ".
    - iDestruct "Hl" as %?; simpl in *; simplify_eq.
      wp_rec. wp_pures. iApply "HΞ".
      rewrite app_nil_r; iFrame; done.
    - iDestruct "Hl" as %[lw [? Hlw]]; subst.
      iDestruct "HΦ" as "[Hx HΦ]".
      wp_rec. wp_pures.
      wp_apply ("Hcl" with "[$Hacc $Hx] [-]"); auto.
      iNext. iIntros (w) "[Hacc HΨ]"; simpl. wp_pures.
      iApply ("IHl" with "[] [$HΦ] [$Hacc] [] [HΨ HΞ]"); [|auto|].
      { rewrite -app_assoc; auto. }
      iNext. iIntros (v) "[HP HΨs]".
      rewrite -app_assoc.
      iApply "HΞ"; iFrame.
  Qed.

  Lemma wp_fldr_list_filter (l : list A) (P : A -> bool) (f lv : val) E :
    {{{ (∀ (x : A),
            {{{ True }}}
              f (inject x) @ E
            {{{ w, RET w; ⌜w = inject (P x)⌝ }}} ) ∗
        ⌜is_list l lv⌝ }}}
       list_filter f lv @ E
     {{{ rv, RET rv; ⌜is_list (List.filter P l) rv⌝ }}}.
  Proof.
    iIntros (Φ) "[#Hf %Hil] HΦ".
    iInduction l as [ | h t] "IH" forall (lv Hil Φ); simpl in Hil.
    - subst.
      rewrite /list_filter; wp_pures.
      iApply "HΦ"; done.
    - destruct Hil as (lv' & -> & Hil).
      rewrite /list_filter.
      do 7 (wp_pure _).
      fold list_filter.
      wp_apply ("IH" $! lv'); [done |].
      iIntros (rv) "%Hilp"; wp_pures.
      wp_apply "Hf"; [done |].
      iIntros (w) "->".
      destruct (P h) eqn:HP; wp_pures.
      + wp_apply wp_fldr_list_cons; [by eauto |].
        iIntros (v) "%Hil'".
        iApply "HΦ"; iPureIntro.
        simpl; rewrite HP; simpl.
        simpl in Hil'; done.
      + iApply "HΦ"; iPureIntro.
        simpl. rewrite HP. done.
  Qed.

End FldrListHelpers.

Section FldrListHelpersExtra.
  Context `{!tachisGS Σ CostEntropy_2}.
  Context `[!Inject A val].

  Lemma wp_fldr_list_map `{!Inject B val} (l : list A) (f : A -> B) (fv lv : val)
    (P : A -> iProp Σ) (Q : A -> val -> iProp Σ) E :
    {{{ (∀ (x : A),
          {{{ P x }}}
            fv (inject x) @ E
          {{{ fr, RET fr; ⌜fr = inject $ f x ⌝ ∗ Q x fr }}}) ∗
        ⌜is_list l lv⌝ ∗
        [∗ list] x∈l, P x
    }}}
      list_map fv lv @ E
      {{{ rv, RET rv; ⌜is_list (List.map f l) rv⌝ ∗
                      [∗ list] p ∈ zip l (List.map f l), Q (fst p) (inject $ snd p)
      }}}.
  Proof.
      iIntros (Φ) "[#Hf [%Hil HP]] HΦ".
      iInduction l as [ | h t] "IH" forall (lv Hil Φ); simpl in Hil; try subst; rewrite /list_map.
      - wp_pures.
        iApply "HΦ".
        iModIntro. iSplitR; last done.
        iPureIntro. rewrite /is_list; done.
      - wp_pures.
        destruct Hil as (lv' & -> & Hil').
        do 4 wp_pure _.
        fold list_map.
        rewrite big_sepL_cons.
        iDestruct "HP" as "[HP HP']".
        wp_apply ("IH" with "[][HP']"); [done|done|].
        iIntros (rv) "[%Hil_rv Hzip]"; wp_pures.
        wp_apply ("Hf" with "[$]").
        iIntros (fr) "[-> HQ]".
        wp_apply (wp_fldr_list_cons); [done|].
        iIntros (v) "%Hilf".
        iApply "HΦ"; auto.
        iSplitR; first done.
        rewrite map_cons. simpl. iFrame.
  Qed.

  Lemma wp_fldr_list_map_pure `{!Inject B val} (l : list A) (f : A -> B) (fv lv : val) E :
    {{{ (∀ (x : A),
          {{{ True }}}
            fv (inject x) @ E
          {{{ fr, RET fr; ⌜fr = inject (f x)⌝ }}}) ∗
          ⌜is_list l lv⌝ }}}
      list_map fv lv @ E
    {{{ rv, RET rv; ⌜is_list (List.map f l) rv⌝ }}}.
  Proof.
    iIntros (Φ) "[#H %Hl] HΦ".
    iApply wp_fldr_list_map; last first.
    - iModIntro. iIntros (?) "[% ?]". by iApply "HΦ".
    - iIntros. repeat iSplit.
      + iIntros (??) "!> _ K". wp_apply "H"; [done|].
        iIntros. iApply "K". by iSplit.
      + done.
      + by instantiate (1 := (λ _, True)%I).
  Qed.

  Lemma wp_fldr_list_mapi_loop `{!Inject B val}
        (f : nat -> A -> B) (k : nat) (l : list A) (fv lv : val)
        (γ : nat -> A -> iProp Σ) (ψ : nat -> B -> iProp Σ) E :
    {{{ □ (∀ (i : nat) (x : A),
              {{{ γ (k + i)%nat x }}}
                fv (inject (k + i)%nat) (inject x) @ E
                {{{ fr, RET fr;
                    let r := f (k + i)%nat x in
                    ⌜fr = (inject r)⌝ ∗ ψ (k + i)%nat r }}}) ∗
        ⌜is_list l lv⌝ ∗
        ([∗ list] i ↦ a ∈ l, γ (k + i)%nat a)
    }}}
      list_mapi_loop fv #k lv @ E
    {{{ rv, RET rv;
        let l' := mapi_loop f k l in
        ⌜is_list l' rv⌝ ∗
        ([∗ list] i ↦ a ∈ l', ψ (k + i)%nat a)}}}.
  Proof.
    iInduction l as [ | h l'] "IH" forall (lv k);
      iIntros (Φ) "[#Hf [%Hil Hown]] HΦ"; simpl in Hil;
      rewrite /list_mapi_loop.
    - subst.
      wp_pures.
      iApply "HΦ".
      iSplitL ""; done.
    - destruct Hil as [lv' [-> Hil']].
      do 10 wp_pure _.
      fold list_mapi_loop.
      wp_bind (list_mapi_loop _ _ _).
      iAssert (⌜#(k + 1) = #(k + 1)%nat⌝%I) as "->".
      { iPureIntro.
        do 2 apply f_equal; lia. }
      iDestruct (big_sepL_cons with "Hown") as "[Hhead Hown]".
      iApply ("IH" with "[Hown]").
      + iSplitL "".
        * iModIntro.
          iIntros (i x).
          iPoseProof ("Hf"  $! (1 + i)%nat x) as "Hf'".
          iAssert (⌜(k + (1 + i))%nat = (k + 1 + i)%nat⌝%I) as %<-.
          {  iPureIntro; by lia. }
          iApply "Hf".
        * iSplitL ""; [done |].
          iApply (big_sepL_impl with "Hown").
          iModIntro.
          iIntros (k' x) "_ Hpre".
          iAssert (⌜(k + 1 + k')%nat = (k + S k')%nat⌝%I) as %->.
          { iPureIntro; lia. }
          done.
      + iModIntro.
        iIntros (rv) "[%Hil'' Hown]".
        wp_pures.
        iAssert (⌜#k = (inject (k + 0)%nat)⌝%I) as %->.
        { simpl.
          iPureIntro.
          do 2 f_equal.
          lia. }
        wp_apply ("Hf" with "Hhead").
        iIntros (fr) "[-> HΨ]".
        wp_apply wp_fldr_list_cons; [done | ].
        iIntros (v) "%Hil'''".
        iApply "HΦ".
        iSplitL ""; [iPureIntro |].
        { assert (f (k + 0)%nat h :: mapi_loop f (k + 1) l' = mapi_loop f k (h :: l')) as <-.
          { simpl.
            assert ((k + 0)%nat = k) as -> by lia.
            assert (k + 1 = S k)%nat as -> by lia.
            reflexivity. }
          done. }
        simpl.
        iSplitL "HΨ".
        { assert (f k h = f (k + 0)%nat h) as ->.
          { assert (k = (k + 0))%nat as <- by lia; done. }
          done. }
        iAssert (⌜(k + 1)%nat = S k⌝%I) as %->.
        { iPureIntro.
          do 2 f_equal.
          lia. }
        iApply (big_sepL_impl with "Hown").
        iModIntro.
        iIntros (k' x) "_ HΨ".
        iAssert (⌜(S k + k')%nat = (k + S k')%nat⌝%I) as %->.
        { iPureIntro.
          lia. }
        done.
  Qed.

  Lemma wp_fldr_list_mapi `{!Inject B val}
        (f : nat -> A -> B) (l : list A) (fv lv : val)
        (γ : nat -> A -> iProp Σ) (ψ : nat -> B -> iProp Σ) E :
    {{{ □ (∀ (i : nat) (x : A),
              {{{ γ i x }}}
                fv #i (inject x) @ E
                {{{ fr, RET fr;
                    let r := f i x in
                    ⌜fr = (inject r)⌝ ∗ ψ i r }}}) ∗
        ⌜is_list l lv⌝ ∗
        ([∗ list] i ↦ a ∈ l, γ i a)
    }}}
      list_mapi fv lv @ E
    {{{ rv, RET rv;
        let l' := mapi f l in
        ⌜is_list l' rv⌝ ∗
        ([∗ list] i ↦ a ∈ l', ψ i a)}}}.
  Proof.
    iIntros (Φ) "[#Hf [%Hil Hown]] HΦ".
    rewrite /list_mapi.
    do 3 wp_pure _.
    iAssert (⌜#0 = #(0%nat)⌝%I) as %->; [done |].
    iApply (wp_fldr_list_mapi_loop with "[Hown]").
    - iSplitL ""; last first.
      + iFrame; done.
      + iModIntro.
        iIntros (i x).
        iAssert (⌜(0 + i)%nat = i⌝%I) as %->; [done |].
        iApply "Hf".
    - iModIntro.
      assert (mapi f l = mapi_loop f 0 l) as <-; [done |].
      iFrame.
  Qed.

End FldrListHelpersExtra.

(** * 2. Tachis twins of [preprocessing.v]'s table-construction lemmas.

    Same statements as [preprocessing.v]'s [twp_fldr_*] lemmas, with
    Tachis's WP ([{{{ }}}]) in place of Eris's total WP ([ [[{ }]] ]); the
    proof scripts port near-verbatim, using Section 1's [wp_fldr_list_*] in
    place of [twp_list_*]/[twp_fldr_list_total]'s [twp_list_*].  The pure
    combinatorial lemmas from [preprocessing.v] ([fldr_weight_sum_snoc],
    [mapi_pair_indexed], [fldr_rem_nat], [fldr_row_bool], [reverse_eq_rev],
    [fldr_row_pred], [fldr_lit_nat]) are reused directly: none of them
    mention [erisGS]/[Σ] in their statement or proof (as [About] shows), so
    closing [preprocessing.v]'s section erases that unused parameter and
    they come through GS-free. *)

Section FldrTablePreprocess.
  Context `{!tachisGS Σ CostEntropy_2}.

  Lemma wp_fldr_weight_sum E (ws : list nat) (vws : val) :
    {{{ ⌜is_list ws vws⌝ }}}
      fldr_weight_sum vws @ E
    {{{ v, RET #v; ⌜v = weight_sum ws⌝ }}}.
  Proof.
    iIntros (Φ) "%Hws HΦ".
    unfold fldr_weight_sum.
    wp_pures.
    iApply (wp_fldr_list_fold
      (fun lacc acc => ⌜acc = #(weight_sum lacc)⌝%I)
      (fun _ => True%I) (fun _ => True%I)
      E (λ: "acc" "w", "acc" + "w") ws #0 vws).
    - iIntros (a acc lacc lrem).
      iIntros (Φ') "!> Hpre Hcont".
      iDestruct "Hpre" as "[%Hsplit [%Hacc _]]".
      subst acc.
      wp_pures.
      iModIntro.
      iApply ("Hcont" $! _).
      iSplit.
      + iPureIntro. rewrite fldr_weight_sum_snoc. simpl. f_equal.
        rewrite Nat2Z.inj_add. reflexivity.
      + done.
    - iSplit.
      + done.
      + iSplit.
        * iPureIntro. simpl. reflexivity.
        * done.
    - iNext. iIntros (v) "[%Hacc _]".
      subst v.
      iApply ("HΦ" $! (weight_sum ws)).
      iPureIntro. reflexivity.
  Qed.

  Lemma wp_fldr_pow2_aux E (k d : nat) :
      d = k ->
      {{{ True }}}
        fldr_pow2 (fldr_lit_nat k) @ E
      {{{ v, RET #v; ⌜v = (2 ^ k)%nat⌝ }}}.
  Proof.
    induction k as [|k IH] in d |- *.
    - intros Hd.
      iIntros (Φ) "_ HΦ".
      unfold fldr_pow2, fldr_lit_nat.
      wp_rec; wp_pures.
      iApply ("HΦ" $! (2 ^ 0)%nat).
      iPureIntro. simpl. reflexivity.
    - intros Hd.
      iIntros (Φ) "_ HΦ".
      unfold fldr_pow2, fldr_lit_nat.
      wp_rec; wp_pure _.
      wp_if.
      wp_op.
      assert (Hsub : #(Z.sub (Z.of_nat (S k)) 1) = #(k)%nat).
      { change (LitV (LitInt (Z.sub (Z.of_nat (S k)) 1)) =
                  LitV (LitInt (Z.of_nat k))).
        do 2 f_equal. rewrite Nat2Z.inj_succ. rewrite Z.sub_1_r. apply Z.pred_succ. }
      rewrite Hsub.
      fold fldr_pow2.
      wp_bind (fldr_pow2 (fldr_lit_nat k)).
      wp_apply (IH k eq_refl); [done|].
      iIntros (v) "%Hv".
      wp_pures.
      subst v.
      iModIntro.
      assert (Hmul : LitV (LitInt (Z.mul (Z.of_nat 2) (Z.of_nat (2 ^ k))) ) =
                       LitV (LitInt (Z.of_nat (2 * 2 ^ k)))).
      { do 2 f_equal. rewrite Nat2Z.inj_mul. reflexivity. }
      rewrite Hmul.
      iApply ("HΦ" $! (2 * 2 ^ k)%nat).
      iPureIntro. simpl. lia.
  Qed.

  Lemma wp_fldr_pow2 E (k : nat) :
    {{{ True }}} fldr_pow2 (fldr_lit_nat k) @ E
    {{{ v, RET #v; ⌜v = (2 ^ k)%nat⌝ }}}.
  Proof.
    iIntros (Φ) "H HΦ".
    iApply (wp_fldr_pow2_aux E k k eq_refl with "H HΦ").
  Qed.

  Lemma wp_fldr_width_aux E (m pow k d : nat) :
      pow = (2 ^ k)%nat -> (k <= Nat.log2_up m)%nat -> d = (Nat.log2_up m - k)%nat ->
      {{{ True }}}
        fldr_width (fldr_lit_nat m) (fldr_lit_nat pow) (fldr_lit_nat k) @ E
      {{{ v, RET #v; ⌜v = Nat.log2_up m⌝ }}}.
  Proof.
    induction d as [|d IH] in m, pow, k |- *.
    - intros Hpow Hk Hd.
      iIntros (Φ) "_ HΦ".
      unfold fldr_lit_nat in *.
      unfold fldr_width.
      wp_rec; wp_pures.
      case_bool_decide as Hcmp.
      + wp_pures.
        assert (Hlog : Nat.log2_up m = k) by lia.
        iApply ("HΦ" $! k).
        iPureIntro. simpl. now rewrite Hlog.
      + exfalso.
        assert (Hmpos : (0 < m)%nat).
        { destruct (Nat.eq_dec m 0) as [->|Hm]; [lia|lia]. }
        pose proof (Nat.log2_log2_up_spec m Hmpos) as [_ Hupper].
        assert (Hlog : Nat.log2_up m = k) by lia.
        subst pow.
        assert (Hcmp_nat : ~ (m <= 2 ^ k)%nat).
        { intros H. apply Hcmp. lia. }
        exfalso. apply Hcmp_nat. now rewrite <- Hlog.
    - intros Hpow Hk Hd.
      iIntros (Φ) "_ HΦ".
      unfold fldr_lit_nat in *.
      unfold fldr_width.
      wp_rec; wp_pures.
      case_bool_decide as Hcmp.
      + wp_pures. exfalso.
        assert (Hlog_gt : (k < Nat.log2_up m)%nat) by lia.
        assert (Hmgt1 : (1 < m)%nat).
        { destruct (le_lt_dec m 1) as [Hm|Hm].
          - pose proof (proj2 (Nat.log2_up_null m) Hm) as Hzero. lia.
          - exact Hm. }
        pose proof (Nat.log2_up_spec m Hmgt1) as [Hlower _].
        assert (Hpred : (k <= Nat.pred (Nat.log2_up m))%nat) by lia.
        pose proof (Nat.pow_le_mono_r 2 k (Nat.pred (Nat.log2_up m)) ltac:(lia) Hpred) as Hpowle.
        assert (Hcmp_nat : (m <= pow)%nat) by lia.
        rewrite Hpow in Hcmp_nat.
        lia.
      + wp_pure.
        fold fldr_width.
        assert (Hpow' : 2 * pow = (2 ^ (k + 1))%nat).
        { rewrite Hpow. replace (k + 1)%nat with (S k) by lia.
          rewrite Nat.pow_succ_r'. lia. }
        assert (Hk' : (k + 1 <= Nat.log2_up m)%nat) by lia.
        assert (Hd' : d = (Nat.log2_up m - (k + 1))%nat) by lia.
        wp_op.
        wp_op.
        fold fldr_width.
        assert (HpowZ : Z.mul (Z.of_nat 2) (Z.of_nat pow) = Z.of_nat (2 * pow)).
        { rewrite <- Nat2Z.inj_mul. reflexivity. }
        assert (HkZ : Z.add (Z.of_nat k) (Z.of_nat 1) = Z.of_nat (k + 1)).
        { rewrite <- Nat2Z.inj_add. reflexivity. }
        rewrite HpowZ HkZ.
        iApply (IH m (2 * pow) (k + 1) Hpow' Hk' Hd' with "[//] HΦ").
  Qed.

  Lemma wp_fldr_width E (m : nat) :
      0 < m ->
      {{{ True }}}
        fldr_width (fldr_lit_nat m) #1 #0 @ E
      {{{ v, RET #v; ⌜v = Nat.log2_up m⌝ }}}.
  Proof.
    intros Hm.
    iIntros (Φ) "_ HΦ".
    iApply (wp_fldr_width_aux E m 1 0 (Nat.log2_up m)
      ltac:(simpl; lia) ltac:(lia) ltac:(lia) with "[//] HΦ").
  Qed.

  Lemma wp_fldr_extend E (ws : list nat) (vws : val) (den m : nat) :
      m <= den ->
      {{{ ⌜is_list ws vws⌝ }}}
        fldr_extend vws (fldr_lit_nat den) (fldr_lit_nat m) @ E
      {{{ v, RET v; ⌜is_list (ws ++ [den - m]) v⌝ }}}.
  Proof.
    intros Hle.
    iIntros (Φ) "%Hws HΦ".
    rewrite /fldr_extend.
    wp_pures.
    assert (Hsub : Z.sub (Z.of_nat den) (Z.of_nat m) = Z.of_nat (den - m)).
    { rewrite <- Nat2Z.inj_sub by lia. reflexivity. }
    rewrite Hsub.
    wp_bind (list_cons #(den - m)%nat (InjLV #())).
    wp_apply (wp_fldr_list_cons (den - m)%nat [] (InjLV #()) E); [done|].
    iIntros (vone) "%Vone".
    wp_apply (wp_fldr_list_append E vws ws vone [den - m]);
      [iPureIntro; split; assumption|].
    iIntros (v) "%Hv".
    iApply ("HΦ" $! v). iPureIntro. exact Hv.
  Qed.

  Lemma wp_fldr_pair E (i x : nat) :
    {{{ True }}}
      (λ: "i" "w", ("i", "w"))%V #i (inject x) @ E
    {{{ fr, RET fr; ⌜fr = inject (i, x)⌝ ∗ True }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_pures.
    iApply ("HΦ" $! (PairV (inject i) (inject x))).
    iModIntro. iSplit; [iPureIntro; reflexivity|done].
  Qed.

  Lemma wp_fldr_index E (l : list nat) (vl : val) :
    {{{ ⌜is_list l vl⌝ }}}
      fldr_index vl @ E
    {{{ v, RET v; ⌜is_list (indexed_weights l) v⌝ }}}.
  Proof.
    iIntros (Φ) "%Hl HΦ".
    rewrite /fldr_index.
    wp_pures.
    wp_apply (wp_fldr_list_mapi (A := nat) (B := nat * nat)
      (fun i w => (i, w)) l
      (λ: "i" "w", ("i", "w"))%V vl
      (fun _ _ => True%I) (fun _ _ => True%I) E).
    - iSplitR.
      + iModIntro. iIntros (i x).
        iIntros (Ψ) "!> _ HΨ".
        wp_pures.
        iApply ("HΨ" $! (PairV (inject i) (inject x))).
        iModIntro. iSplit; [iPureIntro; reflexivity|done].
      + iSplitL "".
        * iPureIntro; exact Hl.
        * iPureIntro. induction l; simpl; auto.
    - iIntros (v) "Hv".
      iApply ("HΦ" $! v).
      iDestruct "Hv" as "[%Hv' _]".
      iPureIntro. rewrite mapi_pair_indexed in Hv'. exact Hv'.
  Qed.

  Lemma wp_fldr_row_pred E (iw : nat * nat) :
    {{{ True }}}
      (λ: "iw", (Snd "iw") `rem` #2 = #1)%V (inject iw) @ E
    {{{ v, RET v; ⌜v = inject (fldr_row_pred iw)⌝ }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    destruct iw as [i w]. simpl [fldr_row_pred].
    wp_pures.
    assert (Hrem : #(Z.rem (Z.of_nat w) (2%Z)) = #(w mod 2)%nat).
    { change (LitV (LitInt (Z.rem (Z.of_nat w) (2%Z))) =
                LitV (LitInt (Z.of_nat (w mod 2)))).
      do 2 f_equal. apply fldr_rem_nat. }
    rewrite Hrem.
    assert (Hbool :
      LitV (LitBool
        (bool_decide (LitV (LitInt (Z.of_nat (w mod 2))) = LitV (LitInt 1)))) =
      LitV (LitBool (Nat.eqb (w mod 2) 1))) by apply fldr_row_bool.
    rewrite Hbool.
    iModIntro. iApply ("HΦ" $! (inject (fldr_row_pred (i,w)))).
    iPureIntro. reflexivity.
  Qed.

  Lemma wp_fldr_fst E (iw : nat * nat) :
    {{{ True }}}
      (λ: "iw", Fst "iw")%V (inject iw) @ E
    {{{ v, RET v; ⌜v = inject (fst iw)⌝ }}}.
  Proof.
    iIntros (Φ) "_ HΦ". destruct iw as [i w].
    wp_pures. iApply ("HΦ" $! (inject i)).
    iModIntro. iPureIntro. reflexivity.
  Qed.

  Lemma wp_fldr_one_row E (iws : list (nat * nat)) (viws : val) :
    {{{ ⌜is_list iws viws⌝ }}}
      fldr_one_row viws @ E
    {{{ v, RET v; ⌜is_list (one_row iws) v⌝ }}}.
  Proof.
    iIntros (Φ) "%Hiws HΦ".
    rewrite /fldr_one_row.
    wp_pures.
    wp_apply (wp_fldr_list_filter (A := nat * nat) iws fldr_row_pred
      (λ: "iw", (Snd "iw") `rem` #2 = #1)%V viws E).
    - iSplitR.
      + iIntros (iw).
        iIntros (Ψ) "!> _ HΨ".
        destruct iw as [i w]. simpl [fldr_row_pred].
        wp_pures.
        assert (Hrem : #(Z.rem (Z.of_nat w) (2%Z)) = #(w mod 2)%nat).
        { change (LitV (LitInt (Z.rem (Z.of_nat w) (2%Z))) =
                    LitV (LitInt (Z.of_nat (w mod 2)))).
          do 2 f_equal. apply fldr_rem_nat. }
        rewrite Hrem.
        rewrite fldr_row_bool.
        iApply ("HΨ" $! (inject (fldr_row_pred (i,w)))).
        iModIntro. iPureIntro. reflexivity.
      + done.
    - iIntros (vf) "%Hf".
      wp_bind (list_map (λ: "iw", Fst "iw")%E vf).
      wp_pures.
      wp_apply (wp_fldr_list_map_pure (A := nat * nat) (B := nat)
        (List.filter fldr_row_pred iws) (fun iw => fst iw)
        (λ: "iw", Fst "iw")%V vf E).
      + iSplitR.
        * iIntros (iw).
          iIntros (Ψ) "!> _ HΨ".
          destruct iw as [i w]. wp_pures.
          iApply ("HΨ" $! (inject i)).
          iModIntro. iPureIntro. reflexivity.
        * done.
      + iIntros (v) "%Hm".
        iApply ("HΦ" $! v).
        iPureIntro. exact Hm.
  Qed.

  Lemma wp_fldr_shift E (iws : list (nat * nat)) (viws : val) :
    {{{ ⌜is_list iws viws⌝ }}}
      fldr_shift viws @ E
    {{{ v, RET v; ⌜is_list (shift_weights iws) v⌝ }}}.
  Proof.
    iIntros (Φ) "%Hiws HΦ".
    rewrite /fldr_shift.
    wp_pures.
    wp_apply (wp_fldr_list_map_pure (A := nat * nat) (B := nat * nat)
      iws (fun iw => (fst iw, snd iw / 2))
      (λ: "iw", (Fst "iw", (Snd "iw") `quot` #2))%V viws E).
    - iSplitR.
      + iIntros (iw).
        iIntros (Ψ) "!> _ HΨ".
        destruct iw as [i w]. simpl.
        wp_pures.
        assert (Hq : #(Z.quot (Z.of_nat w) 2) = #(w / 2)%nat).
        { change (LitV (LitInt (Z.quot (Z.of_nat w) 2)) =
                    LitV (LitInt (Z.of_nat (w / 2)))).
          do 2 f_equal.
          rewrite <- (nat_N_Z w).
          replace (2%Z) with (Z.of_nat 2) by reflexivity.
          rewrite <- (nat_N_Z 2).
          rewrite <- (N2Z.inj_quot (N.of_nat w) (N.of_nat 2)).
          rewrite <- (nat_N_Z (w / 2)).
          rewrite <- (Nat2N.inj_div w 2).
          reflexivity. }
        rewrite Hq.
        iApply ("HΨ" $! (inject (i, w / 2))).
        iModIntro. iPureIntro. reflexivity.
      + done.
    - iIntros (v) "%Hm".
      iApply ("HΦ" $! v).
      iPureIntro. exact Hm.
  Qed.

  Lemma wp_fldr_rows_lsb E (fuel : nat) (iws : list (nat * nat)) (viws : val) :
    {{{ ⌜is_list iws viws⌝ }}}
      fldr_rows_lsb #fuel viws @ E
    {{{ v, RET v; ⌜is_list (rows_lsb fuel iws) v⌝ }}}.
  Proof.
    induction fuel as [|fuel IH] in iws, viws |- *.
    - iIntros (Φ) "%Hiws HΦ".
      rewrite /fldr_rows_lsb.
      wp_rec; wp_pures.
      iModIntro.
      iApply ("HΦ" $! (InjLV #())).
      iPureIntro. reflexivity.
    - iIntros (Φ) "%Hiws HΦ".
      rewrite /fldr_rows_lsb.
      wp_rec; wp_pures.
      wp_bind (fldr_shift viws).
      wp_apply (wp_fldr_shift E iws viws); [done|].
      iIntros (vs) "%Hs".
      wp_op.
      assert (Hsub : #(Z.sub (Z.of_nat (S fuel)) 1) = #(fuel)%nat).
      { change (LitV (LitInt (Z.sub (Z.of_nat (S fuel)) 1)) =
                  LitV (LitInt (Z.of_nat fuel))).
        do 2 f_equal. rewrite Nat2Z.inj_succ. rewrite Z.sub_1_r. apply Z.pred_succ. }
      rewrite Hsub.
      wp_bind (fldr_rows_lsb #fuel vs).
      fold fldr_rows_lsb.
      wp_apply (IH (shift_weights iws) vs); [iPureIntro; exact Hs|].
      iIntros (vt) "%Ht".
      wp_bind (fldr_one_row viws)%E.
      wp_apply (wp_fldr_one_row E iws viws); [done|].
      iIntros (vr) "%Hrow".
      rewrite /list_cons.
      wp_pures.
      iModIntro.
      iApply ("HΦ" $! (InjRV (PairV vr vt))).
      iPureIntro.
      apply (proj1 (is_list_inject _ _)) in Hrow.
      rewrite Hrow.
      exists vt. split; [reflexivity|exact Ht].
  Qed.

  (** The target lemma of this section: builds the full DDG table. *)
  Lemma wp_fldr_table E (ws : list nat) (vws : val) :
    admissible ws ->
    {{{ ⌜is_list ws vws⌝ }}}
      fldr_table vws @ E
    {{{ v, RET v; ⌜is_list (ddg_table ws) v⌝ }}}.
  Proof.
    intros Hadm.
    iIntros (Φ) "%Hws HΦ".
    rewrite /fldr_table.
    wp_pures.
    wp_bind (fldr_weight_sum vws).
    wp_apply (wp_fldr_weight_sum E ws vws); [done|].
    iIntros (m) "%Hm".
    wp_let.
    wp_bind (fldr_width (fldr_lit_nat m) #1 #0).
    wp_apply (wp_fldr_width E m); [rewrite Hm; exact (admissible_weight_sum_pos _ Hadm)|done|].
    iIntros (k) "%Hk".
    wp_let.
    wp_bind (fldr_pow2 (fldr_lit_nat k)).
    wp_apply (wp_fldr_pow2 E k); [done|].
    iIntros (den) "%Hden".
    wp_let.
    rewrite Hden.
    wp_bind (fldr_extend vws (fldr_lit_nat (2 ^ k)) (fldr_lit_nat m)).
    assert (Hle : (m <= 2 ^ k)%nat).
    { pose proof (proj1 (denominator_bounds ws Hadm)) as Hb.
      unfold denominator, dyadic_width in Hb.
      rewrite Hm in Hk.
      rewrite Hm. rewrite Hk. exact Hb. }
    wp_apply (wp_fldr_extend E ws vws (2 ^ k) m); [exact Hle|done|].
    iIntros (ext) "%Hext".
    wp_let.
    assert (Hext' : is_list (extended_weights ws) ext).
    { unfold extended_weights, rejection_weight, denominator, dyadic_width.
      rewrite Hm in Hext.
      rewrite Hm in Hk.
      rewrite <- Hk. exact Hext. }
    wp_bind (fldr_index _).
    wp_apply (wp_fldr_index E (extended_weights ws) ext); [iPureIntro; exact Hext'|].
    iIntros (viws) "%Hiws".
    wp_bind (fldr_rows_lsb (fldr_lit_nat k) viws).
    wp_apply (wp_fldr_rows_lsb E k (indexed_weights (extended_weights ws)) viws);
      [iPureIntro; exact Hiws|].
    iIntros (vr) "%Hr".
    wp_bind (list_rev vr).
    wp_apply (wp_fldr_list_rev E vr (rows_lsb k (indexed_weights (extended_weights ws))));
      [iPureIntro; exact Hr|].
    iIntros (v) "%Hv".
    iApply ("HΦ" $! v).
    iPureIntro.
    rewrite reverse_eq_rev in Hv.
    unfold ddg_table.
    assert (Hdepth : k = dyadic_width ws).
    { unfold dyadic_width. rewrite Hm in Hk. exact Hk. }
    rewrite Hdepth in Hv.
    exact Hv.
  Qed.

End FldrTablePreprocess.

#[local] Open Scope R.

(** * 3. Bridge: Eris's [is_list] representation to [entropy_cost.v]'s
    bespoke [is_row]/[is_rows].

    [is_row]/[is_rows] ([entropy_cost.v], Section 4) are, by construction,
    the SAME recursive shape as [is_list] specialized at [Inject nat val]
    (for rows) and [Inject (list nat) val] (for tables) -- the only
    difference is that [is_rows]' inductive step existentially quantifies
    the row's own representation ([vr]) rather than hard-wiring it to
    [inject r], so the bridge instantiates that existential with [inject r]
    and discharges the resulting [is_row r (inject r)] via [is_list_is_row]
    together with [is_list_inject]. *)

Lemma is_list_is_row (l : list nat) (v : val) : is_list l v -> is_row l v.
Proof.
  induction l as [|n l' IH] in v |- *; simpl.
  - done.
  - intros (lv & -> & Hl'). exists lv. split; [done | by apply IH].
Qed.

Lemma is_list_is_rows (rows : list (list nat)) (v : val) :
  is_list rows v -> is_rows rows v.
Proof.
  induction rows as [|r rows' IH] in v |- *; simpl.
  - done.
  - intros (lv & -> & Hrest).
    exists (inject r), lv.
    split; [done|].
    split; [|by apply IH].
    apply is_list_is_row.
    apply (proj2 (is_list_inject r (inject r))).
    reflexivity.
Qed.

(** * 4. The entry-point triples.

    [wp_fldr_tape_flip_cost] handles the [n = 1] guard branch honestly: it
    returns [#0] with zero cost (the postcondition [0 < 1] holds trivially),
    and the unused credit [⧖ (flip_cost ws)] is simply dropped -- Iris's
    base logic is affine, so discarding an unused resource needs no lemma.
    In the other branch, [wp_fldr_table] builds the table, the Section-3
    bridge converts its [is_list] postcondition to [is_rows], and
    [wp_fldr_loop_flip_cost] (from [entropy_cost.v]) finishes.
    [wp_fldr_flip_cost]/[wp_fldr_sample_flip_cost] are one [wp_pures] (a
    single beta/read step, at [fldr]/[fldr_sample fldr_unit_loc]
    respectively) away from [wp_fldr_tape_flip_cost] at [vws := inject ws]. *)

Section FldrEntry.
  Context `{!tachisGS Σ CostEntropy_2}.

  Lemma wp_fldr_tape_flip_cost E (ws : list nat) (vws : val) :
    admissible ws -> nondegenerate ws ->
    {{{ ⌜is_list ws vws⌝ ∗ ⧖ (flip_cost ws) }}}
      fldr_tape #() vws @ E
    {{{ i, RET #i; ⌜(i < length ws)%nat⌝ }}}.
  Proof.
    iIntros (Hadm Hnd Φ) "[%Hws Hcred] HΦ".
    rewrite /fldr_tape. wp_pures.
    wp_bind (list_length vws).
    wp_apply (wp_list_length_row with "[]").
    { iPureIntro. by apply is_list_is_row. }
    iIntros (n) "%Hn".
    rewrite Hn.
    destruct (decide (length ws = 1%nat)) as [Hone|Hnotone].
    - wp_pures; case_bool_decide as Hcond.
      + wp_pures. iApply ("HΦ" $! 0%nat). iPureIntro. rewrite Hone. lia.
      + exfalso. apply Hcond. rewrite Hone. reflexivity.
    - wp_pures; case_bool_decide as Hcond.
      + exfalso. apply Hnotone.
        change (LitV (LitInt (Z.of_nat (length ws))) = LitV (LitInt 1%Z)) in Hcond.
        inversion Hcond. lia.
      + wp_pures.
        wp_bind (fldr_table vws).
        wp_apply (wp_fldr_table E ws vws Hadm); [done|].
        iIntros (vrows) "%Hrows".
        wp_pures.
        wp_apply (wp_fldr_loop_flip_cost E ws vrows Hadm Hnd with "[Hcred]").
        * iSplit; [iPureIntro; by apply is_list_is_rows | iExact "Hcred"].
        * iIntros (i) "%Hi". iApply "HΦ". iPureIntro. exact Hi.
  Qed.

  Lemma wp_fldr_flip_cost E (ws : list nat) :
    admissible ws -> nondegenerate ws ->
    {{{ ⧖ (flip_cost ws) }}}
      fldr (inject ws) @ E
    {{{ i, RET #i; ⌜(i < length ws)%nat⌝ }}}.
  Proof.
    iIntros (Hadm Hnd Φ) "Hcred HΦ".
    rewrite /fldr. wp_pures.
    wp_apply (wp_fldr_tape_flip_cost E ws (inject ws) Hadm Hnd with "[Hcred]").
    - iSplit; [iPureIntro; apply (proj2 (is_list_inject ws (inject ws))); reflexivity
              | iExact "Hcred"].
    - iIntros (i) "%Hi". iApply "HΦ". iPureIntro. exact Hi.
  Qed.

  Lemma wp_fldr_sample_flip_cost E (ws : list nat) :
    admissible ws -> nondegenerate ws ->
    {{{ ⧖ (flip_cost ws) }}}
      fldr_sample ws fldr_unit_loc @ E
    {{{ i, RET #i; ⌜(i < length ws)%nat⌝ }}}.
  Proof.
    iIntros (Hadm Hnd Φ) "Hcred HΦ".
    rewrite /fldr_sample /fldr_unit_loc. wp_pures.
    wp_apply (wp_fldr_tape_flip_cost E ws (inject ws) Hadm Hnd with "[Hcred]").
    - iSplit; [iPureIntro; apply (proj2 (is_list_inject ws (inject ws))); reflexivity
              | iExact "Hcred"].
    - iIntros (i) "%Hi". iApply "HΦ". iPureIntro. exact Hi.
  Qed.

End FldrEntry.

(** * 5. ERT corollaries: the headline theorems of this file.

    Mirrors [entropy_cost.v]'s [fldr_loop_ERT_bound]/[fldr_loop_ERT_bound_lim]
    exactly, at the two real entry points [fldr (inject ws)] and
    [fldr_sample ws fldr_unit_loc]. *)

Corollary fldr_ERT_bound Σ `{!tachisGpreS Σ} (ws : list nat) (σ : state) (k : nat) :
  admissible ws -> nondegenerate ws ->
  ERT (costfun := CostEntropy_2) k (fldr (inject ws), σ) <= flip_cost ws.
Proof.
  intros Hadm Hnd.
  pose proof (flip_cost_nonneg ws Hadm Hnd) as Hnn.
  apply (wp_ERT CostEntropy_2 Σ _ σ k (mknonnegreal (flip_cost ws) Hnn)
           (fun v => exists i : nat, v = #i /\ (i < length ws)%nat)).
  iIntros (?) "Hx".
  wp_apply (wp_fldr_flip_cost with "[Hx]"); [exact Hadm|exact Hnd| |].
  - iExact "Hx".
  - iIntros (i) "%Hi". iPureIntro. eauto.
Qed.

Corollary fldr_ERT_bound_lim Σ `{!tachisGpreS Σ} (ws : list nat) (σ : state) :
  admissible ws -> nondegenerate ws ->
  lim_ERT (costfun := CostEntropy_2) (fldr (inject ws), σ) <= flip_cost ws.
Proof.
  intros Hadm Hnd.
  pose proof (flip_cost_nonneg ws Hadm Hnd) as Hnn.
  unshelve epose proof (wp_ERT_lim CostEntropy_2 Σ
           (fldr (inject ws)) σ (mknonnegreal (flip_cost ws) Hnn)
           (fun v => exists i : nat, v = #i /\ (i < length ws)%nat) _) as H.
  { iIntros (?) "Hx".
    wp_apply (wp_fldr_flip_cost with "[Hx]"); [exact Hadm|exact Hnd| |].
    - iExact "Hx".
    - iIntros (i) "%Hi". iPureIntro. eauto. }
  apply H.
Qed.

Corollary fldr_sample_ERT_bound Σ `{!tachisGpreS Σ} (ws : list nat) (σ : state) (k : nat) :
  admissible ws -> nondegenerate ws ->
  ERT (costfun := CostEntropy_2) k (fldr_sample ws fldr_unit_loc, σ) <= flip_cost ws.
Proof.
  intros Hadm Hnd.
  pose proof (flip_cost_nonneg ws Hadm Hnd) as Hnn.
  apply (wp_ERT CostEntropy_2 Σ _ σ k (mknonnegreal (flip_cost ws) Hnn)
           (fun v => exists i : nat, v = #i /\ (i < length ws)%nat)).
  iIntros (?) "Hx".
  wp_apply (wp_fldr_sample_flip_cost with "[Hx]"); [exact Hadm|exact Hnd| |].
  - iExact "Hx".
  - iIntros (i) "%Hi". iPureIntro. eauto.
Qed.

Corollary fldr_sample_ERT_bound_lim Σ `{!tachisGpreS Σ} (ws : list nat) (σ : state) :
  admissible ws -> nondegenerate ws ->
  lim_ERT (costfun := CostEntropy_2) (fldr_sample ws fldr_unit_loc, σ) <= flip_cost ws.
Proof.
  intros Hadm Hnd.
  pose proof (flip_cost_nonneg ws Hadm Hnd) as Hnn.
  unshelve epose proof (wp_ERT_lim CostEntropy_2 Σ
           (fldr_sample ws fldr_unit_loc) σ (mknonnegreal (flip_cost ws) Hnn)
           (fun v => exists i : nat, v = #i /\ (i < length ws)%nat) _) as H.
  { iIntros (?) "Hx".
    wp_apply (wp_fldr_sample_flip_cost with "[Hx]"); [exact Hadm|exact Hnd| |].
    - iExact "Hx".
    - iIntros (i) "%Hi". iPureIntro. eauto. }
  apply H.
Qed.
