From stdpp Require Import strings list pretty gmap.
From iris.base_logic.lib Require Import fancy_updates.
From clutch.common Require Import inject.
From clutch.prob_lang Require Export lang notation gwp.gen_weakestpre gwp.list.

Section map_code.
Definition map_empty : val := λ: <>, [].

Definition map_remove : val :=
  λ: "key",
    rec: "loop" "m" :=
      match: "m" with
        NONE => NONE
      | SOME "x" =>
          let, ("p", "m") := "x" in
          if: Fst "p" = "key"
          then "m"
          else "p" :: "loop" "m"
      end.

Definition map_insert : val :=
  λ: "key" "value" "m", ("key", "value") :: map_remove "key" "m".

Definition map_lookup : val :=
  λ: "key", rec: "loop" "m" :=
  match: "m" with
    NONE => NONE
  | SOME "x" =>
      let, ("p", "m") := "x" in
      if: Fst "p" = "key"
      then SOME (Snd "p")
      else "loop" "m"
  end.

Definition map_mem : val :=
  λ: "k" "m",
  match: map_lookup "k" "m" with
    NONE => #false
  | SOME "_p" => #true
  end.

Definition map_iter : val :=
  rec: "map_iter" "f" "m" :=
  match: "m" with
    NONE => #()
  | SOME "x" =>
      let, ("p", "m") := "x" in
      "f" (Fst "p") (Snd "x");;
      "map_iter" "f" "m"
  end.

Definition map_forall : val :=
  rec: "map_forall" "f" "m" :=
  match: "m" with
    NONE => #true
  | SOME "x" =>
      let, ("p", "m") := "x" in
      ("f" (Fst "p") (Snd "p")) && "map_forall" "f" "m"
  end.

End map_code.

Section map_specs.
  Context `{invGS_gen hlc Σ} `{g : !GenWp Σ}.
  Context `[Countable K, !Inject K val].
  Context `[V : Type, !Inject V val].

  Implicit Types k : K.

  Definition is_map (d : val) (m : gmap K V) : Prop :=
    ∃ l, m = list_to_map l ∧ d = inject l ∧ NoDup (fst <$> l).

  Lemma gwp_map_empty s E :
    G{{{ True }}}
      map_empty #() @ s; E
    {{{ v, RET v; ⌜is_map v ∅⌝}}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    gwp_rec. gwp_pures. iApply "HΦ".
    iModIntro. iPureIntro.
    exists []. do 2 (split; [done|]). constructor.
  Qed.

  Lemma gwp_map_remove s E k d m :
    val_is_unboxed (inject k) →
    G{{{ ⌜is_map d m⌝ }}}
      map_remove (inject k) (Val d) @ s; E
    {{{ d', RET d'; ⌜is_map d' (delete k m)⌝ }}}.
  Proof.
    iIntros (? Φ (l & -> & -> & Hdup)) "HΦ".
    gwp_rec. gwp_closure.
    iInduction l as [|[k' v] l] "IH" forall (Hdup Φ) "HΦ".
    - gwp_pures. iApply "HΦ". iIntros "!%".
      exists []. rewrite delete_empty //=.
    - inversion Hdup; simplify_eq.
      gwp_pures.
      case_bool_decide as Heq; simplify_eq.
      + gwp_pures. iApply "HΦ".
        iIntros "!> /= !%".
        rewrite delete_insert.
        * by eexists.
        * by apply not_elem_of_list_to_map.
      + gwp_if.
        gwp_apply ("IH" with "[//]").
        iIntros (d' (l' & Hl' & -> & ?)).
        gwp_pures.
        gwp_apply (gwp_list_cons (k',v)).
        { rewrite is_list_inject //. }
        iIntros (? ->%is_list_inject). iApply "HΦ". iPureIntro.
        destruct (decide (k = k')); simplify_eq.
        eexists ((k', v) :: l') => /=.
        rewrite delete_insert_ne //=.
        split; [congruence|].
        split; [done|].
        constructor; [|done].
        apply not_elem_of_list_to_map_2.
        rewrite -Hl' lookup_delete_ne //.
        by apply not_elem_of_list_to_map_1.
  Qed.

  Lemma gwp_map_insert (k : K) v d m s E :
    val_is_unboxed (inject k) →
    G{{{ ⌜is_map d m⌝ }}}
      map_insert (inject k) (inject v) d @ s; E
    {{{ d', RET d'; ⌜is_map d' (<[ k := v ]> m)⌝ }}}.
  Proof.
    iIntros (? Φ (l & -> & -> & Hdup)) "HΦ".
    gwp_rec. gwp_closure.
    gwp_rec. gwp_pures.
    gwp_apply (gwp_map_remove).
    - done.
    - iPureIntro. exists l.
      split; [done|].
      split; [|done].
      by simpl.
    - iIntros (d' (l' & Hl' & -> & ?)). gwp_pures.
      gwp_apply (gwp_list_cons (k, v)).
      { rewrite is_list_inject //. }
      iIntros (? ->%is_list_inject). iApply "HΦ". iPureIntro.
      exists ((k, v) :: l').
      split.
      + rewrite <- insert_delete_insert.
        rewrite Hl'. symmetry. apply list_to_map_cons.
      + split; [done|].
        constructor; last done.
        eapply (not_elem_of_list_to_map_2).
        rewrite -Hl' lookup_delete //.
  Qed.

  Lemma gwp_map_lookup k d m s E :
    val_is_unboxed (inject k) →
    G{{{ ⌜is_map d m⌝ }}}
      map_lookup (inject k) d @ s; E
     {{{ RET (inject (m !! k)); True }}}
    .
  Proof.
    iIntros (? Φ (l & -> & -> & Hdup)) "HΦ".
    gwp_rec. gwp_closure.
    iInduction l as [|[k' v] l'] "IH" forall (Hdup Φ) "HΦ".
    - gwp_pures. iModIntro. by iApply "HΦ".
    - gwp_pures.
      case_bool_decide as Heq; simplify_eq.
      + gwp_if. gwp_pures.
        iModIntro. rewrite lookup_insert /=.
        by iApply "HΦ".
      + gwp_if. gwp_apply "IH".
        * inversion Hdup. by subst.
        * rewrite lookup_insert_ne /=; [done| ]. intros ->. done.
  Qed.

  Lemma gwp_map_mem k d m s E :
    val_is_unboxed (inject k) →
    G{{{ ⌜is_map d m⌝ }}}
      map_mem (inject k) d @ s; E
     {{{ (b : bool), RET #b; if b then ⌜∃ v, m !! k = Some v⌝ else True }}}
    .
  Proof.
    iIntros (? Φ (l & -> & -> & Hdup)) "HΦ".
    gwp_rec. gwp_pure. gwp_pure.
    gwp_apply gwp_map_lookup; [done| |].
    - iPureIntro. by eexists.
    - destruct ((list_to_map l)!!k) eqn:Heq.
      + iIntros "_".
        gwp_pures. iModIntro. iApply "HΦ".
        iPureIntro. by eexists.
      + iIntros "_". gwp_pures.
        iModIntro. iApply "HΦ". done.
  Qed.

  (* TODO: port to GWP - induct on list rather than use Löb induction *)
  (* Lemma gwp_map_iter (Φ Ψ : K → V → iProp Σ) P ip d m f : *)
  (*   (∀ (k : K) (v : V), *)
  (*       {{{ P ∗ Φ k v }}} *)
  (*         (Val f) $k $v @[ip] *)
  (*       {{{ RET #(); P ∗ Ψ k v }}}) -∗ *)
  (*   {{{ ⌜is_map d m⌝ ∗ P ∗ [∗ map] k↦v ∈ m, Φ k v }}} *)
  (*     map_iter (Val f) d @[ip] *)
  (*   {{{ RET #(); P ∗ [∗ map] k↦v ∈ m, Ψ k v }}}. *)
  (* Proof. *)
  (*   iIntros "#Hf" (Ξ) "!# (%Hd & HP & HΦ) HΞ". *)
  (*   iLöb as "IH" forall (Ξ d m Hd); gwp_rec. *)
  (*   gwp_pures. *)
  (*   destruct Hd as (? & -> & -> & Hnodup). *)
  (*   destruct x as [|[k v] l]. *)
  (*   - gwp_pures. iApply "HΞ". by iFrame. *)
  (*   - gwp_pures. simpl. *)
  (*     iDestruct (big_sepM_insert with "HΦ") as "[Hkv Hrest]". *)
  (*     { apply not_elem_of_list_to_map_1. *)
  (*       inversion Hnodup; simplify_eq. set_solver. } *)
  (*     gwp_apply ("Hf" with "[$HP $Hkv]"). *)
  (*     iIntros "[HP HΨ]". *)
  (*     gwp_pures. *)
  (*     gwp_apply ("IH" with "[] HP Hrest"). *)
  (*     { inversion Hnodup. subst. by iExists l. } *)
  (*     iIntros "[HP Hrest]". *)
  (*     iApply "HΞ". *)
  (*     iFrame. *)
  (*     iApply (big_sepM_insert with "[$Hrest $HΨ]"). *)
  (*     apply not_elem_of_list_to_map_1. *)
  (*     inversion Hnodup; simplify_eq. *)
  (*     set_solver. *)
  (*  Qed. *)

  (* Lemma gwp_map_forall Φ Ψ ip d m (f : val) : *)
  (*   (∀ (k : K) (v : V), *)
  (*       {{{ True }}} *)
  (*         f $k $v @[ip] *)
  (*       {{{ (b : bool), RET #b; if b then Φ k v else Ψ k v }}}) -∗ *)
  (*   {{{ ⌜is_map d m⌝ }}} *)
  (*     map_forall f d @[ip] *)
  (*   {{{ (b : bool), RET #b; *)
  (*         if b then [∗ map] k↦v ∈ m, Φ k v *)
  (*         else ∃ k v , ⌜m !! k = Some v⌝ ∗ Ψ k v }}}. *)
  (* Proof. *)
  (*   iIntros "#Hf" (Ξ) "!# %Hd HΞ". *)
  (*   iLöb as "IH" forall (Ξ d m Hd). gwp_rec. *)
  (*   gwp_pures. *)
  (*   destruct Hd as (? & -> & -> & Hnodup). *)
  (*   destruct x as [|[k v] l]. *)
  (*   - gwp_pures. by iApply "HΞ". *)
  (*   - gwp_pures. gwp_apply "Hf"; [done|]. *)
  (*     iIntros ([]) "Hb". *)
  (*     + gwp_pures. *)
  (*       gwp_apply "IH". *)
  (*       { inversion Hnodup. subst. by iExists l. } *)
  (*       iIntros ([]) "HΦ". *)
  (*       { iApply "HΞ". simpl. *)
  (*         iApply (big_sepM_insert with "[$HΦ $Hb]"). *)
  (*         apply not_elem_of_list_to_map_1. *)
  (*         inversion Hnodup; simplify_eq. *)
  (*         set_solver. } *)
  (*       iApply "HΞ". *)
  (*       iDestruct "HΦ" as (??) "[% ?]". *)
  (*       iExists _, _. iFrame. iPureIntro. *)
  (*       simpl. *)
  (*       rewrite lookup_insert_ne //. *)
  (*       inversion Hnodup; simplify_map_eq. *)
  (*       apply elem_of_list_to_map in H1; [|set_solver]. *)
  (*       intros ->. apply H4. *)
  (*       apply elem_of_list_fmap. *)
  (*       exists (k0, v0); done. *)
  (*     + gwp_pures. *)
  (*       iApply "HΞ". *)
  (*       iExists _, _. iFrame. iPureIntro. *)
  (*       rewrite lookup_insert //. *)
  (* Qed. *)

End map_specs.

Global Arguments gwp_map_empty {_ _ _ _} _ {_ _ _} _.
