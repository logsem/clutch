From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import adequacy diffpriv proofmode.
From clutch.prob_lang Require Import gwp.list.

(* TODO: upstream to gwp.list *)
Definition list_hd : val :=
  λ:"xs", match: "xs" with NONE => #0 #0 | SOME "x_xs" => Fst "x_xs" end.

Definition list_tl : val :=
  λ:"xs", match: "xs" with NONE => "xs" | SOME "x_xs" => Snd "x_xs" end.

Definition list_max_index_aux : val :=
  λ:"y" "xs",
    list_fold
      (λ: "(y, iy, ix)" "x",
         let, ("y", "iy", "ix") := "(y, iy, ix)" in
         if: "y" < "x" then ("x", "ix", "ix"+#1) else ("y", "iy", "ix"+#1))
      ("y", #0, #1) "xs".

Definition list_max_index : val :=
  λ:"xs",
    match: "xs" with
    | NONE => #0
    | SOME "y_xs" =>
        let, ("y", "xs") := "y_xs" in
        let, ("_y", "iy", "_ix") :=
          list_max_index_aux "y" "xs"
        in "iy"
    end.

Definition list_init : val :=
  λ: "len" "f",
  (rec: "aux" "acc" "i" :=
    (if: "i" = #0
     then  "acc"
     else  "aux" (("f" "i") :: "acc") ("i" - #1))) [] "len".

Section list_specs.
  Context `{invGS_gen hlc Σ} `{g : !GenWp Σ}.
  Context `[!Inject A val].

  Definition List_max_index_aux y xs :=
    List.fold_left
      (λ '(y, iy, ix) x,
         if (Z.ltb y x)%Z then (x, ix, ix+1)%nat else (y, iy, ix+1)%nat)
      xs (y, 0, 1)%nat.

  Definition List_max_index (xs : list Z) : nat :=
  match xs with
  | [] => 0%nat
  | y :: xs =>
      let '(_, iy, _) :=
        List_max_index_aux y xs
      in iy
  end.

  Lemma gwp_list_max_index_aux E (y : Z) xs vxs :
    G{{{ ⌜is_list xs vxs⌝ }}}
      list_max_index_aux #y vxs @ g ; E
                 {{{ (y' : Z) (ix iy : nat), RET (#y', #iy, #ix); ⌜(y', iy, ix) = List_max_index_aux y xs⌝}}}.
  Proof.
    iIntros "%post %hxs hpost".
    rewrite /list_max_index_aux. gwp_pures.
    gwp_apply (gwp_list_fold
                 (λ l v, ∃ (y' : Z) (iy' ix : nat),
                     ⌜v = (#y', #iy', #ix)%V⌝ ∗
                     ⌜(y', iy', ix) = List_max_index_aux y l⌝ )
                 (λ _, emp) (λ _, emp))%I.
    2:{ repeat iSplit => //. iExists _,_,_. rewrite /List_max_index_aux /=.
        iSplit => //. done. }
    2:{ iIntros "%v ((%y' & %iy' & %ix' & %eq1 & %eq2) & _)".
        rewrite eq1. iApply "hpost". done. }
    iIntros. iIntros "%post' !> (%&(%&%&%&->&%IH)&_) hpost'".
    simplify_eq.
    gwp_pures.
    rewrite /List_max_index_aux.
    rewrite fold_left_app.
    rewrite /List_max_index_aux in IH. rewrite -IH.
    case_bool_decide ; gwp_pures ; iModIntro ;
      replace (Z.of_nat ix+1)%Z with (Z.of_nat $ ix+1) by lia.
    - iApply "hpost'". iSplit => //. iExists _,_,_. iPureIntro.
      intuition auto => /=.
      destruct (y' <? a)%Z eqn:h ; try apply Z.ltb_lt in h ; try lia.
      reflexivity.
    - iApply "hpost'". iSplit => //. iExists _,_,_. iPureIntro.
      intuition auto => /=.
      destruct (y' <? a)%Z eqn:h ; try apply Z.ltb_lt in h ; try lia.
      reflexivity.
  Qed.

  Lemma gwp_list_max_index E xs vxs :
    G{{{ ⌜is_list xs vxs⌝ }}}
      list_max_index vxs @ g ; E
                 {{{ (i : nat), RET #i; ⌜i = List_max_index xs⌝}}}.
  Proof.
    iIntros (Φ) "%Hxs HΦ". rewrite /list_max_index.
    gwp_pures.
    rewrite /List_max_index.
    destruct xs as [|y xs'].
    { rewrite Hxs. gwp_pures.
      replace 0%Z with (Z.of_nat 0) => //.
      iApply "HΦ". done. }
    destruct Hxs as (vxs' & -> & Hxs'). gwp_pures.
    gwp_bind (list_max_index_aux _ _).
    iApply gwp_list_max_index_aux => //.
    iIntros "!> % % % <-". gwp_pures. by iApply "HΦ".
  Qed.

  Lemma gwp_list_hd E xs vxs :
    G{{{ ⌜is_list xs vxs⌝ ∗ ⌜0 < length xs⌝ }}}
      list_hd vxs @ g ; E
                 {{{ v, RET v; ⌜List.hd v xs = v⌝}}}.
  Proof.
    iIntros (Φ) "(%Hxs & %Hlen) HΦ". rewrite /list_hd.
    gwp_pures.
    destruct xs as [|v xs]. 1: simpl in Hlen ; by (exfalso ; lia).
    simpl in Hxs.
    destruct Hxs as (? & -> & ?). gwp_pures.
    iApply "HΦ". done.
  Qed.

  Lemma gwp_list_tl E xs vxs :
    G{{{ ⌜is_list xs vxs⌝ ∗ ⌜0 < length xs⌝ }}}
      list_tl vxs @ g ; E
                 {{{ v, RET v; ⌜is_list (List.tl xs) v⌝}}}.
  Proof.
    iIntros (Φ) "(%Hxs & %Hlen) HΦ". rewrite /list_tl.
    gwp_pures.
    destruct xs as [|v xs]. 1: simpl in Hlen ; by (exfalso ; lia).
    simpl in Hxs.
    destruct Hxs as (? & -> & ?). gwp_pures.
    iApply "HΦ". done.
  Qed.

  (* Lemma gwp_list_init P Φ Ψ E handler (l : list A) acc lv :
       (∀ (a : A) acc lacc lrem,
           G{{{ ⌜l = lacc ++ a :: lrem⌝ ∗ P lacc acc ∗ Φ a }}}
             (Val handler) (Val acc) (inject a) @ g; E
           {{{v, RET v; P (lacc ++ [a]) v ∗ Ψ a }}}) -∗
       G{{{ ⌜is_list l lv⌝ ∗ P [] acc ∗ [∗ list] a∈l, Φ a }}}
         list_init handler acc lv @ g; E
       {{{v, RET v; P l v ∗ [∗ list] a∈l, Ψ a }}}.
     Proof.
       iIntros "#Hcl". iIntros (Ξ) "!# (Hl & Hacc & HΦ) HΞ".
       change l with ([] ++ l) at 1 4.
       generalize (@nil A) at 1 3 4 as lproc => lproc.
       iInduction l as [|x l] "IHl" forall (Ξ lproc acc lv) "Hacc Hl HΞ".
       - iDestruct "Hl" as %?; simpl in *; simplify_eq.
         gwp_rec. gwp_pures. iApply "HΞ".
         rewrite app_nil_r; iFrame; done.
       - iDestruct "Hl" as %[lw [? Hlw]]; subst.
         iDestruct "HΦ" as "[Hx HΦ]".
         gwp_rec. gwp_pures.
         gwp_apply ("Hcl" with "[$Hacc $Hx] [-]"); auto.
         iNext. iIntros (w) "[Hacc HΨ]"; simpl. gwp_pures.
         iApply ("IHl" with "[] [$HΦ] [$Hacc] [] [HΨ HΞ]"); [|auto|].
         { rewrite -app_assoc; auto. }
         iNext. iIntros (v) "[HP HΨs]".
         rewrite -app_assoc.
         iApply "HΞ"; iFrame.
     Qed. *)

End list_specs.



Section rnm.
  Context `{!diffprivGS Σ}.

  #[local] Open Scope R.

  Definition report_noisy_max (num den : Z) : val :=
    λ:"evalQ" "N" "d",
      let: "maxI" := ref #(-1) in
      let: "maxA" := ref #0 in
      let: "f" :=
        (rec: "rnm" "i" :=
           if: "i" = "N" then
             ! "maxI"
           else
             (let: "a" := Laplace #num #(2*den) ("evalQ" "i" "d") #() in
              (if: "i" = #0 `or` ! "maxA" < "a" then
                 "maxA" <- "a" ;;
                 "maxI" <- "i"
               else #()) ;;
              "rnm" ("i" + #1)))
      in "f" #0.


  Definition report_noisy_max_presampling (num den : Z) : val :=
    (* ↯ (num/den) ∗ evalQ is 1-sensitive ∗ N ∈ ℕ \ {0} ∗ 0 < num/2den ∗ dDB db db' <= 1 *)
    λ:"evalQ" "N" "d",
      let: "xs" := list_init "N" (λ:"i", "evalQ" "i" "d") in
      (* len xs = len xs' = N ∗ List_forall2 x ∈ xs, x' ∈ xs', dZ x x' <= 1 *)
      let: "xs_tapes" := list_map (λ:"x", ("x", AllocTapeLaplace #num #(2*den) "x")) "xs" in
      (* len tapes = len tapes' = N ∗
         List_forall2 (x, ι), (x', ι') ∈ tapes, tapes'
         . dZ x x' <= 1 ∗ ι ↦ (Lap(num, 2den, x), []) ∗ ι' ↦ (Lap(num, 2den, x'), [])
       *)
      (* state step to *)
      (* len tapes = len tapes' = N ∗
         ∃ vs vs' . len vs = len vs' = N ∗
         List_max_index vs = List_max_index vs' ∗
         List_forall4 (x, ι), (x', ι'), v, v' ∈ tapes, tapes', vs, vs'
         . ι ↦ (Lap(num, 2den, x), [v]) ∗ ι' ↦ (Lap(num, 2den, x'), [v'])
       *)
      let: "noisy_xs" := list_mapi (λ:"_k" "x_ι", Laplace #num #(2*den) (Fst "x_ι") (Snd "x_ι")) "xs_tapes" in
      (* We'll get exactly vs as noisy_xs. *)
      (* List.max_index noisy_xs = List.max_index noisy_xs' ; QED *)
      list_max_index "noisy_xs".

  Lemma rnm_init (evalQ : val) DB (dDB : Distance DB) (N : nat) K :
    (∀ i : Z, ⊢ hoare_sensitive (evalQ #i) 1 dDB dZ) →
    ∀ db db', dDB db db' <= 1 →
              {{{ ⤇ fill K ((of_val list_init) #N (λ:"i", (of_val evalQ) "i" (of_val (inject db'))))%V }}}
                (list_init #N (λ:"i", evalQ "i" (of_val (inject db))))%V
                {{{ vxs, RET vxs ; ∃ (vxs' : val) (xs xs' : list Z),
                        ⤇ fill K vxs' ∗
                        ⌜ is_list xs vxs ∧ is_list xs' vxs' ∧ length xs = N ∧ length xs' = N ∧
                        Forall2 (λ x x', dZ x x' <= 1) xs xs'⌝
                }}}.
  Proof with (tp_pures ; wp_pures).
    iIntros (ev_sens ?? adj post) "rhs Hpost".
    wp_lam. wp_pure. wp_lam.
    tp_lam. tp_pure. tp_lam.
    tp_pure. wp_pure.
    set (vxs := InjLV #()).
    unfold vxs at 1.
    set (vxs' := InjLV #()).
    set (k := N).
    wp_pure. tp_pure.
    assert
      (∃ (xs xs' : list Z),
                 is_list xs vxs
                  ∧ is_list xs' vxs'
                    ∧ (length xs + k = N)%nat
                      ∧ (length xs' + k = N)%nat
                        ∧ Forall2 (λ x x' : Z, dZ x x' <= 1) xs xs') as hpre.
    1: exists [], [] ; cbn ; intuition eauto.
    revert hpre.
    unfold k at 4 5.
    generalize k vxs vxs'.
    clear vxs vxs' k. intros.
    iInduction k as [|k'] forall (vxs vxs' hpre).
    - idtac... iApply "Hpost".
      destruct hpre as (?&?&?&?&?&?&?).
      iModIntro. iExists _,_,_. iFrame ; iPureIntro. intuition eauto ; cbn.
      + simplify_eq. lia.
      + simplify_eq. lia.

    - idtac...
      tp_bind (evalQ _ _) ; wp_bind (evalQ _ _).
      wp_apply (ev_sens with "[] [rhs]"). 1: iPureIntro ; lra. 1: iFrame.
      iIntros "% (%&%&->&rhs&%h)".
      idtac... wp_rec. wp_pure. wp_pure. wp_pure. wp_pure.
      simpl. tp_rec. tp_pure. tp_pure. tp_pure. tp_pure.
      replace (S k' - 1)%Z with (Z.of_nat k') by lia.
      destruct hpre as (xs & xs' &?&?&?&?&?).
      iSpecialize ("IHk'" $! (InjRV (#b, vxs)) ((InjRV (#b', vxs'))) with "[] [rhs]").
      2: iFrame.
      + iPureIntro. exists (b::xs). exists (b' :: xs'). intuition eauto.
        * simpl. eauto.
        * simpl. eauto.
        * simpl. lia.
        * simpl. lia.
        * constructor. 2: done.
          simpl in h. etrans. 2: exact adj. rewrite Rmult_1_l in h. done.
      + iSpecialize ("IHk'" with "Hpost").
        iApply "IHk'".
  Qed.

Local Program Instance : Inject loc val := {| inject := LitV ∘ LitLbl |}.
Next Obligation. by intros ?? [=]. Qed.

Lemma big_sepL2_Forall2 {PROP : bi} {A B} P (xs : list A) (ys : list B) :
  ((([∗ list] x; y ∈ xs; ys, ⌜P x y⌝ : PROP) ⊢ ⌜Forall2 P xs ys⌝ : PROP)%I).
Proof.
  iRevert (ys). iInduction xs as [|x xs'] ; iIntros (ys) "h".
  1: iDestruct (big_sepL2_length with "h") as "%len" ; destruct ys => //.
  destruct ys. 1: iDestruct (big_sepL2_length with "h") as "%len" => //.
  rewrite big_sepL2_cons.
  iDestruct "h" as "[hx h]".
  rewrite Forall2_cons_iff. iSplitL "hx" => //.
  iApply "IHxs'". done.
Qed.

Lemma lookup_eq_pointwise {A} `{Inhabited A} (xs ys : list A) :
  length xs = length ys -> (∀ k : nat, (k < length ys)%nat -> xs !!! k = ys !!! k) -> xs = ys.
Proof.
  revert ys. induction xs.
  1: intros ; destruct ys => //.
  intros ? hlen Hlookup . destruct ys. 1: simpl in * ; lia.
  opose proof (Hlookup 0%nat _) as Hl0 => /=; [lia|].
  f_equal. 1: apply Hl0.
  apply IHxs. 1: by inversion hlen.
  intros.
  specialize (Hlookup (S k)). simpl in Hlookup. apply Hlookup.
  lia.
Qed.

Lemma mapi_length {A B} (f : nat -> A -> B) (xs : list A) : length (mapi f xs) = length xs.
Proof. rewrite /mapi. generalize 0%nat. induction xs => //= ?. by rewrite IHxs. Qed.


(* γ := (dZ x x' <= 1) *)
Lemma rwp_list_map {A} `{!Inject A val} `{!Inject B val}
  (l l' : list A) (lv lv' fv fv' : val)
  (γ : A -> A -> iProp Σ) (ψ : B -> B -> iProp Σ)
  (P P' : list B -> iProp Σ) E K :
  {{{
        □ (∀ (x x' : A) K' (prev prev' : list B),
            {{{ γ x x' ∗ ⤇ fill K' (fv' (inject x')) ∗ P prev ∗ P' prev' }}}
              fv (inject x) @ E
              {{{ frv, RET frv;
                  ∃ frv' fr fr',
                    ⌜frv = (inject fr)⌝ ∗ ⌜frv' = (inject fr')⌝
                    ∗ ⤇ fill K' frv'
                    ∗ ψ fr fr' ∗ P (fr :: prev) ∗ P' (fr' :: prev')
          }}}) ∗
      ⌜is_list l lv⌝ ∗
      ⌜is_list l' lv'⌝ ∗
      ⌜length l = length l'⌝ ∗
      ([∗ list] i ↦ a;a' ∈ l;l', γ a a') ∗
      P [] ∗ P' [] ∗
      ⤇ fill K (list_map fv' lv')
  }}}
    list_map fv lv @ E
    {{{ rv, RET rv;
        ∃ rv' xs xs',
          ⌜is_list xs rv⌝ ∗
          ⌜is_list xs' rv'⌝ ∗
          ⌜length xs = length l⌝ ∗
          ⌜length xs' = length l'⌝ ∗
          ⤇ fill K rv' ∗
          ([∗ list] i ↦ a;a' ∈ xs;xs', ψ a a')
          ∗ P xs ∗ P' xs'
    }}}.
Proof.
  (* do whatever list_fold and list_mapi do... *)
  set (prev := []).
  unfold prev at 2.
  set (prev' := []).
  generalize prev, prev'. clear prev prev'.
  iRevert (l' lv').
  iInduction l as [|l_hd l_tl].
  - iIntros (?? prev prev' post) "* [h (%hlv&%hlv'&%hlen&pre&P&P'&rhs)] post". rewrite hlv.
    assert (l' = []) as ->. 1: by destruct l'.
    rewrite /list_map.
    rewrite hlv'. tp_pures.
    wp_pures. iApply "post". iModIntro. iExists _,[],[].
    repeat iSplit => // ; try iPureIntro => //.
    iFrame.
    rewrite hlv'. iFrame.

  (* - iIntros (?? post) "* [h (%hlv&%hlv'&%hlen&pre&P&P'&rhs)] post". rewrite hlv. *)

Admitted.

Lemma wp_alloc_tapes_laplace :
  (forall (num den : Z) K xs xs' vxs vxs',
      is_list xs vxs → is_list xs' vxs' → length xs = length xs' →
      Forall2 (λ x x' : Z, dZ x x' <= 1) xs xs' →
      {{{ ⤇ fill K ((list_map (λ: "x", ("x", AllocTapeLaplace #num #(2 * den) "x")))%V vxs') }}}
        (list_map (λ: "x", ("x", AllocTapeLaplace #num #(2 * den) "x")))%V vxs
        {{{ vxιs, RET vxιs ; ∃ vxιs' xιs xιs',
                ⌜is_list xιs vxιs⌝ ∗ ⌜length xιs = length xs⌝ ∗
                ⌜is_list xιs' vxιs'⌝ ∗ ⌜length xιs' = length xs'⌝ ∗
                ⌜ NoDup xιs.*2 ⌝ ∗ ⌜ NoDup xιs'.*2 ⌝ ∗
                ⤇ fill K vxιs' ∗
                [∗ list] '(x, ι) ; '(x', ι') ∈ xιs ; xιs',
              ι ↪L (num, 2*den, x; []) ∗ ι' ↪Lₛ (num, 2*den, x'; []) ∗
              ⌜dZ x x' <= 1⌝
  }}}).
Proof.
  iIntros (??????? hxs hxs' hlen adj post) "rhs post".
  iApply (rwp_list_map xs xs' vxs vxs'
            (λ: "x", ("x", AllocTapeLaplace #num #(2 * den) "x"))%V
            (λ: "x", ("x", AllocTapeLaplace #num #(2 * den) "x"))%V
            (λ x x', ⌜dZ x x' <= 1⌝)%I
            (λ '(x, ι) '(x', ι'), ⌜dZ x x' <= 1⌝ )%I
            (λ xιs, ([∗ list] xι ∈ xιs, let '(x, ι) := xι in ι ↪L (num, 2*den, x; [])) ∗ ⌜NoDup xιs.*2⌝)%I
            (λ xιs', ([∗ list] xι' ∈ xιs', let '(x', ι') := xι' in ι' ↪Lₛ (num, 2*den, x'; [])) ∗ ⌜NoDup xιs'.*2⌝)%I
           with "[-post]").
  2: iNext ; iIntros (?) "h". 2: iApply "post".
  2: {
    iDestruct "h" as "(%&%&%&%&%&%&%&rhs&h&[hh %]&[hh' %])".

    iExists _,_,_. iFrame.
    repeat iSplit => //.
    iAssert (
        ([∗ list] xι ; xι' ∈ xs0 ; xs'0,
           let '(x, ι) := xι in
           let '(x', ι') := xι' in
           (ι ↪L (num,2 * den,x; []) ∗ ι' ↪Lₛ (num,2 * den,x'; [])))
)%I
 with "[hh hh']" as "hh".
    {
      iApply big_sepL2_mono ; last first.
      - iApply (big_sepL2_sep_2 with "[hh]") ; iFrame.
        + iApply big_sepL2_const_sepL_l.
          iSplit => //. iPureIntro. lia.
        + iApply big_sepL2_const_sepL_r.
          iSplit => //. iPureIntro. lia.
      - iIntros. destruct y1, y2. done.
    }
    iDestruct (big_sepL2_sep_2 _ _ xs0 xs'0 with "[h] [hh]") as "hhh".
    1,2: done.


    rewrite !big_sepL2_alt. iSplit ; [iPureIntro ; lia|].
    iApply big_sepL_mono ; last first.
    - iDestruct "hhh" as "[% h]".
      done.
    - iIntros "* % h". simpl. destruct y. destruct p, p0. simpl.
      iDestruct "h" as "(%&h&h')". iFrame. done.
  }
  iFrame. repeat iSplit => //.
  2:{ iInduction adj as [|] forall (vxs vxs' hxs hxs' hlen) => //.
      iSplit => //. simpl.
      inversion hlen. destruct hxs, hxs'.
      iApply "IHadj" => // ; intuition eauto.
  }
  2,3: iPureIntro ; constructor.
  iModIntro. iIntros. iIntros "%post' !> (% & rhs & (hh & %) & (hh' & %)) post'".
  tp_pures. wp_pures.
  tp_alloctape_laplace ι' as "ι'".
  wp_alloctape_laplace ι as "ι".
  tp_pures. wp_pures. iApply "post'".
  iModIntro. iExists _,(x, ι),(x', ι'). simpl. iFrame "rhs".
  repeat iSplit => //=. iSplitL "ι hh".
  - simpl.
    iAssert (⌜ι ∈ list_fmap (Z * loc)%type loc snd prev⌝ -∗ False)%I as "%".
    {
      iIntros "%not_fresh".
      destruct (elem_of_list_fmap_2 snd prev ι not_fresh) as [? []].
      destruct x0. simpl in H2. symmetry in H2.
      simplify_eq.
      iDestruct (big_sepL_elem_of with "hh") as "ι'".
      1: done.
      iDestruct (ghost_map_elem_valid_2 ι diffprivGS_tapes_laplace_name (DfracOwn 1) (DfracOwn 1)
                   (Tape_Laplace num (Z.mul 2 den) x nil) (Tape_Laplace num (Z.mul 2 den) z nil)
                  with "[ι] [ι']")
        as "[% %]".
      3:{ cbv in H4. done. }
      1: iFrame.
      iFrame "ι'".
    }
    iFrame. iPureIntro.
    econstructor. 1,2: assumption.
  - simpl.
    iAssert (⌜ι' ∈ list_fmap (Z * loc)%type loc snd prev'⌝ -∗ False)%I as "%".
    {
      iIntros "%not_fresh'".
      destruct (elem_of_list_fmap_2 snd prev' ι' not_fresh') as [? []].
      destruct x0. simpl in H2. symmetry in H2.
      simplify_eq.
      iDestruct (big_sepL_elem_of with "hh'") as "ι''".
      1: done.
      iDestruct (ghost_map_elem_valid_2 ι' _ (DfracOwn 1) (DfracOwn 1)
                   (Tape_Laplace num (Z.mul 2 den) _ nil) (Tape_Laplace num (Z.mul 2 den) _ nil)
                  with "ι' ι''")
        as "[% %]".
      cbv in H4. done.
    }
    iFrame. iPureIntro.
    econstructor. 1,2: assumption.
Qed.


  Lemma rnm_pres_diffpriv num den (evalQ : val) DB (dDB : Distance DB) (N : nat) K :
    (0 < IZR num / IZR (2 * den)) →
    (∀ i : Z, ⊢ hoare_sensitive (evalQ #i) 1 dDB dZ) →
    ∀ db db', dDB db db' <= 1 →
                {{{ ↯m (IZR num / IZR den) ∗
                    ⤇ fill K (report_noisy_max_presampling num den evalQ #N (of_val (inject db'))) }}}
                  report_noisy_max_presampling num den evalQ #N (of_val (inject db))
                  {{{ v, RET v ; ∃ (v' : val), ⤇ fill K v' ∗ ⌜ v = v' ⌝  }}}.
  Proof with (tp_pures ; wp_pures).
    intros εpos qi_sens db db' db_adj post. iIntros "[ε rhs] Hpost".
    wp_lam. tp_lam...
    tp_bind (list_init _ _). wp_bind (list_init _ _).
    iApply (rnm_init with "rhs") => //.
    iIntros "!> % (% & % & % & rhs & % & % & % & % & %)". simpl...
    tp_bind (list_map _ _). wp_bind (list_map _ _).

    (* assert (forall K vxs vxs',
                  {{{ ⤇ fill K ((list_map (λ: "x", ("x", AllocTapeLaplace #num #(2 * den) "x")))%V vxs') }}}
                    (list_map (λ: "x", ("x", AllocTapeLaplace #num #(2 * den) "x")))%V vxs
                    {{{ vxιs, RET vxιs ; ∃ vxιs' xιs xιs',
                            ⌜is_list xιs vxιs⌝ ∗ ⌜length xιs = length xs⌝ ∗
                            ⌜is_list xιs' vxιs'⌝ ∗ ⌜length xιs' = length xs'⌝ ∗
                            ⌜ NoDup xιs.*2 ⌝ ∗ ⌜ NoDup xιs'.*2 ⌝ ∗
                            ⤇ fill K vxιs' ∗
                            [∗ list] '(x, ι) ; '(x', ι') ∈ xιs ; xιs',
                          ι ↪L (num, 2*den, x; []) ∗ ι' ↪Lₛ (num, 2*den, x'; []) ∗
                          ⌜dZ x x' <= 1⌝
              }}}) as wp_tape_list.
       1: admit. *)

    wp_apply (wp_alloc_tapes_laplace with "rhs") (* ; clear wp_tape_list *) => //.
    1: lia.
    iIntros "% (% & % & % & % & % & % & % & % & % & rhs & Htapes) /="...
    iAssert
      (∀ num den e Φ,
          (⌜(0 < IZR num / IZR (2 * den))⌝ ∗
           ↯m (IZR num / IZR den) ∗
           ([∗ list] '(x, ι);'(x', ι') ∈ xιs;xιs', ι ↪L (num, 2 * den,x; []) ∗ ι' ↪Lₛ (num,2 * den,x'; []) ∗ ⌜dZ x x' <= 1⌝) ∗
             ⌜ NoDup xιs.*2 ⌝ ∗ ⌜ NoDup xιs'.*2 ⌝
           ∗
             ((∃ zs zs', ([∗ list] k ↦ '(x, ι);'(x', ι') ∈ xιs;xιs',
                            ι ↪L (num, 2 * den,x; [zs !!! k]) ∗
                            ι' ↪Lₛ (num,2 * den,x'; [zs' !!! k]) ∗
                            ⌜dZ x x' <= 1⌝) ∗
                         ⌜length zs = N⌝ ∗
                         ⌜length zs' = N⌝ ∗
                         ⌜List_max_index zs = List_max_index zs'⌝)
              -∗
              WP e {{ v, Φ v }})
             -∗
           WP e {{ v, Φ v }}))%I
      as "presample_laplace_map_max".
    1: admit.

    wp_apply ("presample_laplace_map_max" $! _ _ _ post with "[$ε $Htapes rhs Hpost]") ;
      iClear "presample_laplace_map_max" ; iSplit ; [done|].
    repeat iSplit => //.
    iIntros "(% & % & Htapes & %Hmax)".

    (* TODO split the tapes assumption into three list-foralls (two unary ones and one that's pure about the dZ). *)
    iAssert (([∗ list] k↦'(x, ι);'(x', ι') ∈ xιs;xιs',
               ι ↪L (num, 2 * den,x; [zs !!! k]))
             ∗
               ([∗ list] k↦'(x, ι);'(x', ι') ∈ xιs;xιs',
                  ι' ↪Lₛ (num, 2 * den,x'; [zs' !!! k]) ∗ ⌜dZ x x' <= 1⌝)
            )%I with "[Htapes]" as "[Htapes Htapes']".
    {
      opose proof big_sepL2_sep as h.
      symmetry in h.
      iApply (h with "[Htapes]").
      iApply (big_sepL2_mono with "Htapes").
      iIntros (?[][]) "%% [?[??]]". iFrame.
    }
    iAssert (([∗ list] k↦'(x, ι);'(x', ι') ∈ xιs;xιs',
                  ι' ↪Lₛ (num, 2 * den,x'; [zs' !!! k]))
             ∗
               ([∗ list] k↦'(x, ι);'(x', ι') ∈ xιs;xιs', ⌜dZ x x' <= 1⌝)
            )%I with "[Htapes']" as "[Htapes' htapes]".
    {
      opose proof big_sepL2_sep as h.
      symmetry in h.
      iApply (h with "[Htapes']").
      iApply (big_sepL2_mono with "Htapes'").
      iIntros (?[][]) "%% [??]". iFrame.
    }
    iAssert ((
                ∃ xs xs' ιs ιs',
                  ([∗ list] k↦'xι ∈ xιs,
                     let '(x, ι) := xι in
                     ⌜xs !!! k = x⌝ ∗ ⌜ιs !!! k = ι⌝ ∗
                     ι ↪L (num, 2 * den,x; [zs !!! k]))
                ∗
                  ([∗ list] k↦xι' ∈ xιs',
                     let '(x', ι') := xι' in
                     ⌜xs' !!! k = x'⌝ ∗ ⌜ιs' !!! k = ι'⌝ ∗
                     ι' ↪Lₛ (num, 2 * den,x'; [zs' !!! k]))
                ∗ ⌜Forall2 (λ x x', dZ x x' <= 1) xs xs'⌝
             )%I
              ) with "[Htapes Htapes' htapes]" as
      "(%&%&%&%& Htapes & Htapes' & %htapes)".
    {
      assert (forall (xys : list (Z * loc)) k x y, xys !! k = Some (x,y) → (xys .*1) !! k = Some x) as lookup_fmap_fst.
      {
        clear. intro xys. induction xys. 1: done.
        intros. destruct k.
        - simpl. simpl in H. inversion H. subst. simpl. done.
        - destruct a.
          rewrite fmap_cons.
          simpl. simpl in H. eapply IHxys. done.
      }
      assert (forall (xys : list (Z * loc)) k x y, xys !! k = Some (x,y) → (xys .*2) !! k = Some y) as lookup_fmap_snd.
      {
        clear. intro xys. induction xys. 1: done.
        intros. destruct k.
        - simpl. simpl in H. inversion H. subst. simpl. done.
        - destruct a.
          rewrite fmap_cons.
          simpl. simpl in H. eapply IHxys. done.
      }
      iExists (xιs.*1). iExists (xιs'.*1).
      iExists (xιs.*2). iExists (xιs'.*2).
      iSplitL "Htapes" ; [|iSplitL "Htapes'"].
      - opose proof (big_sepL2_const_sepL_l (λ k '(x, ι), ι ↪L (num, 2 * den,x; [zs !!! k]))%I xιs xιs') as h.
        symmetry in h.
        iDestruct (h with "[Htapes]") as "[% Htapes]" ; clear h.
        { iApply (big_sepL2_mono with "Htapes").
          iIntros (? [] []). iIntros. done. }
        iApply (big_sepL_mono with "Htapes").
        iIntros (? []). iIntros. iFrame.
        iPureIntro. split.
        + apply list_lookup_total_correct. eapply lookup_fmap_fst. done.
        + apply list_lookup_total_correct. eapply lookup_fmap_snd. done.
      - opose proof (big_sepL2_const_sepL_r (λ k '(x, ι), ι ↪Lₛ (num, 2 * den,x; [zs' !!! k]))%I xιs xιs') as h.
        symmetry in h.
        iDestruct (h with "[Htapes']") as "[% Htapes']" ; clear h.
        { iApply (big_sepL2_mono with "Htapes'").
          iIntros (? [] []). iIntros. done. }
        iApply (big_sepL_mono with "Htapes'").
        iIntros (? []). iIntros. iFrame.
        iPureIntro. split.
        + apply list_lookup_total_correct. eapply lookup_fmap_fst. done.
        + apply list_lookup_total_correct. eapply lookup_fmap_snd. done.
      -
        iApply big_sepL2_Forall2.
        iApply big_sepL2_fmap_l.
        iApply big_sepL2_fmap_r.
        iApply (big_sepL2_mono with "htapes").
        { iIntros (? [] []). iIntros. simpl. done. }
    }

    wp_bind (list_mapi _ _).

    iApply (gwp_list_mapi (A:=Z*loc) (B:=Z)
              (Inject0 := (@Inject_prod Z inject.Inject_instance_0 loc Inject_instance_0))
              (λ k '(x, ι), zs !!! k)
              xιs
              _
              _
              (λ k xι, let '(x, ι) := xι in ι ↪L (num, 2*den, x; [zs !!! k]))%I
              (λ k z', ⌜zs !!! k = z'⌝)%I
             with "[Htapes]").
    { repeat iSplit.
      - iModIntro.
        iIntros (k [x ι] Φ) "!> ι HΦ". simpl.
        wp_pures.
        wp_apply (wp_laplace_tape with "[$ι]") ; iIntros "ι".
        iApply "HΦ". done.
      - done.
      - iApply (big_sepL_mono with "Htapes").
        iIntros (?[]) "% [?[??]]". iFrame.
    }
    iIntros "!> % h_list_mapi". idtac...

    tp_bind (list_mapi _ _).

    iMod (gwp_list_mapi (g:=gwp_spec)
                  (λ k '(x, ι), zs' !!! k) xιs'
                  (λ: "_k" "x_ι", Laplace #num #(2 * den) (Fst "x_ι") (Snd "x_ι"))%V
                  vxιs'
                  (λ k '(x, ι), ι ↪Lₛ (num, 2*den, x; [zs' !!! k]))%I
                  (λ k z', ⌜zs' !!! k = z'⌝)%I
               with "[Htapes'] [] [$rhs]") as (?) "[rhs h_list_mapi']".
    {
      repeat iSplit.
      - iModIntro.
        iIntros (k [x ι] Φ) "!> ι HΦ %K' rhs". simpl.
        tp_pures.
        tp_laplace.
        iModIntro. iFrame. iApply "HΦ". done.
      - done.
      - iApply (big_sepL_mono with "Htapes'").
        iIntros (?[]) "% [?[??]]". iFrame.
    }
    1: { iIntros "% hh". iExact "hh". }
    iSimpl in "rhs". tp_pures.
    iDestruct "h_list_mapi" as "(%mapi1&%mapi2)".
    iDestruct "h_list_mapi'" as "(%mapi1'&%mapi2')".

    iMod (gwp_list_max_index (g:=gwp_spec) _ _ _
            (fun (i : val) => ⌜i = LitV (LitInt (List_max_index (mapi (λ (k : nat) '(_, _), zs' !!! k) xιs')))⌝)%I
          with "[] [] rhs")
      as (?) "[rhs %max_rhs]".
    1: done.
    { iIntros (?) "%hh". rewrite hh. done. }
    iApply gwp_list_max_index.
    1: done.
    iIntros "!> **".
    iApply "Hpost".
    iFrame.
    simplify_eq.
    iPureIntro. f_equal. f_equal. f_equal.
    destruct Hmax as (?&?&?).
    assert (zs' = (mapi (λ (k : nat) '(_, _), zs' !!! k) xιs')) as <- ; first last.
    1: assert (zs = (mapi (λ (k : nat) '(_, _), zs !!! k) xιs)) as <- ; first last.
    1: assumption.
    - eapply lookup_eq_pointwise.
      { rewrite mapi_length. lia. }
      intros. apply mapi2.
      apply list_lookup_lookup_total_lt.
      done.
    - eapply lookup_eq_pointwise.
      { rewrite mapi_length. lia. }
      intros. apply mapi2'.
      apply list_lookup_lookup_total_lt.
      done.
  Admitted.



  #[local] Definition rnm_body (num den : Z) (evalQ : val) {DB} (dDB : Distance DB) (N : nat) (db : DB) (maxI maxA : loc) :=
    (rec: "rnm" "i" :=
       if: "i" = #N then ! #maxI
       else let: "a" := Laplace #num #(2*den) (evalQ "i" (inject db)) #() in
            (if:  "i" = #0 `or` ! #maxA < "a"
             then #maxA <- "a";; #maxI <- "i" else #());;
            "rnm" ("i" + #1))%V.

  Lemma rnm_pw_diffpriv num den (evalQ : val) DB (dDB : Distance DB) (N : nat) K :
    (0 < IZR num / IZR (2 * den)) →
    (∀ i : Z, ⊢ hoare_sensitive (evalQ #i) 1 dDB dZ) →
    ∀ db db', dDB db db' <= 1 →
              ∀ j : val,
                {{{ ↯m (IZR num / IZR den) ∗
                    ⤇ fill K (report_noisy_max num den evalQ #N (inject db')) }}}
                  report_noisy_max num den evalQ #N (inject db)
                  {{{ v, RET v ; ∃ (v' : val), ⤇ fill K v' ∗ ⌜ v = j → v' = j ⌝  }}}.
  Proof with (tp_pures ; wp_pures).
    intros εpos qi_sens. iIntros (db db' db_adj j Φ) "(ε & rnm) HΦ".
    rewrite /report_noisy_max /=...
    (* initialize *)
    tp_alloc as maxI2 "maxI2". tp_pures. tp_alloc as maxA2 "maxA2". do 5 tp_pure.
    wp_pures. wp_alloc maxI1 as "maxI1". wp_alloc maxA1 as "maxA1". do 5 wp_pure.
    destruct (decide ((∃ zj : Z, j = #zj))) as [[zj ->]|]. 2: shelve.
    rename zj into j. rewrite -!/(rnm_body _ _ _ _ _ _ _ _).
    (* generalize loop variable, set up invariants *)
    cut
      (∀ (i imax1 imax2 : Z) (amax1 amax2 : Z),
          {{{ maxI1 ↦ #imax1 ∗ maxI2 ↦ₛ #imax2 ∗ maxA1 ↦ #amax1 ∗ maxA2 ↦ₛ #amax2
              ∗ ↯m (if (bool_decide (i <= j))%Z then (IZR num / IZR den) else 0)
              ∗ ⤇ fill K (rnm_body num den evalQ dDB N db' maxI2 maxA2 #i)
              ∗ ⌜ 0 <= i <= N ⌝%Z
              ∗ ⌜ (i = 0) → (imax1 = -1 ∧ imax2 = -1)⌝%Z
              ∗ ⌜ i < j ∧ ¬ (i = 0) → ((dZ amax1 amax2 <= 1)%R ∧ imax1 < i ∧ imax2 < i) ⌝%Z
              ∗ ⌜ i = j ∧ ¬ (i = 0)%Z
                  → ( (dZ amax1 amax2 <= 1)%R ∧ (imax1 = j → (imax2 = j ∧ amax1 + 1 = amax2)))%Z ⌝
              ∗ ⌜ (j < i)%Z ∧ ¬ (i = 0)%Z → ( imax1 = j → (imax2 = j ∧ amax1 + 1 = amax2) )%Z ⌝ }}}
            rnm_body num den evalQ dDB N db maxI1 maxA1 #i
            {{{ (v : Z), RET #v ; ∃ (v' : Z), ⤇ fill K #v' ∗ ⌜ v = j -> v' = j ⌝ }}}
      ).
    (* the general statement implies the original goal *)
    1: { intros h. iMod ecm_zero as "ε0". iApply (h with "[-HΦ]").
         - (* We have all the reference resources for the IH. *)
           iFrame. iSplitL. 1: case_bool_decide ; iFrame.
           (* The arithmetic works out fine. *)
           iPureIntro. split ; [|split ; [|split ; [|split]]] ; clear ; intros. 1: lia.
           + auto.
           + rewrite distance_0 //. lia.
           + lia.
           + exfalso. lia.
         - (* The post-condition of the IH implies the original post. *)
           iNext ; iIntros (v) "(%v' & v' & %h')". iApply "HΦ". iExists _. iFrame.
           iPureIntro. intro h''. do 3 f_equal. apply h'. inversion h''. done.
    }
    clear Φ.

    iLöb as "IH". (* the actual induction begins *)
    iIntros (i imax1 imax2 amax1 amax2 Φ)
      "(maxI1 & maxI2 & maxA1 & maxA2 & ε & rnm' & %iN & %i0 & %below_j & %at_j & %above_j) HΦ".
    rewrite {3 4}/rnm_body... case_bool_decide (#i = #N) as iN'...

    (* base case: exiting the loop at i = N *)
    - tp_load ; wp_load. iApply "HΦ". iExists imax2. iFrame "rnm'". iPureIntro.
      intros ij1. inversion iN'. subst. clear -i0 below_j at_j above_j. lia.

    (* rnm body *)
    - assert (i ≠ N). { intro h. apply iN'. subst. done. }
      assert (i < N)%Z by lia.
      rewrite -!/(rnm_body _ _ _ _ _ _ _ _).
      (* sensitivity of evalQ *)
      tp_bind (evalQ _ _). wp_bind (evalQ _ _).
      iApply (hoare_sensitive_Z_bounded $! (qi_sens i) with "[] [] rnm'") => //.
      1: real_solver. rewrite Zmult_1_l.
      iIntros "!> % (%e1 & %e2 & -> & rnm' & %e1e2_adj & %e1e2_adj')" => /=.
      iMod ecm_zero as "ε0".
      (* case on the whether i is below, at, or above the result j. *)
      destruct (Z.lt_trichotomy i j) as [ij | [e|ij]].
      2:{                       (* i = j *)
        tp_bind (Laplace _ _ _ _). wp_bind (Laplace _ _ _ _).
        iApply (hoare_couple_laplace e1 e2 1%Z 2%Z with "[$rnm' ε]") => //.
        1: apply Zabs_ind ; lia.
        { case_bool_decide. 2: lia. iApply ecm_eq. 2: iFrame.
          rewrite mult_IZR. field. clear -εpos.
          intro d0. rewrite mult_IZR in εpos. rewrite Rdiv_mult_distr in εpos.
          rewrite d0 in εpos. rewrite Rdiv_0_r in εpos. lra. }
        iNext ; iIntros (a) "rnm'" => /=... tp_load ; wp_load...
        case_bool_decide (#i = #0) as case_i0 ; [inversion case_i0 as [ei0]|] => /=...
        { tp_store ; tp_pures ; tp_store ; do 2 wp_store...
          iApply ("IH" with "[-HΦ]") ; iFrame.
          case_bool_decide ; try lia. iFrame. iPureIntro. intuition lia. }
        assert (¬ i = 0)%Z as nei0 ; [intros ? ; apply case_i0 ; by subst |].
        specialize (at_j (conj e nei0)). destruct at_j as (amax_adj & jmax1).
        case_bool_decide (amax1 < a)%Z as case_l ; try rewrite orb_true_r ; tp_pures ; wp_pures.
        all: case_bool_decide (amax2 < a+1)%Z as case_r ; try rewrite orb_true_r ; tp_pures ; wp_pures.
        * do 2 (tp_store ; tp_pures ; wp_store ; wp_pures).
          iApply ("IH" with "[-HΦ]") ; iFrame. case_bool_decide ; try lia ; iFrame.
          iPureIntro. intuition lia.
        * exfalso. clear -case_l case_r amax_adj. assert (a+1 <= amax2)%Z by lia.
          revert amax_adj. rewrite /dZ/distance Rabs_Zabs. apply Zabs_ind ; intros.
          -- lia.
          -- pose proof (le_IZR _ _ amax_adj). lia.
        * tp_store ; tp_pures ; tp_store ; tp_pures.
          iSpecialize ("IH" $! (i+1)%Z imax1 i amax1 (a+1)%Z).
          iSpecialize ("IH" with "[ε0 $rnm' $maxA1 $maxA2 $maxI1 $maxI2]").
          2: iApply ("IH" with "[HΦ]") ; iFrame.
          iSplitL. 1: case_bool_decide ; try lia ; iFrame "ε0".
          iPureIntro ; intuition lia.
        * iApply ("IH" with "[-HΦ]") ; iFrame. case_bool_decide ; try lia.
          iFrame. iFrame. iPureIntro. intuition lia. }

      (* i < j *)
      { tp_bind (Laplace _ _ _ _) ; wp_bind (Laplace _ _ _ _).
        iApply (hoare_couple_laplace e1 e2 (e2 - e1)%Z 0%Z with "[$rnm' ε0]") => //.
        1: eapply Zabs_ind ; intuition lia. 1: rewrite Rmult_0_l => //.
        iNext ; iIntros (a) "rnm'" => /=... tp_load ; wp_load...

        case_bool_decide (#i = #0) as case_i0 ; [inversion case_i0 as [ei0]|] => /=...
        { do 2 (tp_store ; tp_pures ; wp_store ; wp_pures).
          iApply ("IH" with "[-HΦ]") ; iFrame.
          iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
          iPureIntro. intuition try lia.
          all: rewrite Rabs_Zabs ; apply Zabs_ind ; intros ; apply IZR_le ; intuition try lia.
        }
        assert (¬ i = 0)%Z as nei0 ; [intros ? ; apply case_i0 ; by subst |].
        destruct (below_j (conj ij nei0)) as (amax_adj & imax1i & imax2i).
        destruct (dZ_bounded_cases _ _ _ amax_adj).
        case_bool_decide (amax1 < a)%Z as case_l.
        all: case_bool_decide (amax2 < a + (e2 - e1))%Z as case_r...
        all: try do 2 (tp_store ; tp_pures) ; try do 2 wp_store...
        - iApply ("IH" with "[-HΦ]") ; iFrame.
          iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
          iPureIntro ; intuition try lia.
          all: rewrite Rabs_Zabs ; apply IZR_le, Zabs_ind ; lia.
        - iApply ("IH" $! (i+1)%Z with "[-HΦ]") ; iFrame.
          iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
          assert (a+(e2-e1) <= amax2)%Z by lia.
          iPureIntro ; intuition try lia.
          all: rewrite Rabs_Zabs ; apply IZR_le, Zabs_ind ; lia.
        - iApply ("IH" $! (i+1)%Z with "[-HΦ]") ; iFrame.
          iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
          assert (a <= amax1)%Z by lia.
          iPureIntro ; intuition try lia.
          all: rewrite Rabs_Zabs ; apply IZR_le, Zabs_ind ; lia.
        - iApply ("IH" $! (i+1)%Z with "[-HΦ]") ; iFrame.
          iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
          iPureIntro ; intuition try lia. }

      (* j < i *)
      { tp_bind (Laplace _ _ _ _) ; wp_bind (Laplace _ _ _ _).
        iApply (hoare_couple_laplace e1 e2 (e2 - e1)%Z 0%Z with "[$rnm' ε0]") => //.
        1: eapply Zabs_ind ; intuition lia. 1: rewrite Rmult_0_l => //.
        iNext ; iIntros (a) "rnm'" => /=... tp_load ; wp_load...

        case_bool_decide (#i = #0) as case_i0 ; [inversion case_i0 as [ei0]|] => /=...
        { do 2 (tp_store ; tp_pures ; wp_store ; wp_pures).
          iApply ("IH" with "[-HΦ]") ; iFrame.
          iSplitL. 1: repeat case_bool_decide ; try lia ; iFrame.
          iPureIntro ; lia. }

        assert (¬ i = 0)%Z as nei0 ; [intros ? ; apply case_i0 ; by subst |].
        specialize (above_j (conj ij nei0)).
        case_bool_decide (amax1 < a)%Z as case_l.
        all: case_bool_decide (amax2 < a + (e2 - e1))%Z as case_r...
        all: try do 2 (tp_store ; tp_pures) ; try do 2 wp_store...
        - iApply ("IH" with "[-HΦ]") ; iFrame.
          iSplitL. 1: repeat case_bool_decide ; iFrame ; lia. iPureIntro ; lia.
        - iApply ("IH" $! (i+1)%Z with "[-HΦ]") ; iFrame.
          iSplitL. 1: repeat case_bool_decide ; iFrame ; lia. iPureIntro ; lia.
        - iApply ("IH" $! (i+1)%Z with "[-HΦ]") ; iFrame.
          iSplitL. 1: repeat case_bool_decide ; iFrame ; lia. iPureIntro ; lia.
        - iApply ("IH" $! (i+1)%Z with "[-HΦ]") ; iFrame.
          iSplitL. 1: repeat case_bool_decide ; iFrame ; lia. iPureIntro ; lia.
      }

      (* this is the case where the predicted result j is not actually an integer *)
      Unshelve. destruct N... { tp_load ; wp_load. iApply "HΦ". iFrame. done. }
      tp_bind (evalQ _ _) ; wp_bind (evalQ _ _).
      iApply (hoare_sensitive_Z_bounded $! (qi_sens _) with "[] [] rnm") => //.
      1: real_solver. rewrite Zmult_1_l.
      iIntros "!> % (%e1 & %e2 & -> & rnm & %e1e2_adj & %e1e2_adj')" => /=.
      tp_bind (Laplace _ _ _ _) ; wp_bind (Laplace _ _ _ _). iMod ecm_zero as "ε0".
      iApply (hoare_couple_laplace e1 e2 (e2 - e1)%Z 0%Z with "[$rnm ε0]") => //.
      1: eapply Zabs_ind ; intuition lia.
      1: rewrite Rmult_0_l => //.
      iNext ; iIntros (a) "rnm'" => /=...

      tp_load ; wp_load... tp_store ; wp_store...
      tp_store ; tp_pure ; tp_pure ; tp_pure. wp_store. wp_pure.
      rewrite -!/(rnm_body _ _ _ _ _ _ _ _).

      cut (∀ (i : Z) (imax1 imax2 : nat) (amax1 amax2 : Z),
              {{{ maxI1 ↦ #imax1 ∗ maxI2 ↦ₛ #imax2 ∗ maxA1 ↦ #amax1 ∗ maxA2 ↦ₛ #amax2
                  ∗ ⤇ fill K (rnm_body num den evalQ dDB (S N) db' maxI2 maxA2 #i)
                  ∗ ⌜ 0 <= i <= (S N) ⌝%Z }}}
                rnm_body num den evalQ dDB (S N) db maxI1 maxA1 #i
                {{{ (v : nat), RET #v; ∃ (v' : nat), ⤇ fill K #v' ∗ ⌜ #v = j -> #v' = j ⌝ }}}).
      { intros h. iMod ecm_zero as "ε0". iApply (h with "[-HΦ]").
        - replace 0%Z with (Z.of_nat 0) by lia. iFrame. iPureIntro ; lia.
        - iNext ; iIntros (v) "(%v' & v' & %h')". iApply "HΦ". iFrame.
          iPureIntro. intro h''. do 3 f_equal. apply h'. inversion h''. done.
      }
      clear Φ.

      iLöb as "IH".
      iIntros (i imax1 imax2 amax1 amax2 Φ) "(maxI1 & maxI2 & maxA1 & maxA2 & rnm' & %iN) HΦ".
      rewrite {3 4}/rnm_body... case_bool_decide (#i = #(S N)) as iN'...
      + tp_load ; wp_load. iApply "HΦ". iExists imax2. iFrame "rnm'". iPureIntro.
        intros ij1. rewrite -ij1 in n. exfalso. apply n. eexists _. reflexivity.
      + assert (i ≠ S N) as iN''. { intro h. apply iN'. subst. done. }
        assert (i < S N)%Z by lia.
        rewrite -!/(rnm_body _ _ _ _ _ _ _ _).
        clear e1 e2 e1e2_adj e1e2_adj'.
        tp_bind (evalQ _ _) ; wp_bind (evalQ _ _).
        iApply (hoare_sensitive_Z_bounded $! (qi_sens _) with "[] [] rnm'") => //.
        1: real_solver. rewrite Zmult_1_l.
        iIntros "!> % (%e1 & %e2 & -> & rnm' & %e1e2_adj & %e1e2_adj')" => /=.
        tp_bind (Laplace _ _ _ _) ; wp_bind (Laplace _ _ _ _).
        iMod ecm_zero as "ε0".
        iApply (hoare_couple_laplace e1 e2 (e2 - e1)%Z 0%Z with "[$rnm' ε0]") => //.
        1: eapply Zabs_ind ; intuition lia.
        1: rewrite Rmult_0_l => //.
        iNext ; iIntros (a') "rnm'" => /=... tp_load ; wp_load...
        destruct (bool_decide (#i = #0) || bool_decide (amax1 < a')%Z)...
        all: destruct (bool_decide (#i = #0) || bool_decide (amax2 < a' + (e2 - e1))%Z)...
        all: repeat (tp_store ; tp_pures) ; repeat wp_store...
        all: replace i with (Z.of_nat (Z.to_nat i)) ; [|lia] ; iFrame...
        all: iApply ("IH" with "[-HΦ]") => // ; iFrame.
        all: iPureIntro ; lia.
  Qed.

End rnm.

Lemma rnm_diffpriv_cpl num den (evalQ : val) DB (dDB : Distance DB) (N : nat) :
  (0 < IZR num / IZR (2 * den))%R →
  (0 <= IZR num / IZR den)%R →
  (∀ `{!diffprivGS Σ}, ∀ i : Z, ⊢ hoare_sensitive (evalQ #i) 1 dDB dZ) →
  ∀ db db', (dDB db db' <= 1)%R → ∀ σ,
      DPcoupl
        (lim_exec ((report_noisy_max num den evalQ #N (inject db)), σ))
        (lim_exec ((report_noisy_max num den evalQ #N (inject db')), σ))
        (λ v v', v = v')
        (IZR num / IZR den) 0.
Proof.
  intros. replace 0%R with (SeriesC (λ _ : val, 0)). 2: by by apply SeriesC_0.
  apply DPcoupl_pweq => //=. 1: apply ex_seriesC_0. intros x'.
  eapply (adequacy.wp_adequacy diffprivΣ) => //.
  iIntros (?) "rnm' ε _".
  unshelve iPoseProof (rnm_pw_diffpriv num den evalQ DB dDB N [] H (H1 _ _) db db' H2 x'
    (λ v, ∃ v' : val, ⤇ v' ∗ ⌜v = x' → v' = x'⌝)%I) as "h" => //=.
  iSpecialize ("h" with "[$]"). iApply "h".
  iNext. iIntros (?) "[% [? %h]]". iExists v' ; iFrame. iPureIntro. exact h.
Qed.

Lemma rnm_diffpriv num den (evalQ : val) DB (dDB : Distance DB) (N : nat) :
  (0 < IZR num / IZR (2 * den))%R →
  (0 <= IZR num / IZR den)%R →
  (∀ `{!diffprivGS Σ}, ∀ i : Z, ⊢ hoare_sensitive (evalQ #i) 1 dDB dZ) → ∀ σ,
      diffpriv_pure
        dDB
        (λ db, lim_exec ((report_noisy_max num den evalQ #N (inject db)), σ))
        (IZR num / IZR den).
Proof.
  intros. apply diffpriv_approx_pure. apply DPcoupl_diffpriv.
  intros. apply rnm_diffpriv_cpl => //.
Qed.
