From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import adequacy diffpriv proofmode.
From clutch.prob_lang.gwp Require Import gen_weakestpre arith list.
From clutch.diffpriv.examples Require Import list numeric_sparse_vector_technique.

Section pmw.
  Context `{!diffprivGS Σ}.

  #[local] Open Scope R.


  (* For the proof we need to adapt the algo from the book. *)
  (* Indeed, in order to get result on the call to `f`, *)
  (* the numeric sparse vector technique, we need to call *)
  (* it again for e2 only when we know that e1 is None. *)
  (* Otherwise, we can not state no result on e2 since if *)
  (* e1 returned a value then we would not have the right inSVT hypothesis. *)
  (* Knowing that even if e1 and e2 are values, then we will *)
  (* not use e2. Hence we call it only when necessary. *)

  (* We are giving to the oPMW technique a lot of functions in *)
  (* parameters. We also make a lot of assumptions about those *)
  (* functions in the specification. *)
  (* That is why this is only a partial implementation of the *)
  (* private multiplicative weight technique. *)
  (* Moreover I'm not convinced about the specification. *)
  (* Our functions should "here" take any val in args *)
  (* and return a val... this seems like a very strong hypothese ? *)

  (** Query implementation *)
  (* We assume that there exists an indexation on the elements of the domain χ. *)
  (* Hence to represent a database, we will use an array. *)

  Definition c_query : val :=
    λ: "db" "q",
      let: "res" := ref #0 in
      list_iteri (λ: "i" "x", if: (list_nth "q" "i") then ("res" <- "x" + !"res") else #()) "db";;
      !"res".

  Lemma c_query_det :
    ∀ K (vq vdb: val) (q : list bool) (db : list nat) (size_dom : nat),
      ⌜ is_list q vq ⌝ -∗ ⌜ is_list db vdb ⌝ -∗ ⌜ length q = size_dom ⌝ -∗ ⌜ length db = size_dom ⌝ -∗
      ⤇ fill K (c_query vdb vq) -∗
      WP c_query vdb vq {{ v, ⤇ fill K (Val v) ∗ ∃ (n : nat), ⌜ v = #n ⌝ }}.
   Proof with (wp_pures; tp_pures).
     iIntros (K vq vdb q db) "%H1  %H2  %H3 %H4 %H5 hrs".
     rewrite /c_query...
     wp_alloc resw as "Hrw"; tp_alloc as rest "Hrt"...
     (* proove that iteri has the same comportement *)
     (* iApply (wp_list_iteri db (λ: "i" "x", if: list_nth vq "i" then #rest <- "x" + ! #rest else #()) *)
     (*           vdb _ (λ i x, ∃ (n : nat), resw ↦ #n ∗ rest ↦ₛ #n)%I (λ i x, ∃ (n : nat), resw ↦ #n ∗ rest ↦ₛ #n)%I). *)
     Admitted.

  Lemma c_query_1_sens :
    ∀ (vq : val) (q : list bool),
      ⌜ is_list q vq ⌝ -∗ wp_sensitive (c_query vq) 1 (dlist nat) (dnat).
  Proof with (tp_pures; wp_pures).
    iIntros.
    rewrite /wp_sensitive.
    iIntros (_ K x x') "rhs".
    rewrite /c_query.
    wp_lam; tp_lam...
    wp_alloc res1 as "Hres1"; tp_alloc as res2 "Hres2"...
    (* issue, in wp_sensitive, x and x' are list nat not especially lists of the same size...*)
    (* need to show that for each elements of the lists if they are distant of n then the queue of the list is distant of d - n *)
    Admitted.


  Definition sum_db : val :=
    λ: "db",
      list_fold (λ: "acc" "x", "acc" + "x") #0 "db".

  Definition dN : val :=
    λ: "a" "b",
      if: "a" < "b"
      then "b" - "a"
      else "a" - "b".

  Definition normalize : val :=
    (* TODO check, there is certainely a modulo function that exists *)
    λ: "div" "mod" "db" "size",
      let: "s" := sum_db "db" in
      let: "ln" := list_map (λ: "x", "div" ("size" * "x") "s") "db" in
      let: "s'" := sum_db "ln" in
      let: "lln" := list_length "ln" in
      list_mapi (λ: "i" "x", (if: "i" < ("size" - "s'" - #1) `rem` "lln" then #1 else #0) + ("div" ("size" - "s'") "lln") + "x") "ln".

  Definition unif : val :=
    λ: "size" "div",
      list_init "size" (λ: "i", "div" #1 "size").

  Definition mw_upd : val :=
   λ: "div" "exp" "mod" "ηnum" "ηden" "size" "db" "q" "v",
     if: c_query "db" "q" < "v"
     then normalize "div" "mod" (list_mapi (λ: "i" "x", "exp" (-"eta" * (if: list_nth "q" "i" then #0 else #1)) * "x") "db") "size"
     else normalize "div" "mod" (list_mapi (λ: "i" "x", "exp" (-"eta" * (if: list_nth "q" "i" then #1 else #0)) * "x") "db") "size".

  Definition det_int_fun (f : val) : Prop :=
    ∀ K (n : nat),
      ⤇ fill K (f #n) -∗
      WP f #n {{v, ⤇ fill K (Val v) ∗ ∃ (n' : nat), ⌜ v = #n ⌝ }}.

  Definition det_q (q : val) : Prop :=
    ∀ K (vdb : val) (db : list nat),
      ⌜ is_list db vdb ⌝ -∗
      ⤇ fill K (q vdb) -∗
      WP q vdb {{v, ⤇ fill K (Val v) ∗ ∃ r : nat, ⌜ v = #r ⌝ }}.

  Definition spec_upd (upd : val) : Prop :=
    (∀ K (vdb vq : val) (l : Z) (db : list nat) (q : list bool),
           (* The update returns a database of the right size for the "right" inputs *)
         ⌜is_list db vdb⌝ ∗ ⌜is_list q vq⌝ ∗
         ⌜length q = length db⌝ -∗
         ⤇ fill K ((upd vdb) vq #l) -∗
         WP upd vdb vq #l
         {{ v, ⤇ fill K (Val v) ∗ ∃ db' : list nat, ⌜is_list db' v⌝ ∗ ⌜length db' = length db⌝ }}).

  Definition spec_stream (stream_q : val) (size_dom : nat) : Prop :=
    (∀ K (bs : val),
           (* stream_q returns a boolean query of the right size *)
         ⤇ fill K (stream_q bs) -∗
         WP stream_q bs
         {{ qopt, ⤇ fill K (Val qopt) ∗
                    (⌜qopt = NONEV⌝ ∨ ∃ (vq : val) (q : list bool),
                        ⌜is_list q vq⌝ ∗ ⌜length q = size_dom⌝ ∗ ⌜qopt = SOMEV vq⌝)}}).

  Definition spec_f (f : val) : Prop :=
     (∀ K (vq vdb: val) (db : list nat) (q : list bool),
            (* f returns a 1sens deterministic query for the "right" inputs *)
          ⌜is_list db vdb⌝ ∗ ⌜is_list q vq⌝ ∗
          ⌜length db = length q⌝ -∗ (* we need the original query to be a homogenous boolean query *)
          ⤇ fill K (f vq vdb) -∗
          WP f vq vdb
          {{ v, ⤇ fill K (Val v) ∗ □ wp_sensitive v 1 (dlist nat) dnat ∗ ⌜ det_q v ⌝ }}).
  Lemma upd_deterministic :
    (* If we have the good arguments then we get a distribution of the same size *)
    ∀ K (vdb vq : val) (db : list nat) (q : list bool) (l size ηnum ηden : nat) (div exp modu : val),
          ⌜ det_int_fun div ⌝ ∗ ⌜ det_int_fun exp ⌝ ∗ ⌜ det_int_fun modu ⌝  -∗
          ⌜ is_list q vq ⌝ ∗ ⌜ is_list db vdb ⌝ ∗ ⌜ length q = length db ⌝ -∗
          ⤇ fill K (mw_upd div exp modu #ηnum #ηden #size vdb vq #l) -∗
          WP mw_upd div exp modu #ηnum #ηden #size vdb vq #l
          {{ v, ⤇ fill K (Val v) ∗ ∃ (db' : list nat), ⌜ is_list db' v ⌝ ∗ ⌜ length db = length db' ⌝}}.
  Proof with (tp_pures; wp_pures).
    iIntros (K vdb vq db q l size ηnum ηden div exp modu) "(%Hf1 & %Hf2 & %Hf3) (%H1 & %H2 & %H3) hrs".
    rewrite /mw_upd...
    wp_bind (c_query _ _); tp_bind (c_query _ _).
    iPoseProof (c_query_det _ vq vdb q db (length db) $! _ _ _ _ with "hrs") as "Hcqd".
    Unshelve.
    2, 3, 4, 5: done.
    iApply (wp_strong_mono'' with "Hcqd").
    iIntros (vr) "(rhs & %r & ->)".
    simpl.

  Admitted.


  (** General implementation *)
  Definition oPMW_large : val :=
    λ: "x" "stream_q" "num" "den" "c" "t" "unif" "upd" "f1" "f2",
      let: "f" := (onSVT "num" "den" "t" "c") in
      (rec: "aux" "i" "bs" "distrib" :=
         match: "stream_q" "bs" with
         | NONE => "bs"  (* No more queries *)
         | SOME "q" =>
             if: "i" = "c" then (* We made too many updates *)
               "aux" "i" (list_cons (c_query "distrib" "q") "bs") "distrib"
             else (
               match: "f" "x" ("f1" "q" "distrib") with
               | NONE =>
                   match: "f" "x" ("f2" "q" "distrib") with
                   | NONE => "aux" "i" (list_cons (c_query "distrib" "q") "bs") "distrib"
                   (* The answer is under the threshold *)
                   | SOME "v" => "aux" ("i" + #1) (list_cons "v" "bs") ("upd" "distrib" "q" (c_query "distrib" "q" + "v"))
                   end
               | SOME "v" => "aux" ("i" + #1) (list_cons "v" "bs") ("upd" "distrib" "q" (c_query "distrib" "q" - "v"))
               end)
         end) #0 list_nil "unif".

  Definition oPMW : val :=
    λ: "εnum" "εden" "αnum" "αden" "βnum" "βden" "ηnum" "ηden" "db" "unif" "size_db" "size_dom" "stream_q" "nb_q" "upd" "fc" "ft",
      let: "c" := "fc" "size_dom" "αden" "αnum" in
      let: "t" := "ft" "εnum" "εden" "βnum" "βden" "c" "nb_q" "size_db" in
      let: "f1" := (λ: "q" "distrib" "x", c_query "x" "q" "size" - c_query "distrib" "q" "size") in
      let: "f2" := (λ: "q" "distrib" "x", c_query "distrib" "q" "size" - c_query "x" "q" "size") in
      oPMW_large "db" "stream_q" "εnum" ("c"*"εden") "c" "t" "unif" "upd" (*"div" "exp" "mod" "ηnum" "ηden"*) "f1" "f2".

  (* Lemma f1_deterministic `(dDB : DistanceDB): *)
  (*   ⊢ □ (∀ K (distrib q : DB), (* we get back a 1sens query *) *)
  (*         (wp_sensitive q 1 dDB dZ) -∗ (* we need the original query to be 1 sensitive *) *)
  (*         ⤇ fill K ((λ: "x" "size", c_query "x" q "size" - c_query distrib q "size") q distrib) -∗ *)
  (*         WP (λ: "x" "size", c_query "x" q "size" - c_query distrib q "size") q distrib *)
  (*         {{ v, ⤇ fill K (Val v) ∗ □ wp_sensitive v 1 dDB dZ }}). *)

  #[local] Definition pMW_body (c : nat) (stream_q : val) {_ : Inject (list nat) val} (db : list nat) (f : val) (upd f1 f2: val) :=
       (rec: "aux" "i" "bs" "distrib" :=
                  match: stream_q "bs" with
                    InjL <> => "bs"
                  | InjR "q" =>
                    if: "i" = #c then "aux" "i" (list_cons (c_query "distrib" "q") "bs") "distrib"
                    else match: f (list.inject_list db) (f1 "q" "distrib") with
                           InjL <> =>
                             match: f (list.inject_list db) (f2 "q" "distrib") with
                               InjL <> => "aux" "i" (list_cons (c_query "distrib" "q") "bs") "distrib"
                             | InjR "v" => "aux" ("i" + #1) (list_cons "v" "bs") (upd "distrib" "q" (c_query "distrib" "q" + "v"))
                             end
                         | InjR "v" => "aux" ("i" + #1) (list_cons "v" "bs") (upd "distrib" "q" (c_query "distrib" "q" - "v"))
                         end
                  end)%V.

  Lemma pMW_general_diffpriv (num den c t : nat) (stream_q : val) (upd f1 f2 vunif : val) (unif : list nat) :
    let ε := IZR num / IZR den in
    let size_dom := length unif in
    ⌜ is_list unif vunif ⌝ -∗
    ⌜ length unif = size_dom ⌝ -∗
    ∀ (εpos : 0 < ε) (cpos : (0 < c)%nat) (tpos : (0 < t)%nat),
      □ (∀ K (bs : val),
            (* stream_q returns a boolean query of the right size *)
          ⤇ fill K (stream_q bs) -∗
          WP stream_q bs
          {{ qopt, ⤇ fill K (Val qopt) ∗
                     (⌜qopt = NONEV⌝ ∨ ∃ (vq : val) (q : list bool),
                         ⌜is_list q vq⌝ ∗ ⌜length q = size_dom⌝ ∗ ⌜qopt = SOMEV vq⌝)}}) -∗
      □ (∀ K (vdb vq : val) (l : Z) (db : list nat) (q : list bool),
            (* The update returns a database of the right size for the "right" inputs *)
          ⌜is_list db vdb⌝ -∗ ⌜is_list q vq⌝ -∗
          ⌜length db = size_dom ⌝ -∗ ⌜ length q = size_dom ⌝ -∗
          ⤇ fill K ((upd vdb) vq #l) -∗
          WP upd vdb vq #l
          {{ v, ⤇ fill K (Val v) ∗ ∃ db' : list nat, ⌜is_list db' v⌝ ∗ ⌜length db' = size_dom⌝ }}) -∗
      □ (∀ K (vq vdb: val) (db : list nat) (q : list bool),
            (* f returns a 1sens deterministic query for the "right" inputs *)
          ⌜is_list db vdb⌝ -∗ ⌜is_list q vq⌝ -∗
          ⌜length db = size_dom ⌝ -∗ ⌜ length q = size_dom ⌝ -∗ (* we need the original query to be a homogenous boolean query *)
          ⤇ fill K (f1 vq vdb) -∗
          WP f1 vq vdb
          {{ v, ⤇ fill K (Val v) ∗ □ wp_sensitive v 1 (dlist nat) dZ ∗ ⌜ det_q v ⌝ }}) -∗
      □ (∀ K (vq vdb: val) (db : list nat) (q : list bool),
            (* f returns a 1sens deterministic query for the "right" inputs *)
          ⌜is_list db vdb⌝ -∗ ⌜is_list q vq⌝ -∗
          ⌜length db = size_dom ⌝ -∗ ⌜ length q = size_dom ⌝ -∗ (* we need the original query to be a homogenous boolean query *)
          ⤇ fill K (f2 vq vdb) -∗
          WP f2 vq vdb
          {{ v, ⤇ fill K (Val v) ∗ □ wp_sensitive v 1 (dlist nat) dZ ∗ ⌜ det_q v ⌝ }}) -∗
      ∀ (db db' : list nat) (adj : (dlist nat) db db' <= 1) K,
      ⌜ length db = size_dom ⌝ ∗ ⌜ length db' = size_dom ⌝ -∗
      ↯m (c * ε) -∗
      ⤇ fill K (oPMW_large (inject db') stream_q #num #den #c #t vunif upd f1 f2) -∗
      WP oPMW_large (inject db) stream_q #num #den #c #t vunif upd f1 f2
      {{ v, ⤇ fill K (Val v) }}.
  Proof with (tp_pures; wp_pures).
    iIntros (ε size_dom) "#Hvunif #Hlunif %εpos %cpos %tpos #Hstream #Hupdate #Hf1 #Hf2 % % % % [%Hldb %Hlbd'] ε rhs".
    rewrite /oPMW_large...
    tp_bind (onSVT _ _ _ _); wp_bind (onSVT _ _ _ _).
    iPoseProof (nSVT_online_diffpriv with "ε rhs") as "spec" => //.
    iApply (wp_strong_mono'' with "spec").
    iIntros "%f (%f' & % & rhs & inSVT & spec) /=".
    do 4 tp_pure; do 4 wp_pure.
    rewrite -!/(pMW_body _ _ _ _ _ _ _).
    set (vdistrib := vunif).
    set (distrib := unif).
    set (bs := InjLV #()). rewrite {1}/bs.
    set (i := 0%Z). set (c' := c). rewrite {1 3}/c'.
    assert (0 <= i)%Z as ipos by lia. assert (c' + i = c)%Z as hi by lia.
    generalize i c' bs hi ipos vdistrib distrib. clear i c' bs hi ipos vdistrib distrib.
    intros.
    iRevert (i c' bs hi ipos vdistrib distrib) "Hvunif Hlunif rhs inSVT spec".
    iLöb as "IH".
    iIntros (i c' bs hi ipos vdistrib distrib) "#Hvdistrib #Hldistrib rhs inSVT #spec".
    rewrite {3 4}/pMW_body...
    wp_bind (stream_q _); tp_bind (stream_q _).
    iPoseProof ("Hstream" $! _  with "rhs") as "H_bs".
    iApply (wp_strong_mono'' with "H_bs").
    iIntros "%qopt (rhs & [->|(%vq & %q & #hq & #hlq & %Hvq)]) /="... 1: done.
    subst qopt...
    case_bool_decide...
    - (* Case where we have already proceed all the allowed updates *)
      do 2 rewrite -/(pMW_body _ _ _ _ _ _ _).
      wp_bind (c_query _ _); tp_bind (c_query _ _).
      iPoseProof (c_query_det _ vq vdistrib q distrib with "hq Hvdistrib hlq Hldistrib") as "h_c_query".
      iPoseProof ("h_c_query" with "rhs") as "h_c_query_det'".
      iApply (wp_strong_mono'' with "h_c_query_det'").
      iIntros (v) "[rhs _]"...
      simpl.
      rewrite /list_cons...
      iApply ("IH" with "[] [] Hvdistrib Hldistrib rhs inSVT"). 3: done. 1,2: iPureIntro. 1,2: lia.
    - (* We will deal with the nsvt *)
      do 2 rewrite -/(pMW_body _ _ _ _ _ _ _).
      wp_bind (f _ _); tp_bind (f' _ _).
      wp_bind (f1 _ _); tp_bind (f1 _ _).
      iSpecialize ("Hf1" $! _ vq vdistrib distrib q with "Hvdistrib hq Hldistrib hlq").
      iPoseProof ("Hf1" with "rhs") as "Hf1'".
      iApply (wp_strong_mono'' with "Hf1'").
      iIntros (q1) "[rhs [#sens_q1 #det_q1]]".
      tp_bind (f' _ _).
      iCombine "spec" as "spec_i".
      iEval (rewrite /nSVT_spec) in "spec_i".
      assert (not (i = c)). 1: intros h ; subst ; auto.
      assert (∃ c'', c' = S c'') as [? ->]. { destruct c'. 1: lia. eauto. }
      iSpecialize ("spec_i" $! _ _ db db' adj q1 _ with "sens_q1 rhs inSVT") => //.
      iApply (wp_strong_mono'' with "spec_i").
      iIntros "% (rhs & %e1 & -> & inSVT) /="...
      destruct e1...
      + (* e1 is a value (not none) *)
        wp_bind (c_query _ _); tp_bind (c_query _ _).
        iPoseProof (c_query_det _ vq vdistrib q distrib with "hq Hvdistrib hlq Hldistrib") as "h_c_query".
        iPoseProof ("h_c_query" with "rhs") as "h_c_query_det'".
        iApply (wp_strong_mono'' with "h_c_query_det'").
        iIntros (v) "[rhs [%nv %htv]]"...
        simpl.
        subst v.

        wp_binop; tp_binop.
        wp_bind (upd _ _ _ ); tp_bind (upd _ _ _ ).
        iPoseProof ("Hupdate" $! _ vdistrib vq _ distrib q with "Hvdistrib hq Hldistrib hlq rhs") as "Hupdate'".
        iApply (wp_strong_mono'' with "Hupdate'").
        iIntros (vdistrib') "(rhs & %distrib' & #Hvdistrib' & #Hldistrib')".
        simpl.
        rewrite /list_cons...
        iApply ("IH" with "[] [] Hvdistrib' Hldistrib' rhs inSVT"). 3: done. 1,2: iPureIntro. 1,2: lia.
      + (* e1 is none but we have inSVT (S x) *)
        iSimpl in "inSVT"...
        wp_bind (f _ _); tp_bind (f' _ _).
        wp_bind (f2 _ _); tp_bind (f2 _ _).

        iSpecialize ("Hf2" $! _ vq vdistrib distrib q with "Hvdistrib hq Hldistrib hlq").
        iPoseProof ("Hf2" with "rhs") as "Hf2'".
        iApply (wp_strong_mono'' with "Hf2'").
        iIntros (q2) "[rhs [#sens_q2 #det_q2]]".
        tp_bind (f' _ _).

        iCombine "spec" as "spec_i".
        iEval (rewrite /nSVT_spec) in "spec_i".
        iSpecialize ("spec_i" $! _ _ db db' adj q2 _ with "sens_q2 rhs inSVT") => //.
        iApply (wp_strong_mono'' with "spec_i").
        iIntros "% (rhs & %e2 & -> & inSVT) /=".
        destruct e2...
        -- (* e2 is a value (not none) *)
          wp_bind (c_query _ _); tp_bind (c_query _ _).
          iPoseProof (c_query_det _ vq vdistrib q distrib with "hq Hvdistrib hlq Hldistrib") as "h_c_query".
          iPoseProof ("h_c_query" with "rhs") as "h_c_query_det'".
          iApply (wp_strong_mono'' with "h_c_query_det'").
          iIntros (v) "[rhs [%nv %htv]]"...
          simpl.
          subst v.

          wp_binop; tp_binop.
          wp_bind (upd _ _ _ ); tp_bind (upd _ _ _ ).
          iPoseProof ("Hupdate" $! _ vdistrib vq _ distrib q with "Hvdistrib hq Hldistrib hlq rhs") as "Hupdate'".
          iApply (wp_strong_mono'' with "Hupdate'").
          iIntros (vdistrib') "(rhs & %distrib' & #Hvdistrib' & #Hldistrib')".
          simpl.
          rewrite /list_cons...
          iApply ("IH" with "[] [] Hvdistrib' Hldistrib' rhs inSVT"). 3: done. 1,2: iPureIntro. 1,2: lia.
        -- (* both answers are under the threshold *)
          wp_bind (c_query _ _); tp_bind (c_query _ _).
          iPoseProof (c_query_det _ vq vdistrib q distrib with "hq Hvdistrib hlq Hldistrib") as "h_c_query".
          iPoseProof ("h_c_query" with "rhs") as "h_c_query_det'".
          iApply (wp_strong_mono'' with "h_c_query_det'").
          iIntros (v) "[rhs [%nv %htv]]"...
          simpl.
          subst v.
          rewrite /list_cons...
          iApply ("IH" with "[] [] Hvdistrib Hldistrib rhs inSVT"). 3: done. 1,2: iPureIntro. 1,2: lia.
  Qed.

  Lemma pMW_diffpriv (εnum εden αnum αden βnum βden ηnum ηden size_db nb_q : nat) (unif : list nat) (stream_q fc ft (*div mul exp log modu*) : val) :
    let ε := IZR εnum / IZR εden in
    ∀ (εpos : 0 < ε),
      □ (∀ K (bs : val),
            (* stream_q returns a boolean query of the right size *)
          ⤇ fill K (stream_q bs) -∗
          WP stream_q bs
          {{ qopt, ⤇ fill K (Val qopt) ∗
                     (⌜qopt = NONEV⌝ ∨ ∃ (vq : val) (q : list bool),
                         ⌜is_list q vq⌝ ∗ ⌜length q = length unif⌝ ∗ ⌜qopt = SOMEV vq⌝)}}) -∗
      □ (∀ K (a1 a2 a3 : nat),
        ⤇ fill K (fc #a1 #a2 #a3) -∗
        WP fc #a1 #a2 #a3 {{ v, ⤇ fill K (Val v) ∗ ∃ (n : nat ), ⌜ v = #n ⌝ ∗ ⌜ 0 < n ⌝ }}) -∗
      □ (∀ K (a1 a2 a3 a4 a5 a6 a7 : nat),
        ⤇ fill K (ft #a1 #a2 #a3 #a4 #a5 #a6 #a7) -∗
        WP ft #a1 #a2 #a3 #a4 #a5 #a6 #a7 {{ v, ⤇ fill K (Val v) ∗ ∃ (n : nat ), ⌜ v = #n ⌝ ∗ ⌜ 0 < n ⌝ }}) -∗
      ∀ K (db db' : list nat) (adj : (dlist nat) db db' <= 1),
        ↯m (ε) -∗
        ⌜ length db = length unif ⌝ -∗
        ⌜ length db' = length unif ⌝ -∗
        ⌜ sum_db (inject db) = #size_db ⌝ -∗
        ⌜ sum_db (inject db') = #size_db ⌝ -∗
        ⤇ fill K (oPMW #εnum #εden #αnum #αden #βnum #βden #ηnum #ηden (Val (inject db')) (inject unif) #size_db #(length unif) stream_q #nb_q mw_upd fc ft(*div mul exp log modu*)) -∗
        WP oPMW #εnum #εden #αnum #αden #βnum #βden #ηnum #ηden (Val (inject db)) (inject unif) #size_db #(length unif) stream_q #nb_q mw_upd fc ft(*div mul exp log modu*)
        {{ v, ⤇ fill K (Val v) }}.
  Proof with (wp_pures; tp_pures).
    iIntros (ε εpos) "#Hstream #Hfc #Hft".
    iIntros (K db db' ddb) "Hε #Hl #Hl' #Hs #Hs' rhs".
    rewrite /oPMW...
    simpl.
    tp_pures.
    wp_bind (fc _ _ _); tp_bind (fc _ _ _).
    iPoseProof ("Hfc" $! _ _ _ with "rhs") as "Hfc'".
    iApply (wp_strong_mono'' with "Hfc'").
    iIntros (tmpC) "(rhs & %c & %HtmpC & %HposC)".
    rewrite HtmpC.
    simpl...
    wp_bind (ft _ _ _ _ _ _ _); tp_bind (ft _ _ _ _ _ _ _).
    iPoseProof ("Hft" $! _ _ _ with "rhs") as "Hft'".
    iApply (wp_strong_mono'' with "Hft'").
    iIntros (tmpT) "(rhs & %t & %HtmpT & %HposT)".
    rewrite HtmpT.
    simpl...
    iPoseProof (pMW_general_diffpriv εnum (c * εden) c t stream_q mw_upd (λ: "q" "distrib" "x", c_query "x" "q" "size" - c_query "distrib" "q" "size")%V
                  (λ: "q" "distrib" "x", c_query "distrib" "q" "size" - c_query "x" "q" "size")%V (inject unif) unif) as "pMWG".
    iSpecialize ("pMWG" $! _ _).
    Unshelve.
    2: { by apply is_list_inject. }
    2: { reflexivity. }
    iSpecialize ("pMWG" $! _ _ _).
    Unshelve.
    3 : { real_solver. }
    3 : { real_solver. }
    2: {
         do 2 rewrite -INR_IZR_INZ.
         rewrite mult_INR Rmult_comm Rdiv_mult_distr.
         replace (INR εnum / INR εden) with ε.
         {
           apply RIneq.Rdiv_pos_pos.
           1, 2: done.
         }
         subst ε.
         do 2 rewrite -INR_IZR_INZ.
         done.
    }

    (* Hypothesis of stream query *)
    iSpecialize ("pMWG" with "Hstream").

    (* Hyposthesis of update *)
    iSpecialize ("pMWG" with "[]" ).
    {
      admit.
    }

    (* Hyposthesis of f1 *)
    iSpecialize ("pMWG" with "[]" ).
    {
      iModIntro.
      iIntros (K' vq' vh h q') "#Hlh #Hlq' #Hsh #Hsq' rhs".
      tp_pures; wp_pures.
      iModIntro.
      iFrame.
      iSplit.
      - admit.
      - iPureIntro.
        rewrite /det_q.
        (* add a condition on the size of the list in det_q *)
        iIntros (K'' vh' h') "#Hlh' rhs".
        tp_pures; wp_pures.

        admit.
    }

    (* Hyposthesis of f2 *)
    iSpecialize ("pMWG" with "[]" ).
    {
      iModIntro.
      iIntros (K' vq' vh h q') "#Hlh #Hlq' #Hsh #Hsq' rhs".
      tp_pures; wp_pures.
      iModIntro.
      iFrame.
      iSplit.
      - admit.
      - iPureIntro.
        rewrite /det_q.
        (* add a condition on the size of the list in det_q *)
        admit.
    }

    iSpecialize ("pMWG" $! db db' ddb K).
    iSpecialize ("pMWG" with "[$]").
    iSpecialize ("pMWG" with "[Hε]").
    {
      subst ε.
      (* Set Printing Coercions. *)
      replace (INR c * (IZR (Z.of_nat εnum) / IZR (Z.of_nat (c * εden)))) with (IZR (Z.of_nat εnum) / IZR (Z.of_nat εden)). 1: done.
      do 3 rewrite -INR_IZR_INZ.
      rewrite mult_INR Rmult_div_assoc Rdiv_mult_distr Rmult_div_r.
      1: done.
      lra.
    }

    (* Set Printing Coercions. *)
    replace (Val #(LitInt (Z.of_nat (c * εden)))) with (Val #(LitInt (Z.of_nat c * Z.of_nat εden))).
    { iApply ("pMWG" with "rhs"). }
    do 3 f_equal.
    lia.



End pmw.
