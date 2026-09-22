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
    λ: "q" "db",
      Snd
        (if: list_length "db" <= list_length "q"
        then
          list_fold (λ: "acc" "x",
              ((Fst "acc")+#1, (Snd "acc") + (if: (list_nth "q" (Fst "acc")) then "x" else #0))) (#0, #0) "db"
        else
          list_fold (λ: "acc" "x",
              ((Fst "acc")+#1, (Snd "acc") + (if: "x" then list_nth "db" (Fst "acc") else #0))) (#0, #0) "db").

  Lemma c_query_det :
    ∀ K (vq vdb: val) (q : list bool) (db : list nat),
      ⌜ is_list q vq ⌝ -∗ ⌜ is_list db vdb ⌝ -∗
      ⤇ fill K (c_query vq vdb) -∗
      WP c_query vq vdb {{ v, ⤇ fill K (Val v) ∗ ∃ (n : nat), ⌜ v = #n ⌝ }}.
   Proof with (wp_pures; tp_pures).
     iIntros (K vq vdb q db) "%H1  %H2 hrs".
     rewrite /c_query...
     (* proove that iteri has the same comportement *)
     (* iApply (wp_list_iteri db (λ: "i" "x", if: list_nth vq "i" then #rest <- "x" + ! #rest else #()) *)
     (*           vdb _ (λ i x, ∃ (n : nat), resw ↦ #n ∗ rest ↦ₛ #n)%I (λ i x, ∃ (n : nat), resw ↦ #n ∗ rest ↦ₛ #n)%I). *)
     (* Doable *)
     Admitted.

  Lemma c_query_1_sens :
    ∀ (vq : val) (q : list bool),
      ⌜ is_list q vq ⌝ -∗ wp_sensitive (c_query vq) 1 (dlist nat) (dZ).
  Proof with (tp_pures; wp_pures).
    iIntros.
    rewrite /wp_sensitive.
    iIntros (_ K x x') "rhs".
    rewrite /c_query.
    wp_lam; tp_lam...
    (* issue, in wp_sensitive, x and x' are list nat not especially lists of the same size...*)
    (* need to show that for each elements of the lists if they are distant of n then the queue of the list is distant of d - n *)
    (* More Difficult *)
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
    λ: "db" "size",
      let: "s" := sum_db "db" in
      let: "ln" := list_map (λ: "x", ("size" * "x") `quot` "s") "db" in
      let: "s'" := sum_db "ln" in
      let: "lln" := list_length "ln" in
      list_mapi (λ: "i" "x", (if: "i" < ("size" - "s'" - #1) `rem` "lln" then #1 else #0) + (("size" - "s'") `quot` "lln") + "x") "ln".

  Definition get_unif : val :=
    λ: "size_dom" "size_db",
      normalize (list_init "size_dom" (λ: "i", #1)) "size_db".

  Definition mw_upd : val :=
   λ: "exp" "ηnum" "ηden" "size" "db" "q" "v",
     if: c_query "q" "db" < "v"
     then normalize (list_mapi (λ: "i" "x", "exp" (-"eta" * (if: list_nth "q" "i" then #0 else #1)) * "x") "db") "size"
     else normalize (list_mapi (λ: "i" "x", "exp" (-"eta" * (if: list_nth "q" "i" then #1 else #0)) * "x") "db") "size".

  Definition det_int_fun (f : val) : Prop :=
    ∀ K (n : nat),
      ⤇ fill K (f #n) -∗
      WP f #n {{v, ⤇ fill K (Val v) ∗ ∃ (n' : Z), ⌜ v = #n ⌝ }}.

  Definition det_q (q : val) : Prop :=
    ∀ K (vdb : val) (db : list nat),
      ⌜ is_list db vdb ⌝ -∗
      ⤇ fill K (q vdb) -∗
      WP q vdb {{v, ⤇ fill K (Val v) ∗ ∃ r : Z, ⌜ v = #r ⌝ }}.

  Definition spec_upd (upd : val) : Prop :=
    (∀ K (vdb vq : val) (l : Z) (db : list nat) (q : list bool),
           (* The update returns a database of the right size for the "right" inputs *)
         ⌜is_list db vdb⌝ ∗ ⌜is_list q vq⌝ ∗
         ⤇ fill K ((upd vdb) vq #l) -∗
         WP upd vdb vq #l
         {{ v, ⤇ fill K (Val v) ∗ ∃ db' : list nat, ⌜is_list db' v⌝ }}).

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
          ⤇ fill K (f vq vdb) -∗
          WP f vq vdb
          {{ v, ⤇ fill K (Val v) ∗ □ wp_sensitive v 1 (dlist nat) dnat ∗ ⌜ det_q v ⌝ }}).

  Lemma upd_deterministic :
    (* If we have the good arguments then we get a distribution of the same size *)
    ∀ K (vdb vq : val) (db : list nat) (q : list bool) (l size ηnum ηden : nat) (exp : val),
          ⌜ det_int_fun exp ⌝ -∗
          ⌜ is_list q vq ⌝ ∗ ⌜ is_list db vdb ⌝ -∗
          ⤇ fill K (mw_upd exp #ηnum #ηden #size vdb vq #l) -∗
          WP mw_upd exp #ηnum #ηden #size vdb vq #l
          {{ v, ⤇ fill K (Val v) ∗ ∃ (db' : list nat), ⌜ is_list db' v ⌝ }}.
  Proof with (tp_pures; wp_pures).
    iIntros (K vdb vq db q l size ηnum ηden exp) "%Hexp (%H1 & %H2) hrs".
    rewrite /mw_upd...
    wp_bind (c_query _ _); tp_bind (c_query _ _).
    iPoseProof (c_query_det _ vq vdb q db $! _ _ with "hrs") as "Hcqd".
    Unshelve.
    2, 3: done.
    iApply (wp_strong_mono'' with "Hcqd").
    iIntros (vr) "(rhs & %r & ->)".
    simpl.
  Admitted.

  Lemma upd_partial :
    ∀ K (exp : val) (ηnum ηden size_db : nat),
      ⤇ fill K (mw_upd exp #ηnum #ηden #size_db) -∗
      WP mw_upd exp #ηnum #ηden #size_db {{ f,
          ⤇ fill K (Val f) ∗
          □ (∀ K' (vdb vq : val) (v : Z) (db : list nat) (q : list bool),
            ⌜ is_list db vdb ⌝ -∗
            ⌜ is_list q vq ⌝ -∗
            ⤇ fill K' (f vdb vq #v) -∗
            WP f vdb vq #v {{ vdb',
                ⤇ fill K' (Val vdb') ∗ ∃ (db' : list nat), ⌜is_list db' vdb'⌝
            }})
      }}.
  Proof with (tp_pures; wp_pures).
    iIntros (K exp ηnum ηden size_db) "rhs".
    rewrite /mw_upd.
  Admitted.

  Lemma get_unif_det :
    ∀ K (size_db size_dom : nat),
      ⤇ fill K (get_unif #size_db #size_dom) -∗
      WP get_unif #size_db #size_dom {{ vu,
           ⤇ fill K (Val vu) ∗ ∃ (u : list nat), ⌜ is_list u vu ⌝
      }}.
  Proof.
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
               "aux" "i" (list_cons (c_query "q" "distrib") "bs") "distrib"
             else (
               match: "f" "x" ("f1" "q" "distrib") with
               | NONE =>
                   match: "f" "x" ("f2" "q" "distrib") with
                   | NONE => "aux" "i" (list_cons (c_query "q" "distrib") "bs") "distrib"
                   (* The answer is under the threshold *)
                   | SOME "v" => "aux" ("i" + #1) (list_cons "v" "bs") ("upd" "distrib" "q" (c_query "q" "distrib" + "v"))
                   end
               | SOME "v" => "aux" ("i" + #1) (list_cons "v" "bs") ("upd" "distrib" "q" (c_query "q" "distrib" - "v"))
               end)
         end) #0 list_nil "unif".

  Definition oPMW : val :=
    λ: "εnum" "εden" "αnum" "αden" "βnum" "βden" "ηnum" "ηden" "db" "size_db" "size_dom" "stream_q" "nb_q" "fc" "ft" "exp",
      let: "c" := "fc" "size_dom" "αden" "αnum" in
      let: "t" := "ft" "εnum" "εden" "βnum" "βden" "c" "nb_q" "size_db" in
      let: "f1" := (λ: "q" "distrib" "x", c_query "q" "x" - c_query "q" "distrib") in
      let: "f2" := (λ: "q" "distrib" "x", c_query "q" "distrib" - c_query "q" "x") in
      let: "unif" := get_unif "size_dom" "size_db" in
      let: "upd" := mw_upd "exp" "ηnum" "ηden" "size_db" in
      oPMW_large "db" "stream_q" "εnum" ("c"*"εden") "c" "t" "unif" "upd" "f1" "f2".

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
                    if: "i" = #c then "aux" "i" (list_cons (c_query "q" "distrib") "bs") "distrib"
                    else match: f (list.inject_list db) (f1 "q" "distrib") with
                           InjL <> =>
                             match: f (list.inject_list db) (f2 "q" "distrib") with
                               InjL <> => "aux" "i" (list_cons (c_query "q" "distrib") "bs") "distrib"
                             | InjR "v" => "aux" ("i" + #1) (list_cons "v" "bs") (upd "distrib" "q" (c_query "q" "distrib" + "v"))
                             end
                         | InjR "v" => "aux" ("i" + #1) (list_cons "v" "bs") (upd "distrib" "q" (c_query "q" "distrib" - "v"))
                         end
                  end)%V.

  Lemma pMW_general_diffpriv (num den c t : nat) (stream_q : val) (upd f1 f2 vunif : val) (unif : list nat) :
    let ε := IZR num / IZR den in
    let size_dom := length unif in
    ⌜ is_list unif vunif ⌝ -∗
    ∀ (εpos : 0 < ε) (cpos : (0 < c)%nat) (tpos : (0 < t)%nat),
      □ (∀ K (bs : val),
            (* stream_q returns a boolean query of the right size *)
          ⤇ fill K (stream_q bs) -∗
          WP stream_q bs
          {{ qopt, ⤇ fill K (Val qopt) ∗
                     (⌜qopt = NONEV⌝ ∨ ∃ (vq : val) (q : list bool),
                         ⌜is_list q vq⌝ ∗ ⌜qopt = SOMEV vq⌝)}}) -∗
      □ (∀ K (vdb vq : val) (l : Z) (db : list nat) (q : list bool),
            (* The update returns a database of the right size for the "right" inputs *)
          ⌜is_list db vdb⌝ -∗ ⌜is_list q vq⌝ -∗
          ⤇ fill K ((upd vdb) vq #l) -∗
          WP upd vdb vq #l
          {{ v, ⤇ fill K (Val v) ∗ ∃ db' : list nat, ⌜is_list db' v⌝ }}) -∗
      □ (∀ K (vq vdb: val) (db : list nat) (q : list bool),
            (* f returns a 1sens deterministic query for the "right" inputs *)
          ⌜is_list db vdb⌝ -∗ ⌜is_list q vq⌝ -∗
          ⤇ fill K (f1 vq vdb) -∗
          WP f1 vq vdb
          {{ v, ⤇ fill K (Val v) ∗ □ wp_sensitive v 1 (dlist nat) dZ ∗ ⌜ det_q v ⌝ }}) -∗
      □ (∀ K (vq vdb: val) (db : list nat) (q : list bool),
            (* f returns a 1sens deterministic query for the "right" inputs *)
          ⌜is_list db vdb⌝ -∗ ⌜is_list q vq⌝ -∗
          ⤇ fill K (f2 vq vdb) -∗
          WP f2 vq vdb
          {{ v, ⤇ fill K (Val v) ∗ □ wp_sensitive v 1 (dlist nat) dZ ∗ ⌜ det_q v ⌝ }}) -∗
      ∀ (db db' : list nat) (adj : (dlist nat) db db' <= 1) K,
      ↯m (c * ε) -∗
      ⤇ fill K (oPMW_large (inject db') stream_q #num #den #c #t vunif upd f1 f2) -∗
      WP oPMW_large (inject db) stream_q #num #den #c #t vunif upd f1 f2
      {{ v, ⤇ fill K (Val v) }}.
  Proof with (tp_pures; wp_pures).
    iIntros (ε size_dom) "#Hvunif %εpos %cpos %tpos #Hstream #Hupdate #Hf1 #Hf2 % % % % ε rhs".
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
    iRevert (i c' bs hi ipos vdistrib distrib) "Hvunif rhs inSVT spec".
    iLöb as "IH".
    iIntros (i c' bs hi ipos vdistrib distrib) "#Hvdistrib rhs inSVT #spec".
    rewrite {3 4}/pMW_body...
    wp_bind (stream_q _); tp_bind (stream_q _).
    iPoseProof ("Hstream" $! _  with "rhs") as "H_bs".
    iApply (wp_strong_mono'' with "H_bs").
    iIntros "%qopt (rhs & [->|(%vq & %q & #hq & %Hvq)]) /="... 1: done.
    subst qopt...
    case_bool_decide...
    - (* Case where we have already proceed all the allowed updates *)
      do 2 rewrite -/(pMW_body _ _ _ _ _ _ _).
      wp_bind (c_query _ _); tp_bind (c_query _ _).
      iPoseProof (c_query_det _ vq vdistrib q distrib with "hq Hvdistrib") as "h_c_query".
      iPoseProof ("h_c_query" with "rhs") as "h_c_query_det'".
      iApply (wp_strong_mono'' with "h_c_query_det'").
      iIntros (v) "[rhs _]"...
      simpl.
      rewrite /list_cons...
      iApply ("IH" with "[] [] Hvdistrib rhs inSVT"). 3: done. 1,2: iPureIntro. 1,2: lia.
    - (* We will deal with the nsvt *)
      do 2 rewrite -/(pMW_body _ _ _ _ _ _ _).
      wp_bind (f _ _); tp_bind (f' _ _).
      wp_bind (f1 _ _); tp_bind (f1 _ _).
      iSpecialize ("Hf1" $! _ vq vdistrib distrib q with "Hvdistrib hq").
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
        iPoseProof (c_query_det _ vq vdistrib q distrib with "hq Hvdistrib") as "h_c_query".
        iPoseProof ("h_c_query" with "rhs") as "h_c_query_det'".
        iApply (wp_strong_mono'' with "h_c_query_det'").
        iIntros (v) "[rhs [%nv %htv]]"...
        simpl.
        subst v.
        wp_binop; tp_binop.
        wp_bind (upd _ _ _ ); tp_bind (upd _ _ _ ).
        iPoseProof ("Hupdate" $! _ vdistrib vq _ distrib q with "Hvdistrib hq rhs") as "Hupdate'".
        iApply (wp_strong_mono'' with "Hupdate'").
        iIntros (vdistrib') "(rhs & %distrib' & #Hvdistrib')".
        simpl.
        rewrite /list_cons...
        iApply ("IH" with "[] [] Hvdistrib' rhs inSVT"). 3: done. 1,2: iPureIntro. 1,2: lia.
      + (* e1 is none but we have inSVT (S x) *)
        iSimpl in "inSVT"...
        wp_bind (f _ _); tp_bind (f' _ _).
        wp_bind (f2 _ _); tp_bind (f2 _ _).
        iSpecialize ("Hf2" $! _ vq vdistrib distrib q with "Hvdistrib hq").
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
          iPoseProof (c_query_det _ vq vdistrib q distrib with "hq Hvdistrib") as "h_c_query".
          iPoseProof ("h_c_query" with "rhs") as "h_c_query_det'".
          iApply (wp_strong_mono'' with "h_c_query_det'").
          iIntros (v) "[rhs [%nv %htv]]"...
          simpl.
          subst v.

          wp_binop; tp_binop.
          wp_bind (upd _ _ _ ); tp_bind (upd _ _ _ ).
          iPoseProof ("Hupdate" $! _ vdistrib vq _ distrib q with "Hvdistrib hq rhs") as "Hupdate'".
          iApply (wp_strong_mono'' with "Hupdate'").
          iIntros (vdistrib') "(rhs & %distrib' & #Hvdistrib')".
          simpl.
          rewrite /list_cons...
          iApply ("IH" with "[] [] Hvdistrib' rhs inSVT"). 3: done. 1,2: iPureIntro. 1,2: lia.
        -- (* both answers are under the threshold *)
          wp_bind (c_query _ _); tp_bind (c_query _ _).
          iPoseProof (c_query_det _ vq vdistrib q distrib with "hq Hvdistrib") as "h_c_query".
          iPoseProof ("h_c_query" with "rhs") as "h_c_query_det'".
          iApply (wp_strong_mono'' with "h_c_query_det'").
          iIntros (v) "[rhs [%nv %htv]]"...
          simpl.
          subst v.
          rewrite /list_cons...
          iApply ("IH" with "[] [] Hvdistrib rhs inSVT"). 3: done. 1,2: iPureIntro. 1,2: lia.
  Qed.

  Lemma pMW_diffpriv (εnum εden αnum αden βnum βden ηnum ηden size_db size_dom nb_q : nat) (stream_q fc ft exp : val) :
    let ε := IZR εnum / IZR εden in
    ∀ (εpos : 0 < ε),
      □ (∀ K (bs : val),
            (* stream_q returns a boolean query of the right size *)
          ⤇ fill K (stream_q bs) -∗
          WP stream_q bs
          {{ qopt, ⤇ fill K (Val qopt) ∗
                     (⌜qopt = NONEV⌝ ∨ ∃ (vq : val) (q : list bool),
                         ⌜is_list q vq⌝ ∗ ⌜qopt = SOMEV vq⌝)}}) -∗
      □ (∀ K (a1 a2 a3 : nat),
        ⤇ fill K (fc #a1 #a2 #a3) -∗
        WP fc #a1 #a2 #a3 {{ v, ⤇ fill K (Val v) ∗ ∃ (n : nat ), ⌜ v = #n ⌝ ∗ ⌜ 0 < n ⌝ }}) -∗
      □ (∀ K (a1 a2 a3 a4 a5 a6 a7 : nat),
        ⤇ fill K (ft #a1 #a2 #a3 #a4 #a5 #a6 #a7) -∗
        WP ft #a1 #a2 #a3 #a4 #a5 #a6 #a7 {{ v, ⤇ fill K (Val v) ∗ ∃ (n : nat ), ⌜ v = #n ⌝ ∗ ⌜ 0 < n ⌝ }}) -∗
      (* hypothesis on the maths functions *)
      □ (∀ K (a : nat),
        ⤇ fill K (exp #a) -∗
        WP exp #a {{ v, ⤇ fill K (Val v) ∗ ∃ (n : nat), ⌜ v = #n ⌝ }}) -∗
      ∀ K (db db' : list nat) (adj : (dlist nat) db db' <= 1),
        ↯m (ε) -∗
        ⤇ fill K (oPMW #εnum #εden #αnum #αden #βnum #βden #ηnum #ηden (Val (inject db')) #size_db #size_dom stream_q #nb_q fc ft exp) -∗
        WP oPMW #εnum #εden #αnum #αden #βnum #βden #ηnum #ηden (Val (inject db)) #size_db #size_dom stream_q #nb_q fc ft exp
        {{ v, ⤇ fill K (Val v) }}.
  Proof with (wp_pures; tp_pures).
    iIntros (ε εpos) "#Hstream #Hfc #Hft #Hexp".
    iIntros (K db db' ddb) "Hε rhs".
    rewrite /oPMW.
    simpl...
    tp_bind (fc _ _ _); wp_bind (fc _ _ _).
    iPoseProof ("Hfc" $! _ _ _ _ with "rhs") as "Hfc'".
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

    wp_bind (get_unif _ _); tp_bind (get_unif _ _).
    (* iPoseProof get_unif_det as "Hunif_det". *)
    (* iCombine *)
    iPoseProof (get_unif_det _ _ _ with "rhs") as "Hunif_det".
    iApply (wp_strong_mono'' with "Hunif_det").
    iIntros (vunif) "(rhs & %unif & %Hunif)".
    simpl...

    wp_bind (mw_upd _ _ _ _); tp_bind (mw_upd _ _ _ _).
    (* iPoseProof upd_partial as "Hupd_partial". *)
    iPoseProof (upd_partial _ _ _ _ _ with "rhs") as "Hupd_partial".
    iApply (wp_strong_mono'' with "Hupd_partial").
    iIntros (upd) "[rhs #Hupd]"...
    iPoseProof (pMW_general_diffpriv εnum (c * εden) c t stream_q upd (λ: "q" "distrib" "x", c_query "q" "x" - c_query "q" "distrib")%V
                  (λ: "q" "distrib" "x", c_query "q" "distrib" - c_query "q" "x")%V vunif unif) as "pMWG".
    iSpecialize ("pMWG" $! _).
    Unshelve.
    2: { by apply Hunif. }
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
    iSpecialize ("pMWG" with "Hupd").

    (* Hyposthesis of f1 *)
    iSpecialize ("pMWG" with "[]" ).
    {
      iModIntro.
      iIntros (K' vq' vh h q') "%Hlh %Hlq' rhs".
      tp_pures; wp_pures.
      iModIntro.
      iFrame.
      iSplit.
      - iModIntro.
        rewrite /wp_sensitive.
        iIntros (_ Kw x x') "rhs"...
        iPoseProof (c_query_1_sens vq' q') as "Hq1s".
        iSpecialize ("Hq1s" $! _).
        iPoseProof (c_query_det _ vq' vh q' h) as "Hqdet".
        iSpecialize ("Hqdet" $! _ _).
        rewrite /wp_sensitive.
        wp_bind (c_query _ _); tp_bind (c_query _ _).
        iPoseProof ("Hqdet" with "rhs") as "Hqdet'".
        iApply (wp_strong_mono'' with "Hqdet'").
        iIntros (vres_f1_d) "(rhs & %res_f1_d & ->)".

        wp_bind (c_query _ _); tp_bind (c_query _ _).
        iSpecialize ("Hq1s" $! _ _ x x').
        iPoseProof ("Hq1s" with "rhs") as "Hq1s'".
        iApply (wp_strong_mono'' with "Hq1s'").
        iIntros (vres_f1_n1) "(%res_f1_n1 & %res_f1_n2 & -> & rhs & %Hdisf1)"...
        (* Set Printing All. *)
        iModIntro.
        simpl.
        iExists (res_f1_n1 - res_f1_d)%Z.
        iExists (res_f1_n2 - res_f1_d)%Z.
        (* Set Printing All. *)
        (* replace (BinOp MinusOp (Val (LitV (LitInt res_f1_n2))) (Val (LitV (LitInt res_f1_d)))) with (LitV (LitInt (Z.sub res_f1_n2 res_f1_d))). *)
        iSplit. 1: done.
        iSplit.
        {
          replace (BinOp MinusOp (Val (LitV (LitInt res_f1_n2))) (Val (LitV (LitInt res_f1_d)))) with (Val (LitV (LitInt (Z.sub res_f1_n2 res_f1_d)))).
          1: done.
          (* Set Printing All. *)
          admit.
        }
        iPureIntro.
        replace (res_f1_n1 - res_f1_d - (res_f1_n2 - res_f1_d))%Z with (res_f1_n1 - res_f1_n2)%Z.
        { done. }.
        lia.

        Unshelve.
        1, 2, 3: done.
        lra.

      - iPureIntro.
        rewrite /det_q.
        iIntros (K'' vdb'' db'') "%Hldb'' rhs".
        tp_pures; wp_pures.
        wp_bind (c_query _ _); tp_bind (c_query _ _).
        iPoseProof (c_query_det _ vq' vh q' h) as "Hqdet".
        iSpecialize ("Hqdet" $! _ _).
        iPoseProof ("Hqdet" with "rhs") as "Hqdet'".
        iApply (wp_strong_mono'' with "Hqdet'").
        iIntros (vres_f1_d') "(rhs & %res_f1_d' & ->)".
        wp_bind (c_query _ _); tp_bind (c_query _ _).
        iClear "Hqdet".
        iPoseProof (c_query_det _ vq' vdb'' q' db'') as "Hqdet".
        iSpecialize ("Hqdet" $! _ _).
        iPoseProof ("Hqdet" with "rhs") as "Hqdet'".
        iApply (wp_strong_mono'' with "Hqdet'").
        iIntros (vres_f1_d'') "(rhs & %res_f1_d'' & ->)".
        simpl...
        iModIntro.
        iSplit.
        {
          replace (BinOp MinusOp (Val (LitV (LitInt res_f1_d''))) (Val (LitV (LitInt res_f1_d')))) with (Val (LitV (LitInt (Z.sub res_f1_d'' res_f1_d')))).
          1: done.
          (* Set Printing All. *)
          admit. }
        iExists (res_f1_d'' - res_f1_d')%Z.
        iPureIntro.
        done.

        Unshelve.
        1, 2, 3, 4: done.
    }

    (* Hyposthesis of f2 *)
    iSpecialize ("pMWG" with "[]" ).
    {
      iModIntro.
      iIntros (K' vq' vh h q') "%Hlh %Hlq' rhs".
      tp_pures; wp_pures.
      iModIntro.
      iFrame.
      iSplit.
      - iModIntro.
        rewrite /wp_sensitive.
        iIntros (_ Kw x x') "rhs"...
        iPoseProof (c_query_1_sens vq' q') as "Hq2s".
        iSpecialize ("Hq2s" $! _).
        rewrite /wp_sensitive.
        wp_bind (c_query _ _); tp_bind (c_query _ _).
        iSpecialize ("Hq2s" $! _ _ x x').
        iPoseProof ("Hq2s" with "rhs") as "Hq2s'".
        iApply (wp_strong_mono'' with "Hq2s'").
        iIntros (vres_f2_n1) "(%res_f2_n1 & %res_f2_n2 & -> & rhs & %Hdisf2)"...
        simpl...

        wp_bind (c_query _ _); tp_bind (c_query _ _).
        iPoseProof (c_query_det _ vq' vh q' h) as "Hqdet".
        iSpecialize ("Hqdet" $! _ _).
        iPoseProof ("Hqdet" with "rhs") as "Hqdet'".
        iApply (wp_strong_mono'' with "Hqdet'").
        iIntros (vres_f1_d) "(rhs & %res_f1_d & ->)".
        simpl...

        iModIntro.
        iExists (res_f1_d - res_f2_n1)%Z.
        iExists (res_f1_d - res_f2_n2)%Z.
        iSplit.
        { done. }
        iSplit.
        {
          replace (BinOp MinusOp (Val (LitV (LitInt res_f1_d))) (Val (LitV (LitInt res_f2_n2)))) with (Val (LitV (LitInt (Z.sub res_f1_d res_f2_n2)))).
          1: done.
          (* Set Printing All. *)
          admit. }

        iPureIntro.
        replace (res_f1_d - res_f2_n1 - (res_f1_d - res_f2_n2))%Z with (- res_f2_n1 + res_f2_n2)%Z.
        { replace (Rabs (IZR (- res_f2_n1 + res_f2_n2))) with (Rabs (IZR (res_f2_n1 - res_f2_n2))).
          1: done.
          do 2 rewrite plus_IZR opp_IZR.
          replace (IZR res_f2_n1 + - IZR res_f2_n2) with (-(- IZR res_f2_n1 + IZR res_f2_n2)).
          1: by rewrite Rabs_Ropp.
          lra. }
        lia.

        Unshelve.
        2: lra.
        1, 2, 3: done.

      - iPureIntro.
        rewrite /det_q.
        iIntros (K'' vdb'' db'') "%Hldb'' rhs".
        tp_pures; wp_pures.
        wp_bind (c_query _ _); tp_bind (c_query _ _).
        iPoseProof (c_query_det _ vq' vdb'' q' db'') as "Hqdet".
        iSpecialize ("Hqdet" $! _ _).
        iPoseProof ("Hqdet" with "rhs") as "Hqdet'".
        iApply (wp_strong_mono'' with "Hqdet'").
        iIntros (vres_f1_d'') "(rhs & %res_f1_d'' & ->)".
        iClear "Hqdet".
        simpl...

        wp_bind (c_query _ _); tp_bind (c_query _ _).
        iPoseProof (c_query_det _ vq' vh q' h) as "Hqdet".
        iSpecialize ("Hqdet" $! _ _).
        iPoseProof ("Hqdet" with "rhs") as "Hqdet'".
        iApply (wp_strong_mono'' with "Hqdet'").
        iIntros (vres_f1_d') "(rhs & %res_f1_d' & ->)".
        simpl...

        iModIntro.
        iSplit.
        {
          replace (BinOp MinusOp (Val (LitV (LitInt res_f1_d'))) (Val (LitV (LitInt res_f1_d'')))) with (Val (LitV (LitInt (Z.sub res_f1_d' res_f1_d'')))).
          1: done.
          (* Set Printing All. *)

          admit. }
        iExists (res_f1_d' - res_f1_d'')%Z.
        iPureIntro.
        done.

        Unshelve.
        1, 2, 3, 4: done.
    }

    iSpecialize ("pMWG" $! db db' ddb K).
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
    simpl...
    replace (Val #(LitInt (Z.of_nat (c * εden)))) with (Val #(LitInt (Z.of_nat c * Z.of_nat εden))).
    { iApply ("pMWG" with "rhs"). }
    do 3 f_equal.
    lia.
    (* It would be greate if I could find a way to get rid of these 4 same goal. *)
Admitted.



End pmw.
