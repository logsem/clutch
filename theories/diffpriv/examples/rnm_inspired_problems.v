From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import adequacy diffpriv proofmode.

Section rnm.
  Context `{!diffprivGS Σ}.

  #[local] Open Scope R.
  (* An online version of RNM (oRNM) providing two methods:
- add_query receives and evaluates queries one at a time, storing the highest (noisy) result,
- release outputs the index of the query with the highest result. *)
  Definition report_noisy_max_online : val :=
    λ:"num" "den" "evalQ" "d",
      let: "maxI" := ref #(-1) in
      let: "maxA" := ref #0 in
      let: "add_query" :=
        λ:"i",
          (let: "a" := Laplace "num" (#2 * "den") ("evalQ" "i" "d") in
           (if: "i" = #0 `or` ! "maxA" < "a" then
              "maxA" <- "a" ;;
              "maxI" <- "i"
            else #())) in
      let: "release" :=
        λ:"_",
          ! "maxI"
      in ("add_query", "release").

  (* Given the error credits for one run of RNM, initializing oRNM provides an abstract token AUTH
  that is required to call the add_query and release methods, and...
- add_query processes a query and returns AUTH back to the caller
- release consumes the AUTH token and ensures that both db and db' yield (pointwise) equal results *)
  Lemma rnm_online (j : Z) (num den : Z) (evalQ : val)
    (εpos : 0 < IZR num / IZR den) `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1) K
    :
    (∀ i, wp_sensitive (Val evalQ i) 1 dDB dZ) -∗
    ↯m (IZR num / IZR den) -∗

    ⤇ fill K (report_noisy_max_online #num #den (Val evalQ) (inject db')) -∗
    WP report_noisy_max_online #num #den evalQ (inject db)

      {{ add_release,
           ∃ (add' release' : val) (AUTH : iProp Σ),

             ⤇ fill K (add', release')%V ∗

             AUTH ∗

             (∀ K i,
                 AUTH -∗
                 ⤇ fill K (add' #i) -∗
                 WP (Fst (Val add_release) #i) {{ _, ⤇ fill K #() ∗ AUTH }}) ∗

             (∀ K,
                 AUTH -∗
                 ⤇ fill K (release' #()) -∗
                 WP (Snd (Val add_release) #())
                   {{ v, ∃ v' : val, ⌜ v = #j → v' = #j ⌝ }})
            }}.
  Proof with (tp_pures ; wp_pures).
    (* The privacy proof of RNM hinges on the fact that the credit gets spent when the "winning"
    query gets evaluated, i.e., when the index matches that of the result in the point-wise
    equality.

    For oRNM, the result index in the point-wise equality of the release method can either be
    quantified before or after the initialisation of oRNM. Knowing the index is required to decide
    which coupling to spend the credit on. If the index is quantified in the spec for `release`,
    then `add` cannot know about it, and we don't know how to couple.

    This is why this current spec quantifies over `i : Z` before initialising oRNM. *)

    (* NB: Actually, since we require to know `j` in advance, we could also make the queries on
    `i≠j` free and only require ↯ε on the j-th query. *)

    iIntros "sens ε rhs".
    rewrite /report_noisy_max_online... simpl...
    tp_alloc as maxI2 "maxI2". tp_pures. tp_alloc as maxA2 "maxA2". do 5 tp_pure.
    wp_pures. wp_alloc maxI1 as "maxI1". wp_alloc maxA1 as "maxA1". do 5 wp_pure.
    simpl...
    iExists _,_.
    (* TODO: This is too simple-minded; the availability of ε in AUTH has to depend on whether or
    not `i` has been queried. *)
    iExists (
        maxI2 ↦ₛ #(-1) ∗
        maxA2 ↦ₛ #0 ∗
        maxI1 ↦ #(-1) ∗
        maxA1 ↦ #0 ∗
        ↯m (IZR num / IZR den)
      )%I.
    iFrame.
    clear K.
    iModIntro. iSplitL.
    - iIntros "%K %i (maxI2 & maxA2 & maxI1 & maxA1 & ε) rhs".
      admit.
    - iIntros "%K (maxI2 & maxA2 & maxI1 & maxA1 & ε) rhs".
      admit.
  Abort.

  (* The above-mentioned issue with anticipating when an error-credit gets spent by examining the
  index returned as final result can be exhibited in an example simpler than oRNM.

   This problem can be stated in Eris as follows. Sufficient use of laziness in `get` might solve
   this particular problem. *)

  Goal
    ↯m (1/4)  -∗
    WP
      let: "res" := ref (rand #3) in
      let: "resample" := λ:"_", "res" <- rand #3 in
      let: "get" := λ:"_", !"res" in
      ("resample", "get")
        {{ resample_get ,
             let (resample, get) := ((Fst (Val resample_get))%E, (Snd (Val resample_get))%E) in
             ∃ TOKEN : iProp Σ,
               TOKEN ∗
               (TOKEN -∗ WP resample #() {{ _, TOKEN }}) ∗
               (TOKEN -∗ WP get #() {{ v, ∃ k : Z, ⌜v = #k⌝ ∗ ⌜0 < k⌝%Z }})
        }}.
  Abort.

  (* One can generalize this argument by parametrising `resample` by some function `f` which is
  (i) known to be safe, and (ii) produces the result 1 if given some resource `X`.

    This is now a problem in unary separation logic, although it is not immediate what `X` and `f` should be.
   *)
  Goal
    ∀ (f : val), ∃ (X : iProp Σ),
      (X -∗ WP (Val f) #()  {{ v, ⌜v = #1⌝}}) -∗
      (WP (Val f) #()  {{ _, ⌜True⌝ }}) -∗
      X -∗
      WP
        let: "res" := ref (f #()) in
        let: "resample" := (λ:"_", "res" <- f #()) in
        let: "get" := (λ:"_", !"res") in
        ("resample", "get")
          {{ resample_get ,
               let (resample, get) := ((Fst (Val resample_get))%E, (Snd (Val resample_get))%E) in
               ∃ TOKEN,
                 TOKEN ∗
                 (TOKEN -∗ WP resample #() {{ _, TOKEN }}) ∗
                 (TOKEN -∗ WP get #() {{ v, ∃ k : Z, ⌜v = #k⌝ ∗ ⌜0 < k⌝%Z }})
          }}.
  Abort.

End rnm.
