(** RNM-INSPIRED PROBLEMS (exploratory), ported from
    [clutch.diffpriv.examples.rnm_inspired_problems] to the GENERIC language.

    This file collects three RNM-inspired *problem statements* that motivated the
    design of the report-noisy-max development.  As in the monomorphic original,
    NONE of them is provable as stated (the comments below — preserved verbatim —
    explain precisely WHY: the privacy proof of RNM hinges on knowing, when a
    Laplace draw is taken, whether the corresponding index is the "winning" one,
    and the online / lazy variants destroy exactly that information).  We therefore
    port the program definitions and the goal *statements* faithfully and leave the
    proofs [Abort]ed — matching the original, and contributing NO admits/axioms
    (an [Abort]ed lemma adds nothing to the context, unlike [Admitted]).

    THE PORT (sampling):
      - [Laplace #num #(2*#den) … #()] is the [gen] Laplace surface notation
        (from [clutch.gen_diffpriv.lib.laplace]); it desugars to
        [Sample sample_idx …] with [sample_idx] recovered from the
        [SampleIn laplace_family Sg] instance.
      - the original's uniform/RNG draws [rand #3] (a CANDIDATE / resampling stream
        whose VALUE is privacy-irrelevant for these statements) are re-expressed as
        the [gen] uniform surface notation [Uniform #3 #()] (from
        [clutch.gen_diffpriv.lib.uniform]); the 0-cost shift coupling
        [couple_uniform]/[wp_couple_uniform] is the relevant rule, but since every
        goal here is [Abort]ed (the statements are unprovable), no coupling is
        actually discharged.  No uniform-coupling gap is encountered.

    SIGNATURE THREADING: parametric over any [Sg] containing BOTH [laplace_family]
    and [uniform_family] (cf. [sum_queries] / [privacy_filter] / the [report_noisy_max]
    section it reuses).  [report_noisy_max] is reused from the ported pointwise RNM
    development [report_noisy_max_pointwise]. *)
From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import differential_privacy.
From clutch.gen_diffpriv Require Import adequacy all.
From clutch.gen_diffpriv.lib Require Import laplace uniform.
From clutch.gen_prob_lang Require Import inject families.
From clutch.gen_prob_lang.gwp Require Import list.
From clutch.gen_diffpriv.examples Require Import report_noisy_max_pointwise.
From iris.prelude Require Import options.

(** Keep the family index [sample_idx] folded so the [Laplace]/[Uniform] surface
    notations match the library coupling rules syntactically (cf. the rest of the
    gen examples). *)
#[global] Opaque sample_idx.

Section rnm.
  (** Both families are enabled: [laplace_family] (the noise mechanism, reused via
      [report_noisy_max]) and [uniform_family] (the candidate / RNG stream). *)
  Context {Sg : Sig} `{!SampleIn laplace_family Sg} `{!SampleIn uniform_family Sg}
    `{!diffprivGS Sg Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).

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
          (let: "a" := Laplace "num" (#2 * "den") ("evalQ" "i" "d") #() in
           (if: "i" = #0 `or` ! "maxA" < "a" then
              "maxA" <- "a" ;;
              "maxI" <- "i"
            else #())) in
      let: "release" :=
        λ:"_",
          ! "maxI"
      in ("add_query", "release").

  Definition report_noisy_max_online_lazy (num den : Z) : val :=
    λ: "evalQ" "d",
      let: "queries" := ref list_nil in
      let: "add_query" :=
        λ:"i",
          "queries" <- list_cons "i" !"queries" in
      let: "release" :=
        λ:"_",
          let: "evalQ'" :=
            λ:"i" "d",
              "evalQ" (list_nth "i" !"queries") "d"
          in
          let: "N" := list_length !"queries" in
          report_noisy_max num den "evalQ'" "N" "d"
      in ("add_query", "release").

  (* Unclear how to show that evalQ' is 1-sensitive b/c it doesn't directly use the d provided as input. *)
  Definition report_noisy_max_online_less_lazy (num den : Z) : val :=
    λ:"num" "den" "evalQ" "d",
      let: "query_results" := ref list_nil in
      let: "add_query" :=
        λ:"i",
          "query_results" <- list_cons ("evalQ" "i" "d") !"query_results" in
      let: "release" :=
        λ:"_",
          let: "evalQ'" :=
            λ:"i" "d",
              (list_nth "i" !"query_results")
          in
          let: "N" := list_length !"query_results" in
          report_noisy_max num den "evalQ'" "N" "d"
      in ("add_query", "release").

  (* Given the error credits for one run of RNM, initializing oRNM provides an abstract token AUTH
  that is required to call the add_query and release methods, and...
- add_query processes a query and returns AUTH back to the caller
- release consumes the AUTH token and ensures that both db and db' yield (pointwise) equal results *)
  Lemma rnm_online (j : Z) (num den : Z) (evalQ : val)
    (εpos : 0 < IZR num / IZR den) `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1) K
    :
    (∀ i, ⊢ hoare_sensitive Sg (evalQ (Val i)) 1 dDB dZ) →
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

    iIntros (sens) "ε rhs".
    (* expose the [Val]-head of the [inject db'] spec leaf so the [tp_*] reshape
       tactics see a value (the gen analogue of the original proof's [simpl] — see
       [report_noisy_max_pointwise] for the same seam). *)
    rewrite !inject_expr_Val.
    rewrite /report_noisy_max_online...
    tp_alloc as maxI2 "maxI2". tp_pures. tp_alloc as maxA2 "maxA2". tp_pures.
    wp_pures. wp_alloc maxI1 as "maxI1". wp_alloc maxA1 as "maxA1". wp_pures.
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
      (* Cannot be proved: we do not know, at this [add_query] call, whether [i] is
         the winning index [j], so we cannot decide on which Laplace draw to spend
         the (single) credit.  See the section comment. *)
  Abort.

  (* The above-mentioned issue with anticipating when an error-credit gets spent by examining the
  index returned as final result can be exhibited in an example simpler than oRNM.

   This problem can be stated in Eris as follows. Sufficient use of laziness in `get` might solve
   this particular problem.

   PORT NOTE: the original used [rand #3] (a uniform draw on [{0,1,2,3}]) for the
   resampled value; in [gen] this is the uniform surface notation [Uniform #3 #()]
   (the draw's VALUE is privacy-irrelevant here, so the 0-cost [couple_uniform]
   shift would be the relevant rule — but the goal is unprovable and [Abort]ed). *)

  Goal
    ↯m (1/4)  -∗
    WP
      let: "res" := ref (Uniform #3 #()) in
      let: "resample" := λ:"_", "res" <- Uniform #3 #() in
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
