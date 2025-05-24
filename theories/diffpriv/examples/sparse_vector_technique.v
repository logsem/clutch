From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import adequacy diffpriv proofmode.

Section svt.
  Context `{!diffprivGS Σ}.

  #[local] Open Scope R.

  (* above_threshold ((num/den) : Q) (T : Z) (db : DB) (qᵢ : DB -o Z) : option (DB -o Z)  *)
  (* "give me ↯ε and I'll privately find a query qᵢ above T" *)

  (* in terms of affine / quantitative resources: *)
  (* "give me ↯ε and I'll privately find a query qᵢ above T ONCE" *)
  (* "for ↯ε you get a value that you can use once to privately find a query qᵢ above T" *)


  (* { ↯ ε } A_T T { f . f : (DB -o Z) -> DB -o option Z }  *)
  (* { ↯ ε } A_T T
     { f . AUTH
           ∗ ∀ db qᵢ,
               { AUTH ∗ { ⊤ } qᵢ db { v . T ≤ v } } f db qi { true }
             ∗ { AUTH ∗ { ⊤ } qᵢ db { v . v < T } } f db qi { false ∗ AUTH }
[or this:]
             { AUTH } f db qi { b : bool . if b = false then AUTH }
     }  *)
  Definition above_threshold : val :=
    λ:"num" "den" "T",
      let: "T'" := Laplace "num" (#2*"den") "T" in
      let: "reset" := #false in
      λ:"db",
        let: "f" :=
          (λ: "qi",
             if: ! "reset" then
               NONE
             else
               (let: "vi" := Laplace "num" (#4*"den") ("qi" "db") in
                (if: "T'" ≤ "vi" then
                   "reset" <- #true ;;
                   SOME #true
                 else
                   SOME #false)))
        in "f".

  Definition wp_sensitive (f : expr) (c : R) `(d_in : Distance A) `(d_out : Distance B) : iProp Σ
    :=
    ∀ (c_pos : 0 <= c) K (x x' : A),
    ⤇ fill K (f $ Val $ inject x') -∗
    WP
      f $ Val $ inject x
      {{ v,
           ∃ b b' : B, ⌜v = inject b⌝ ∧ ⤇ fill K (inject b')
                      ∧ ⌜d_out b b' <= c * d_in x x'⌝
      }}.

  (* NB: could postpone introducing db and db' *)
  Lemma above_threshold_online_spec (num den T : Z) (_ : 0 <= IZR num / IZR den) `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1) K :
    ↯ (IZR num / IZR den) -∗
    ⤇ fill K ((Val above_threshold) #num #den #T (Val (inject db')))
    -∗
    WP (Val above_threshold) #num #den #T (Val (inject db))
       {{ f, ∃ f' : val,
             ⤇ fill K (Val f') ∗
             ∃ AUTH : iProp Σ,
               (∀ q, wp_sensitive (Val q) 1 dDB dZ -∗
                     AUTH -∗
                     ⤇ fill K (f' q) -∗
                     WP (Val f) (Val q)
                       {{ v, ⤇ fill K (Val v) ∗
                             ∃ b : bool, ⌜v = #b⌝ ∗
                                         if b then emp else AUTH
                       }}

               )
       }}.
  Proof.
    iIntros "ε rhs". rewrite /above_threshold.
    tp_pures. wp_pures.
  Admitted.

  (* SVT calibrates the noise by simply dividing up the initial budget ε =
  num/den over the number of queries c exceeding the threshold T and running
  each "above_threshold" query with privacy budget ε/c. *)
  (* SVT : ℚ → ℤ → ℕ → DB → (DB → Z) → option 𝔹 *)
  Definition SVT (num den : Z) : val :=
    λ:"T" "c",
      let: "found_above_T" := ref #true in
      let: "T'" := ref "T" in
      let: "count" := ref #0 in
      let: "f" :=
        λ:"db" "qi",
          if: "c" < !"count" then NONEV else
            SOME
              ((if: ! "found_above_T" then
                  (* need to reset T' from T with fresh noise *)
                  "T'" <- Laplace #num ("c" * #(2*den)) "T" else #()) ;;
               let: "vi" := Laplace #num #(4*den) ("qi" "db") in
               if: "T'" ≤ "vi" then
                 "found_above_T" <- #true ;;
                 "count" <- !"count"+#1 ;;
                 #true
               else
                 #false)
      in "f".

  (* SVT expressed in terms of Above Threshold, for modular analysis. *)
  (* NB: This is different from bounded oracles ("q_calls" in Approxis) because
     we only count calls to above_threshold that return a #true result. *)
  Definition SVT_AT (num den : Z) : val :=
    λ:"T" "c",
      let: "count" := ref #0 in
      let: "AT" := ref (above_threshold #num ("c" * #den) "T" "db") in
      λ:"db" "qi",
        if: "c" < !"count" then NONE else
          match: !"AT" "db" "qi" with
          | SOME "v" =>
              (if: "v" then
                 ("AT" <- (above_threshold #num ("c" * #den) "T" "db") ;;
                  "count" <- !"count" + #1)
               else #()) ;;
              SOME "v"
          | NONE => NONE (* should never happen because we always reset AT diligently *)
          end.

  (* In Justin's thesis, the discussion of choice couplings (p.70) and
  especially of randomized privacy cost (p.71) is relevant ; it suggests that
  the point-wise equality proof may not be required for SVT. *)
