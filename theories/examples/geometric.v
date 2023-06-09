(* Small demo that Clutch can prove equivalence of recursively defined procedures. *)

From clutch Require Export clutch lib.flip.
Set Default Proof Using "Type*".

Definition geo_true : val := rec: "f" "n" := if: flip then "n" else "f" ("n" + #1).
Definition geo_false : val := rec: "f" "n" := if: flip then "f" ("n" + #1) else "n".

Section logical_ref.
  Context `{!clutchRGS Σ}.

  Lemma true_false :
    ⊢ REL geo_true << geo_false : lrel_int → lrel_int.
  Proof with rel_pures_l ; rel_pures_r.
    auto...
    iLöb as "HH".
    rewrite /geo_true /geo_false.
    rel_arrow_val.
    iIntros (??) "[%n [-> ->]]"...
    rel_apply (refines_couple_flip_flip negb) => /=.
    iIntros "!>" ([]).
    - auto... rel_values.
    - rel_pure_r. rel_pure_l.
      fold geo_true. fold geo_false.
      rel_apply refines_app.
      + iAssumption.
      + auto... rel_values.
  Qed.

  Lemma false_true :
    ⊢ REL geo_false << geo_true : lrel_int → lrel_int.
  Proof with rel_pures_l ; rel_pures_r.
    auto...
    iLöb as "HH".
    rewrite /geo_true /geo_false.
    rel_arrow_val.
    iIntros (??) "[%n [-> ->]]"...
    rel_apply (refines_couple_flip_flip negb) => /=.
    iIntros "!>" ([]).
    - rel_pure_r. rel_pure_l.
      fold geo_true. fold geo_false.
      rel_apply refines_app.
      + iAssumption.
      + auto... rel_values.
    - auto... rel_values.
  Qed.
End logical_ref.
