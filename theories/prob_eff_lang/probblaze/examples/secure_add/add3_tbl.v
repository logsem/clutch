From clutch.prob_eff_lang.probblaze Require Import logic proofmode.
From clutch.prob_eff_lang.probblaze.examples.secure_add Require Import add3_def.

(** The network's write-once tables: [v] represents the finite map [M].  A
    key is only ever added when absent, so a table never shadows a key. *)

Inductive is_tbl : val → gmap Z val → Prop :=
| is_tbl_nil : is_tbl NONEV ∅
| is_tbl_cons (k : Z) w v M :
    M !! k = None → is_tbl v M → is_tbl (SOMEV ((#k, w), v)) (<[k := w]> M).

Definition optv (o : option val) : val :=
  match o with Some w => SOMEV w | None => NONEV end.

Lemma is_tbl_add v M (k : Z) w :
  M !! k = None → is_tbl v M → is_tbl (SOMEV ((#k, w), v)) (<[k := w]> M).
Proof. apply is_tbl_cons. Qed.

Section tbl.
  Context `{!probblazeRGS Σ}.

  Lemma brel_tbl_lookup_l E K e2 L R v M (k : Z) :
    is_tbl v M →
    BREL fill K (optv (M !! k)) ≤ e2 @ E <|L|> {{R}} ⊢
    BREL fill K (tbl_lookup v #k) ≤ e2 @ E <|L|> {{R}}.
  Proof.
    intros Htbl. iIntros "H".
    iInduction Htbl as [|k' w v M Hk Htbl] "IH".
    - rewrite /tbl_lookup. brel_pures_l. by rewrite lookup_empty.
    - rewrite {2}/tbl_lookup. brel_pures_l.
      case_bool_decide as Heq; [brel_pures_l|brel_pures_l 1%nat].
      + simplify_eq. by rewrite lookup_insert_eq.
      + rewrite lookup_insert_ne; last by intros ->. by iApply "IH".
  Qed.

  Lemma brel_tbl_lookup_r E K e1 L R v M (k : Z) :
    is_tbl v M →
    BREL e1 ≤ fill K (optv (M !! k)) @ E <|L|> {{R}} ⊢
    BREL e1 ≤ fill K (tbl_lookup v #k) @ E <|L|> {{R}}.
  Proof.
    intros Htbl. iIntros "H".
    iInduction Htbl as [|k' w v M Hk Htbl] "IH".
    - rewrite /tbl_lookup. brel_pures_r. by rewrite lookup_empty.
    - rewrite {2}/tbl_lookup. brel_pures_r.
      case_bool_decide as Heq; [brel_pures_r|brel_pures_r 1%nat].
      + simplify_eq. by rewrite lookup_insert_eq.
      + rewrite lookup_insert_ne; last by intros ->. by iApply "IH".
  Qed.

End tbl.
