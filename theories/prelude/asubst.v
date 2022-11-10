(** Autosubst helper lemmata *)
From Autosubst Require Export Autosubst.
From iris.prelude Require Export prelude.

Section Autosubst_Lemmas.
  Context {term : Type} {Ids_term : Ids term}
          {Rename_term : Rename term} {Subst_term : Subst term}
          {SubstLemmas_term : SubstLemmas term}.

  Lemma iter_up (m x : nat) (f : var → term) :
    upn m f x = if decide (x < m) then ids x else rename (+m) (f (x - m)).
  Proof.
    revert x; induction m as [|m IH]=> -[|x];
      repeat (case_match || asimpl || rewrite IH); auto with lia.
  Qed.
End Autosubst_Lemmas.
