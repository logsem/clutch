From stdpp Require Import namespaces.
From self.prob_lang Require Import lang notation spec_ra proofmode primitive_laws.
From self.logrel Require Import model rel_rules rel_tactics compatibility.
From self.prelude Require Import base.
Set Default Proof Using "Type*".

Section proofs.
  Context `{!prelogrelGS Σ}.

  Definition coinN := nroot.@"coin".

  (* t4 = { true ⟼ 1/4, false ⟼ 3/4 } *)
  Definition t4 :=
    (λ:<>,
      let: "b0" := flip #() in
      let: "b1" := flip #() in
      if: "b1" then "b0" else #false)%V.

  Definition vnc (t : expr) :=
    (rec: "f" <> :=
      let: "x" := t #() in
      let: "y" := t #() in
      if: "x" = "y" then "f" #() else "x")%V.

  Goal ⊢ REL (vnc t4) << (λ:<>, flip #()) : lrel_unit → lrel_bool.
  Proof.
    rewrite /vnc.
    rel_pures_r. rel_pures_l.
    iApply refines_arrow_val.
    iIntros "!#" (??) "#[-> ->]".
    rel_pures_r. rel_pures_l.
    set (vnc4 := vnc t4).
    unfold vnc in vnc4.
    fold vnc4.
    unfold t4. rel_pures_l.
  Abort.

  (* t2 = { true ⟼ 1/2, false ⟼ 1/2 } *)
  Definition t2 := (λ:<>, flip #())%V.

  Goal ⊢ REL (vnc t2) << (λ:<>, flip #()) : lrel_unit → lrel_bool.
  Proof.
    rewrite /vnc.
    rel_pures_r. rel_pures_l.
    iApply refines_arrow_val.
    iIntros "!#" (??) "#[-> ->]".
    rel_pures_r. rel_pures_l.
    set (vnc2 := vnc t2) ; unfold vnc in vnc2 ; fold vnc2.
    unfold t2. rel_pures_l.
  Abort.

  Goal ⊢ REL flip #() = flip #() << flip #() : lrel_bool.
  Abort.

  Goal ⊢ REL if: flip #() then flip #() else flip #() << flip #() : lrel_bool.
