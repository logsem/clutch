From iris.prelude Require Import options.
From clutch.foxtrot Require Import foxtrot spawn.

Definition parN : namespace := nroot .@ "par".

Definition par : val :=
  λ: "e1" "e2",
    let: "handle" := spawn "e1" in
    let: "v2" := "e2" #() in
    let: "v1" := join "handle" in
    ("v1", "v2").
Notation "e1 ||| e2" := (par (λ: <>, e1)%E (λ: <>, e2)%E) : expr_scope.
Notation "e1 ||| e2" := (par (λ: <>, e1)%V (λ: <>, e2)%V) : val_scope.

Section proof.
Local Set Default Proof Using "Type*".
Context `{!foxtrotGS Σ, !spawnG Σ}.

(* Notice that this allows us to strip a later *after* the two Ψ have been
   brought together.  That is strictly stronger than first stripping a later
   and then merging them, as demonstrated by [tests/joining_existentials.v].
   This is why these are not Texan triples. *)
Lemma par_spec (Ψ1 Ψ2 : val → iProp Σ) (f1 f2 : val) (Φ : val → iProp Σ) :
  WP f1 #() {{ Ψ1 }} -∗ WP f2 #() {{ Ψ2 }} -∗
  (▷ ∀ v1 v2, Ψ1 v1 ∗ Ψ2 v2 -∗ ▷ Φ (v1,v2)%V) -∗
  WP par f1 f2 {{ Φ }}.
Proof.
  iIntros "Hf1 Hf2 HΦ". wp_lam. wp_let.
  wp_apply (spawn_spec parN with "Hf1"). iIntros (l) "Hl".
  wp_let. wp_bind (f2 _).
  wp_apply (wp_wand with "Hf2") as (v) "H2". wp_let.
  wp_apply (join_spec with "[$Hl]") as (w) "H1".
  iSpecialize ("HΦ" with "[$H1 $H2]"). by wp_pures.
Qed.

Lemma wp_par (Ψ1 Ψ2 : val → iProp Σ) (e1 e2 : expr) (Φ : val → iProp Σ) :
  WP e1 {{ Ψ1 }} -∗ WP e2 {{ Ψ2 }} -∗
  (∀ v1 v2, Ψ1 v1 ∗ Ψ2 v2 -∗ ▷ Φ (v1,v2)%V) -∗
  WP (e1 ||| e2)%V {{ Φ }}.
Proof.
  iIntros "H1 H2 H".
  wp_apply (par_spec Ψ1 Ψ2 with "[H1] [H2] [H]"); [by wp_lam..|auto].
Qed.
End proof.

Section proof'.
  Context `{!foxtrotGS Σ}.
  Lemma tp_par j K e1 e2 E:
    j ⤇ fill K (e1 ||| e2) -∗
    pupd E E
      (∃ j1 j2 K1 K2, j1 ⤇ fill K1 e1 ∗ j2 ⤇ fill K2 e2 ∗
                   (∀ (v1 v2 : val) E', j1 ⤇ fill K1 v1 ∗ j2 ⤇ fill K2 v2 -∗
                                        pupd E' E' (j ⤇ fill K (v1, v2)%V)
                   )
      ).
  Proof.
    rewrite /par.
    iIntros "Hspec".
    rewrite /spawn.
    tp_pures j.
    tp_alloc j as l "Hl".
    tp_pures j.
    tp_fork j.
    iIntros (j') "Hspec'".
    tp_pures j'.
    tp_pures j.
    tp_bind j (e2).
    tp_bind j' e1.
    iFrame.
    iModIntro.
    iIntros (???) "[??]".
    simpl.
    tp_pures j.
    tp_pures j'.
    tp_store j'.
    rewrite /join.
    tp_pures j.
    tp_load j.
    tp_pures j.
    by iFrame.
  Qed.  
End proof'.
