From clutch.foxtrot Require Import foxtrot.

Definition nodetN : namespace := nroot .@ "nodet".

Definition nodet : val :=
  λ: "_", 
    let: "x" := ref #0 in 
    Fork ((rec: "f" "_" :=
             "x" <- !"x" + #1;;
             "f" #()
          ) #());;
    !"x".
        
Section proof.
Local Set Default Proof Using "Type*".
Context `{!foxtrotGS Σ}.

Lemma wp_nondet:
  {{{ True }}}
    nodet #()
    {{{ (x:nat), RET (#x); True}}}.
Proof.
  rewrite /nodet.
  iIntros (Φ) "_ HΦ".
  wp_pures.
  wp_alloc l as "Hl".
  wp_pures.
  replace 0%Z with (Z.of_nat 0); last lia.
  iMod (inv_alloc nodetN _ (∃ (n:nat), l↦#n)%I with "[$]") as "#?".
  wp_apply (wp_fork).
  - wp_pure.
    iLöb as "IH".
    wp_pures.
    wp_bind (! _)%E.
    iInv nodetN as ">(%&Hl)" "Hclose".
    wp_load.
    iMod ("Hclose" with "[$]") as "_".
    iModIntro.
    wp_pures.
    wp_bind (_<-_)%E.
    iInv nodetN as ">(%&Hl)" "Hclose".
    wp_store.
    replace (Z.of_nat n + 1)%Z with (Z.of_nat (n+1)) by lia.
    iMod ("Hclose" with "[$]") as "_".
    iModIntro.
    do 2 wp_pure.
    iApply "IH".
  - wp_pures.
    iInv nodetN as ">(%&Hl)" "Hclose".
    wp_load.
    iMod ("Hclose" with "[$]") as "_".
    iModIntro.
    by iApply "HΦ".
Qed. 
End proof.

Section proof'.
  Context `{!foxtrotGS Σ}.
  Lemma tp_nodet j K E (n:nat):
    j ⤇ fill K (nodet #()) -∗
    pupd E E
      (j ⤇ fill K #n
      ).
  Proof.
    rewrite /nodet.
    iIntros "Hspec".
    tp_pures j.
    tp_alloc j as l "Hl".
    tp_pures j.
    tp_fork j.
    iIntros (j') "Hspec'".
    tp_pures j.
    tp_pure j'.
    iAssert (pupd E E (j ⤇ fill K ! #l ∗ l ↦ₛ #n ∗j' ⤇ (rec: "f" "_" := #l <- ! #l + #1;; "f" #())%V #() ))%I with "[-]" as ">(?&?&?)"; last (tp_load j; by iFrame).
    iInduction n as [|n] "IH"; first by iFrame.
    iMod ("IH" with "[$][$][$]") as "(Hspec & Hl & Hspec')".
    tp_pures j'.
    tp_load j'.
    tp_pures j'.
    tp_store j'.
    do 2 tp_pure j'.
    replace (n+1)%Z with (Z.of_nat (S n))%Z by lia.
    by iFrame.
  Qed. 
End proof'.
