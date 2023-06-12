(* We establish a refinement of two implementations of a coin with two methods
   "update" and "read". The first time "read" is called, it returns a random
   boolean, on successive calls the result will be fixed.

   The "eager" implementation samples a new bit every time "update" is called,
   and fixes the last sampled bit on the first call to "read".

   The "lazy" implementation instead does nothing on "update", and samples only
   once "read" is called.

   The interest of this example is that the update procedure may be called many
   times, and thus eager may sample more bits than lazy. At first glance, it
   may thus seem difficult to choose which two flips to couple.

   We solve the issue by proving an intermediate refinement "lazy_alt". This
   variant of "lazy" performs a flip in "update", but discards the result. It
   thus behaves like "lazy", but still allows us to keep the tapes "α" (from
   "lazy_alt") and "β" (from eager) synchronised.
 *)

From clutch Require Export clutch lib.flip.
Set Default Proof Using "Type*".

Section proofs.
  Context `{!clutchRGS Σ}.

  Definition onceN := nroot.@"once".

  Let read_lazy lbl : expr :=
        λ:<>,
            ((if: !"f" then
                (let: "x" := flipL lbl in
                 "r" <- "x" ;;
                 "f" <- #false)
              else #()) ;;
             ! "r").

  Definition lazy : expr :=
    let: "r" := ref #false in
    let: "f" := ref #true in
    let: "update" := λ:<>, #() in
    let: "read" := read_lazy #() in
    ("update", "read").

  Definition lazy_alt : expr :=
    let: "α" := allocB in
    let: "r" := ref (flipL "α") in
    let: "f" := ref #true in
    let: "update" := λ:<>, (flipL "α") ;; #() in
    let: "read" := read_lazy "α" in
    ("update", "read").

  Definition eager : expr :=
    let: "β" := allocB in
    let: "r" := ref (flipL "β") in
    let: "f" := ref #true in
    let: "update" :=
      λ:<>,
        if: !"f" then
          let: "x" := flipL "β" in
          "r" <- "x"
        else #() in
    let: "read" :=
      λ:<>,
        ("f" <- #false ;;
         !"r")
    in ("update", "read").

  Lemma lazy_alt_eager :
    ⊢ REL lazy_alt << eager
      : (() → ()) * (() → lrel_bool).
  Proof with try rel_pures_l ; try rel_pures_r.
    unfold lazy_alt, eager.
    rel_allocBtape_l α as "α"...
    rel_allocBtape_r β as "β"...
    rel_apply_l refines_flipL_empty_l => // ; iFrame ; iIntros "%b' α"...    
    rel_apply_r refines_couple_bool_tape_tape => // ; iFrame.
    iIntros (b) "[β α]" => /=...
    rel_flipL_r...
    rel_alloc_l x as "x"...
    rel_alloc_r y as "y"...
    rel_alloc_l f as "f".
    rel_alloc_r g as "g".
    set (P2 := ((∃ (bx b:bool), ∃ bs, x ↦ #bx ∗ y ↦ₛ #b ∗ α ↪B (b :: bs) ∗ β ↪ₛB bs ∗ f ↦ #true ∗ g ↦ₛ #true))%I).
    set (P3 := ((∃ b:bool, ∃ bs, ∃ bs', x ↦ #b ∗ y ↦ₛ #b ∗ α ↪B bs ∗ β ↪ₛB bs' ∗ f ↦ #false ∗ g ↦ₛ #false))%I).
    iApply (refines_na_alloc (P2 ∨ P3) onceN).
    iSplitL ; [ iLeft ; iExists _,_,_ ; iFrame |].
    iIntros "#Hinv". clear.
    do 8 rel_pure_l.
    do 8 rel_pure_r.
    iApply refines_pair.
    - iApply refines_arrow_val.
      iIntros "!#" (f1 f2) "#Hf".
      iApply (refines_na_inv with "[-$Hinv]"); [done|].
      iIntros "(>[ (%bx & %b & %bs & x & y & α & β & f & g)
                 | (%b & %bs & %bs' & x & y & α & β & f & g) ] & Hclose)"...
      + rel_load_r...
        iApply refines_couple_bool_tape_tape => // ; iFrame ; iIntros (b') "(β & α)" => /=.
        destruct bs.
        * rel_flipL_l. rel_flipL_r... rel_store_r.
          #[local] Tactic Notation "close_inv" :=
            iApply (refines_na_close with "[-$Hclose]") ; iSplitL ;
            [iNext ; (iLeft ; iExists _,_,_ ; by iFrame)
                     || (iRight ; iExists _,_,_ ; by iFrame)|].
          close_inv.
          rel_values.
        * rel_flipL_l. rel_flipL_r... rel_store_r.
          close_inv.
          rel_values.
      + rel_load_r...
        destruct bs.
        * rel_apply_l refines_flipL_empty_l => // ; iFrame ; iIntros "%b' α"...
          close_inv ; rel_values.
        * rel_flipL_l...
          close_inv ; rel_values.
    - iApply refines_arrow_val.
      iIntros "!#" (f1 f2) "#Hf".
      iApply (refines_na_inv with "[-$Hinv]"); [done|].
      iIntros "(>[ (%bx & %b & %bs & x & y & α & β & f & g)
                 | (%b & %bs & %bs' & x & y & α & β & f & g) ] & Hclose)"...
      + rel_store_r ; rel_load_l... rel_load_r.
        rel_flipL_l.
        do 2 rel_store_l...
        rel_load_l.
        close_inv ; rel_values.
      + rel_store_r ; rel_load_l... rel_load_r.
        rel_load_l.
        close_inv ; rel_values.
  Qed.

  Lemma lazy_lazy_alt :
    ⊢ REL lazy << lazy_alt
    : (() → ()) * (() → lrel_bool).
  Proof with try rel_pures_l ; try rel_pures_r.
    unfold lazy_alt, lazy.
    rel_alloctape_r β as "β"...
    rel_apply_r refines_flipL_empty_r => // ; iFrame ; iIntros "%b' β"...
    rel_alloc_l x as "x"...
    rel_alloc_r y as "y"...
    rel_alloc_l f as "f".
    rel_alloc_r g as "g".
    set (P2 := ((∃ (bx b:bool), x ↦ #bx ∗ y ↦ₛ #b ∗ β ↪ₛB [] ∗ f ↦ #true ∗ g ↦ₛ #true))%I).
    set (P3 := ((∃ b:bool, x ↦ #b ∗ y ↦ₛ #b ∗ β ↪ₛB [] ∗ f ↦ #false ∗ g ↦ₛ #false))%I).
    iApply (refines_na_alloc (P2 ∨ P3) onceN).
    iSplitL ; [ iLeft ; iExists _,_ ; iFrame |].
    iIntros "#Hinv". clear.
    do 8 rel_pure_l.
    do 8 rel_pure_r.
    iApply refines_pair.
    - iApply refines_arrow_val.
      iIntros "!#" (f1 f2) "#Hf".
      iApply (refines_na_inv with "[-$Hinv]"); [done|].
      iIntros "(>[ (%bx & %b & x & y & β & f & g)
                 | (%b & x & y & β & f & g) ] & Hclose)".
      #[local] Tactic Notation "close_inv" :=
        iApply (refines_na_close with "[-$Hclose]") ; iSplitL ;
        [iNext ; (iLeft ; iExists _,_ ; by iFrame)
                 || (iRight ; iExists _ ; by iFrame)|].
      + rel_pures_r.
        rel_apply_r refines_flipL_empty_r => // ; iFrame ; iIntros "%b' β"...
        close_inv ; rel_values.
      + rel_pures_r.
        rel_apply_r refines_flipL_empty_r => // ; iFrame ; iIntros "%b' β"...
        close_inv ; rel_values.
    - iApply refines_arrow_val.
      iIntros "!#" (f1 f2) "#Hf".
      iApply (refines_na_inv with "[-$Hinv]"); [done|].
      iIntros "(>[ (%bx & %b & x & y & β & f & g)
                 | (%b & x & y & β & f & g) ] & Hclose)"...
      + rel_load_l. rel_load_r...
        rel_apply_l refines_couple_flip_tape ; iFrame ; iIntros "!>" (b') "β" => /=...
        rel_flipL_r.
        do 2 rel_store_l... rel_load_l.
        do 2 rel_store_r ; rel_load_r.
        close_inv ; rel_values.
      + rel_load_l... rel_load_r...
        rel_load_l ; rel_load_r.
        close_inv ; rel_values.
  Qed.

End proofs.
