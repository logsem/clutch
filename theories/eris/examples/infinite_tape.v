From clutch.eris Require Export adequacy.
From clutch.eris Require Export eris error_rules receipt_rules.

Set Default Proof Using "Type*".

Section infinite_tape.

  Context `{!erisGS Σ}.

  Definition infinite_tape α (f: nat → (fin 2)) : iProp Σ :=
    ∃ k ns, α ↪ (1; ns) ∗ steps_left k ∗ ⌜ k < length ns ⌝ ∗ ⌜ ∀ i b, ns !! i = Some b → f i = b ⌝.

End infinite_tape.
