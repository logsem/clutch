From clutch.elton Require Import elton hash. 
Set Default Proof Using "Type*".

Section proofs.
  Context `{eltonGS Σ}.
  Variable secret_range:nat.
  Variable val_size: nat.
  Variable bound: nat.

  Definition prog : expr :=
    λ: "A",
      let: "hashf" := init_hash val_size in
      let: "secret" := rand #secret_range in
      let: "h" := "hashf" "secret" in
      let: "i" := ref #bound in
      let: "hashf'" :=
        (λ: "x", if: ! "x" = #0
                 then NONE
                 else "i" <- ! "i" - #1;; SOME ("hashf" "x") ) in
      let: "g" := "A" "hashf'" "h" in
      "hashf" "g" = "h".

  
  Definition prog' : expr :=
    λ: "A",
      let: "hashf" := init_hash val_size in
      let: "secret" := drand #secret_range in
      let: "h" := "hashf" "secret" in
      let: "i" := ref #bound in
      let: "hashf'" :=
        (λ: "x", if: ! "x" = #0
                 then NONE
                 else "i" <- ! "i" - #1;; SOME ("hashf" "x") ) in
      let: "g" := "A" "hashf'" "h" in
      "hashf" "g" = "h".
  
End proofs.

