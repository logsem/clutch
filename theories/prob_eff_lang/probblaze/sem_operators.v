(* sem_operators.v *)

From clutch.prob_eff_lang.probblaze Require Import syntax.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types.

Open Scope sem_ty_scope.

Inductive typed_un_op {Σ} : un_op → sem_ty Σ → sem_ty Σ → Prop :=  
  | typed_un_op_neg : typed_un_op NegOp 𝔹 𝔹
  | typed_un_op_minus : typed_un_op MinusUnOp ℤ ℤ
.

Inductive typed_bin_op {Σ}: bin_op → sem_ty Σ → sem_ty Σ → sem_ty Σ → Prop :=  
  | typed_bin_op_plus : typed_bin_op PlusOp ℤ ℤ ℤ
  | typed_bin_op_minus : typed_bin_op MinusOp ℤ ℤ ℤ
  | typed_bin_op_mult : typed_bin_op MultOp ℤ ℤ ℤ
  | typed_bin_op_quot : typed_bin_op QuotOp ℤ ℤ ℤ
  | typed_bin_op_rem : typed_bin_op RemOp ℤ ℤ ℤ
  | typed_bin_op_and : typed_bin_op AndOp 𝔹 𝔹 𝔹
  | typed_bin_op_or : typed_bin_op OrOp 𝔹 𝔹 𝔹
  | typed_bin_op_xor : typed_bin_op XorOp 𝔹 𝔹 𝔹
  | typed_bin_op_shiftl : typed_bin_op ShiftLOp ℤ ℤ ℤ
  | typed_bin_op_shiftr : typed_bin_op ShiftROp ℤ ℤ ℤ
  | typed_bin_op_le : typed_bin_op LeOp ℤ ℤ 𝔹
  | typed_bin_op_lt : typed_bin_op LtOp ℤ ℤ 𝔹
  | typed_bin_op_Eq : typed_bin_op EqOp ℤ ℤ 𝔹
.
