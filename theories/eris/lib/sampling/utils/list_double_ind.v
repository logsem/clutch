From Coq Require Import Utf8 List Lia Program.
Import ListNotations.


Program Fixpoint list_double_ind {A B: Type} (l1 : list A) (l2 : list B) (P : list A -> list B -> Type) 
    (IH1 : P [] [])
    (IH2 : ∀ h1 t1, 
      P t1 [] -> 
      P (h1::t1) [])
    (IH3 : ∀ h2 t2, 
      P [] t2 -> 
      P [] (h2::t2))
    (IH4 : ∀ h1 t1 h2 t2, P t1 t2 -> P (h1 :: t1) (h2 :: t2)) {measure (length l1 + length l2)} : P l1 l2 :=
  match l1, l2 with 
  | [], [] => IH1
  | h1::t1, [] => IH2 h1 t1 (list_double_ind t1 [] P IH1 IH2 IH3 IH4)
  | [], h2::t2 => IH3 h2 t2 (list_double_ind [] t2 P IH1 IH2 IH3 IH4)
  | h1::t1, h2::t2 => IH4 h1 t1 h2 t2 (list_double_ind t1 t2 P IH1 IH2 IH3 IH4)
  end.
  Next Obligation.
    simpl; lia.
  Qed.
