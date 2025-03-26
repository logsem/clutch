From Coq Require Import Utf8 List ssreflect.
Import ListNotations.

Definition list_double_ind {A B: Type} (l1 : list A) (l2 : list B) 
  (P : list A → list B → Type)
  (IH1 : P [] [])
  (IH2 : ∀ h1 t1, 
    P t1 [] → 
    P (h1::t1) [])
  (IH3 : ∀ h2 t2,
    P [] t2 →
    P [] (h2::t2))
  (IH4 : ∀ h1 t1 h2 t2,
    P t1 t2 → 
    P (h1 :: t1) (h2 :: t2))  
    : P l1 l2.
    Proof.
      elim: l1 l2 => [|h1 t1 IHl1]; elim; auto.
    Qed.