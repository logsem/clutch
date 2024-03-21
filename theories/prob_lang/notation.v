From clutch.prob_lang Require Import locations.
From clutch.prob_lang Require Export lang.
From iris.prelude Require Import options.

(** Coercions to make programs easier to type. *)
Coercion LitInt : Z >-> base_lit.
Coercion LitBool : bool >-> base_lit.
Coercion LitLoc : loc >-> base_lit.

Coercion App : expr >-> Funclass.

Coercion Val : val >-> expr.
Coercion Var : string >-> expr.

(** Define some derived forms. *)
Notation Lam x e := (Rec BAnon x e) (only parsing).
Notation Let x e1 e2 := (App (Lam x e2) e1) (only parsing).
Notation Seq e1 e2 := (Let BAnon e1 e2) (only parsing).
Notation LamV x e := (RecV BAnon x e) (only parsing).
Notation LetCtx x e2 := (AppRCtx (LamV x e2)) (only parsing).
Notation SeqCtx e2 := (LetCtx BAnon e2) (only parsing).
Notation Alloc e := (AllocN (Val $ LitV $ LitInt 1) e) (only parsing).
Notation Match e0 x1 e1 x2 e2 := (Case e0 (Lam x1 e1) (Lam x2 e2)) (only parsing).

(* Skip should be atomic, we sometimes open invariants around
   it. Hence, we need to explicitly use LamV instead of e.g., Seq. *)
Notation Skip := (App (Val $ LamV BAnon (Val $ LitV LitUnit)) (Val $ LitV LitUnit)).

(* No scope for the values, does not conflict and scope is often not inferred
properly. *)
Notation "# l" := (LitV l%Z%V%stdpp) (at level 8, format "# l").

(** Syntax inspired by Coq/Ocaml. Constructions with higher precedence come
    first. *)
Notation "( e1 , e2 , .. , en )" := (Pair .. (Pair e1 e2) .. en) : expr_scope.
Notation "( e1 , e2 , .. , en )" := (PairV .. (PairV e1 e2) .. en) : val_scope.

(* We implement a destructing let bind (x₁,…,xₙ) for tuples by storing the
   value v that e1 computes in xₙ, bind (fst xₙ) to xₙ₋₁ to hold x₁…xₙ₋₁, bind
   xₙ to the last component of v, so on. Since xₙ is bound in e2, we have no
   risk of shadowing other uses of x₁. *)
(* I failed to convince Coq that this pattern is recursive, so here's the
   unrolled version for a pairs and triples. *)
Notation "'let,' ( x1 , x2 ) := e1 'in' e2" :=
  (Lam x2%E (Lam x1%E (Lam x2%E e2%E (Snd x2)) (Fst x2)) e1%E)
  (at level 100, x1, x2 at level 1, e1, e2 at level 200) : expr_scope.

(* Notation "'let,' ( x1 , x2 , x3 ) := e1 'in' e2" := *)
(*   (Lam x3%E (Lam x2%E (Lam x3%E (Lam x1%E (Lam x2%E e2%E (Snd x2)) (Fst x2)) (Snd x3)) (Fst x3)) e1%E) *)
(*   (at level 100, x1, x2, x3 at level 1, e1, e2 at level 200) : expr_scope. *)

(* Notation "'let,' ( x1 , ( x2 , x3 ) ) := e1 'in' e2" := *)
(*   (Lam x1%E (Lam x2%E (Lam x1%E (Lam x3%E (Lam x2%E e2%E (Fst x2)) (Snd x2)) (Fst x1)) (Snd x1)) e1%E) *)
(*   (at level 100, x1, x2, x3 at level 1, e1, e2 at level 200) : expr_scope. *)

(* This version doesn't have as uniform of a recursion as described above, but
   it is more concise, since it only uses one of the pattern variables as
   temporary variable from which the others are projected. *)
Notation "'let,' ( x1 , x2 , x3 ) := e1 'in' e2" :=
  ((Lam x1%E (Lam x2 (Lam x3 (Lam x1%E e2 (Fst (Fst x1))) (Snd x1)) (Snd (Fst x1)))) e1%E)
  (at level 100, x1, x2, x3 at level 1, e1, e2 at level 200) : expr_scope.

Notation "'let,' ( x1 , ( x2 , x3 ) ) := e1 'in' e2" :=
  ((Lam x1%E (Lam x2 (Lam x3 (Lam x1%E e2 (Fst x1)) (Snd (Snd x1))) (Fst (Snd x1)))) e1%E)
    (at level 100, x1, x2, x3 at level 1, e1, e2 at level 200) : expr_scope.

Notation "'let,' ( x1 , x2 , x3 , x4 ) := e1 'in' e2" :=
  ((Lam x1%E (Lam x2 (Lam x3 (Lam x4 (Lam x1%E e2 (Fst (Fst (Fst x1)))) (Snd x1)) (Snd (Fst x1))) (Snd (Fst (Fst x1))))) e1%E)
    (at level 100, x1, x2, x3, x4 at level 1, e1, e2 at level 200) : expr_scope.

Notation "'let,' ( x1 , x2 , x3 , x4 , x5 ) := e1 'in' e2" :=
  ((Lam x1%E (Lam x2 (Lam x3 (Lam x4 (Lam x5 (Lam x1%E e2 (Fst (Fst (Fst (Fst x1))))) (Snd x1)) (Snd (Fst x1))) (Snd (Fst (Fst x1))))
      (Snd (Fst (Fst (Fst x1)))))) e1%E)
  (at level 100, x1, x2, x3, x4, x5 at level 1, e1, e2 at level 200) : expr_scope.

(*
Using the '[hv' ']' printing box, we make sure that when the notation for match
does not fit on a single line, line breaks will be inserted for *each* breaking
point '/'. Note that after each breaking point /, one can put n spaces (for
example '/  '). That way, when the breaking point is turned into a line break,
indentation of n spaces will appear after the line break. As such, when the
match does not fit on one line, it will print it like:

  match: e0 with
    InjL x1 => e1
  | InjR x2 => e2
  end

Moreover, if the branches do not fit on a single line, it will be printed as:

  match: e0 with
    InjL x1 =>
    lots of stuff bla bla bla bla bla bla bla bla
  | InjR x2 =>
    even more stuff bla bla bla bla bla bla bla bla
  end
*)
Notation "'match:' e0 'with' | 'InjL' x1 => e1 | 'InjR' x2 => e2 'end'" :=
  (Match e0 x1%binder e1 x2%binder e2)
  (e0, x1, e1, x2, e2 at level 200,
   format "'[hv' 'match:'  e0  'with'  '/  ' '[' | 'InjL'  x1  =>  '/  ' e1 ']'  '/' '[' |  'InjR'  x2  =>  '/  ' e2 ']'  '/' 'end' ']'") : expr_scope.
Notation "'match:' e0 'with' | 'InjR' x1 => e1 | 'InjL' x2 => e2 'end'" :=
  (Match e0 x2%binder e2 x1%binder e1)
  (e0, x1, e1, x2, e2 at level 200, only parsing) : expr_scope.
Notation "'match:' e0 'with' 'InjL' x1 => e1 | 'InjR' x2 => e2 'end'" :=
  (Match e0 x1%binder e1 x2%binder e2)
  (e0, x1, e1, x2, e2 at level 200,
   format "'[hv' 'match:'  e0  'with'  '/  ' '[' 'InjL'  x1  =>  '/  ' e1 ']'  '/' '[' |  'InjR'  x2  =>  '/  ' e2 ']'  '/' 'end' ']'") : expr_scope.
Notation "'match:' e0 'with' 'InjR' x1 => e1 | 'InjL' x2 => e2 'end'" :=
  (Match e0 x2%binder e2 x1%binder e1)
  (e0, x1, e1, x2, e2 at level 200, only parsing) : expr_scope.

Notation "()" := LitUnit : val_scope.
Notation "! e" := (Load e%E) (at level 9, right associativity) : expr_scope.
Notation "'ref' e" := (Alloc e%E) (at level 10) : expr_scope.
Notation "- e" := (UnOp MinusUnOp e%E) : expr_scope.

Notation alloc := AllocTape.

Notation "'rand(' α ) e" := (Rand e%E α%E) (at level 70, right associativity, format "'rand(' α )  e") : expr_scope.
Notation "'rand' e" := (Rand e%E (Val $ LitV LitUnit)) (at level 70) : expr_scope.

Notation "'#lbl:' α" := (# (LitLbl α)) (at level 8, format "#lbl: α").

Notation tick := Tick. 
  
Notation "e1 + e2" := (BinOp PlusOp e1%E e2%E) : expr_scope.
Notation "e1 +ₗ e2" := (BinOp OffsetOp e1%E e2%E) : expr_scope.
Notation "e1 - e2" := (BinOp MinusOp e1%E e2%E) : expr_scope.
Notation "e1 * e2" := (BinOp MultOp e1%E e2%E) : expr_scope.
Notation "e1 `quot` e2" := (BinOp QuotOp e1%E e2%E) : expr_scope.
Notation "e1 `rem` e2" := (BinOp RemOp e1%E e2%E) : expr_scope.
Notation "e1 ≪ e2" := (BinOp ShiftLOp e1%E e2%E) : expr_scope.
Notation "e1 ≫ e2" := (BinOp ShiftROp e1%E e2%E) : expr_scope.

Notation "e1 ≤ e2" := (BinOp LeOp e1%E e2%E) : expr_scope.
Notation "e1 < e2" := (BinOp LtOp e1%E e2%E) : expr_scope.
Notation "e1 = e2" := (BinOp EqOp e1%E e2%E) : expr_scope.
Notation "e1 ≠ e2" := (UnOp NegOp (BinOp EqOp e1%E e2%E)) : expr_scope.

Notation "~ e" := (UnOp NegOp e%E) (at level 75, right associativity) : expr_scope.
(* The unicode ← is already part of the notation "_ ← _; _" for bind. *)
Notation "e1 <- e2" := (Store e1%E e2%E) (at level 80) : expr_scope.

(* The breaking point '/  ' makes sure that the body of the rec is indented
by two spaces in case the whole rec does not fit on a single line. *)
Notation "'rec:' f x := e" := (Rec f%binder x%binder e%E)
  (at level 200, f at level 1, x at level 1, e at level 200,
   format "'[' 'rec:'  f  x  :=  '/  ' e ']'") : expr_scope.
Notation "'rec:' f x := e" := (RecV f%binder x%binder e%E)
  (at level 200, f at level 1, x at level 1, e at level 200,
   format "'[' 'rec:'  f  x  :=  '/  ' e ']'") : val_scope.
Notation "'if:' e1 'then' e2 'else' e3" := (If e1%E e2%E e3%E)
  (at level 200, e1, e2, e3 at level 200) : expr_scope.

(** Derived notions, in order of declaration. The notations for let and seq
are stated explicitly instead of relying on the Notations Let and Seq as
defined above. This is needed because App is now a coercion, and these
notations are otherwise not pretty printed back accordingly. *)
Notation "'rec:' f x y .. z := e" := (Rec f%binder x%binder (Lam y%binder .. (Lam z%binder e%E) ..))
  (at level 200, f, x, y, z at level 1, e at level 200,
   format "'[' 'rec:'  f  x  y  ..  z  :=  '/  ' e ']'") : expr_scope.
Notation "'rec:' f x y .. z := e" := (RecV f%binder x%binder (Lam y%binder .. (Lam z%binder e%E) ..))
  (at level 200, f, x, y, z at level 1, e at level 200,
   format "'[' 'rec:'  f  x  y  ..  z  :=  '/  ' e ']'") : val_scope.

(* The breaking point '/  ' makes sure that the body of the λ: is indented
by two spaces in case the whole λ: does not fit on a single line. *)
Notation "λ: x , e" := (Lam x%binder e%E)
  (at level 200, x at level 1, e at level 200,
   format "'[' 'λ:'  x ,  '/  ' e ']'") : expr_scope.
Notation "λ: x y .. z , e" := (Lam x%binder (Lam y%binder .. (Lam z%binder e%E) ..))
  (at level 200, x, y, z at level 1, e at level 200,
   format "'[' 'λ:'  x  y  ..  z ,  '/  ' e ']'") : expr_scope.

Notation "λ: x , e" := (LamV x%binder e%E)
  (at level 200, x at level 1, e at level 200,
   format "'[' 'λ:'  x ,  '/  ' e ']'") : val_scope.
Notation "λ: x y .. z , e" := (LamV x%binder (Lam y%binder .. (Lam z%binder e%E) .. ))
  (at level 200, x, y, z at level 1, e at level 200,
   format "'[' 'λ:'  x  y  ..  z ,  '/  ' e ']'") : val_scope.

Notation "'let:' x := e1 'in' e2" := (Lam x%binder e2%E e1%E)
  (at level 200, x at level 1, e1, e2 at level 200,
   format "'[' 'let:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.
Notation "e1 ;; e2" := (Lam BAnon e2%E e1%E)
  (at level 100, e2 at level 200,
   format "'[' '[hv' '[' e1 ']' ;;  ']' '/' e2 ']'") : expr_scope.

(* Shortcircuit Boolean connectives *)
Notation "e1 && e2" :=
  (If e1%E e2%E (LitV (LitBool false))) (only parsing) : expr_scope.
Notation "e1 || e2" :=
  (If e1%E (LitV (LitBool true)) e2%E) (only parsing) : expr_scope.

(** Notations for option *)
Notation NONE := (InjL (LitV LitUnit)) (only parsing).
Notation NONEV := (InjLV (LitV LitUnit)) (only parsing).
Notation SOME x := (InjR x) (only parsing).
Notation SOMEV x := (InjRV x) (only parsing).

Notation "'match:' e0 'with' | 'NONE' => e1 | 'SOME' x => e2 'end'" :=
  (Match e0 BAnon e1 x%binder e2)
  (e0, e1, x, e2 at level 200, only parsing) : expr_scope.
Notation "'match:' e0 'with' | 'SOME' x => e2 | 'NONE' => e1 'end'" :=
  (Match e0 BAnon e1 x%binder e2)
  (e0, e1, x, e2 at level 200, only parsing) : expr_scope.

Notation "'match:' e0 'with' 'NONE' => e1 | 'SOME' x => e2 'end'" :=
  (Match e0 BAnon e1 x%binder e2)
  (e0, e1, x, e2 at level 200, only parsing) : expr_scope.
Notation "'match:' e0 'with' 'SOME' x => e2 | 'NONE' => e1 'end'" :=
  (Match e0 BAnon e1 x%binder e2)
  (e0, e1, x, e2 at level 200, only parsing) : expr_scope.

(** Notations for the option monad *)
Notation "'let:m' x := e1 'in' e2" :=
  (match: e1%E with NONE => NONE | SOME x => e2%E end)%E
  (at level 100, x at level 1, e1, e2 at level 200) : expr_scope.

(* `assert e1 ;;; e2` errors out if e1 evaluates to false. *)
Notation "'assert' e1 ;;; e2" := (if: e1%E then SOME e2%E else NONE)%E
  (at level 200, e1, e2 at level 200) : expr_scope.

Notation "'while' e1 'do' e2 'end'" :=
  ((rec: "loop" <> := (if: e1 then e2 ;; "loop" #() else #())) #())%E
  (e1, e2 at level 200) : expr_scope.

(* Shortcut for recursive definitions *)
Notation "'letrec:' f x := e1 'in' e2" :=
  (Lam f%binder e2%E (Rec f%binder x%binder e1%E))
  (at level 200, f at level 1, x at level 1, e1, e2 at level 200,
   format "'[' 'letrec:'  f  x  :=  '/  ' '[' e1 ']'  'in'  '/' e2 ']'")
  : expr_scope.

Notation "'letrec:' f x y .. z := e1 'in' e2" :=
  (Lam f%binder e2%E
     (Rec f%binder x%binder (Lam y%binder .. (Lam z%binder e1%E) ..)))
  (at level 200, f at level 1, x,y,z at level 1, e1, e2 at level 200,
   format "'[' 'letrec:'  f  x y .. z :=  '/  ' '[' e1 ']'  'in'  '/' e2 ']'")
  : expr_scope.
