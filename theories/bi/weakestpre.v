(** Shared notation file for WP connectives. *)

From stdpp Require Export coPset.
From iris.bi Require Import interface derived_connectives.
From iris.prelude Require Import options.

Declare Scope expr_scope.
Delimit Scope expr_scope with E.

Declare Scope val_scope.
Delimit Scope val_scope with V.

Class Wp (PROP EXPR VAL A : Type) := {
  wp : A → coPset → EXPR → (VAL → PROP) → PROP;
  wp_default : A
}.

Global Arguments wp {_ _ _ _ _} _ _ _%E _%I.
Global Instance: Params (@wp) 9 := {}.
Global Arguments wp_default : simpl never.

Class Twp (PROP EXPR VAL A : Type) := {
    twp : A → coPset → EXPR → (VAL → PROP) → PROP;
    twp_default : A
    }.
Global Arguments twp {_ _ _ _ _} _ _ _%E _%I.
Global Instance: Params (@twp) 9 := {}.
Global Arguments twp_default : simpl never.


(** Notations for partial weakest preconditions *)
(** Notations without binder -- only parsing because they overlap with the
notations with binder. *)
Notation "'WP' e @ s ; E {{ Φ } }" := (wp s E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e @ E {{ Φ } }" := (wp wp_default E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e {{ Φ } }" := (wp wp_default ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.

(** Notations with binder. *)
(** The general approach we use for all these complex notations: an outer '[hv'
to switch bwteen "horizontal mode" where it all fits on one line, and "vertical
mode" where each '/' becomes a line break. Then, as appropriate, nested boxes
('['...']') for things like preconditions and postconditions such that they are
maximally horizontal and suitably indented inside the parentheses that surround
them. *)
Notation "'WP' e @ s ; E {{ v , Q } }" := (wp s E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ E {{ v , Q } }" := (wp wp_default E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  E  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e {{ v , Q } }" := (wp wp_default ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

(** Texan triples w/one later *)
Notation "'{{{' P } } } e @ s ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ s; E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' s ;  '/' E  ']' '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  E  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.

Notation "'{{{' P } } } e @ s ; E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ s; E {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' s ;  '/' E  ']' '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ E {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  E  '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.

(** Texan triples with [n] laters *)
Notation "'{{{' P } } } e 'at' n @ s ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷^n (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ s; E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e   'at'  n  '/' @  '[' s ;  '/' E  ']' '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e 'at' n @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷^n (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e   'at'  n  '/' @  E  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e 'at' n {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷^n (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  'at'  n  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.

Notation "'{{{' P } } } e 'at' n @ s ; E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷^n (Q -∗ Φ pat%V) -∗ WP e @ s; E {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e   'at'  n  '/' @  '[' s ;  '/' E  ']' '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e 'at' n @ E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷^n (Q -∗ Φ pat%V) -∗ WP e @ E {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e   'at'  n  '/' @  E  '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e 'at' n {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷^n (Q -∗ Φ pat%V) -∗ WP e {{ Φ }})%I
    (at level 20,
      format "'[hv' {{{  '[' P  ']' } } }  '/  ' e   'at'  n  '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.

(** Aliases for stdpp scope -- they inherit the levels and format from above. *)
Notation "'{{{' P } } } e @ s ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ s; E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ s ; E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ s; E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e {{ Φ }}) : stdpp_scope.

Notation "'{{{' P } } } e 'at' n @ s ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷^n (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ s; E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e 'at' n @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷^n (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e 'at' n {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷^n (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e 'at' n @ s ; E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷^n (Q -∗ Φ pat%V) -∗ WP e @ s; E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e 'at' n @ E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷^n (Q -∗ Φ pat%V) -∗ WP e @ E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e 'at' n {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷^n (Q -∗ Φ pat%V) -∗ WP e {{ Φ }}) : stdpp_scope.

(** Texan triples with *no* laters *)
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e @ s ; E ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ s; E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  '/' @  s ;  E  ⟨⟨⟨  x  ..  y ,  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e @ E ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E {{Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  '/' @  E  ⟨⟨⟨  x  ..  y ,  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e {{Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  '/' ⟨⟨⟨  x  ..  y ,  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.

Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e @ s ; E ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e @ s; E {{Φ }})%I
    (at level 20,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  '/' @  s ;  E  ⟨⟨⟨  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e @ E ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e @ E {{Φ }})%I
    (at level 20,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  '/' @  E  ⟨⟨⟨  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e {{Φ }})%I
    (at level 20,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  '/' ⟨⟨⟨  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.

(** Aliases for stdpp scope -- they inherit the levels and format from above. *)
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e @ s ; E ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ s; E {{ Φ }}) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e @ E ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E {{ Φ }}) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e {{ Φ }}) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e @ s ; E ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e @ s; E {{ Φ }}) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e @ E ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e @ E {{ Φ }}) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e {{ Φ }}) : stdpp_scope.



(** Notations for total weakest preconditions *)
(** Notations without binder -- only parsing because they overlap with the
notations with binder. *)
Notation "'WP' e @ s ; E [{ Φ } ]" := (twp s E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e @ E [{ Φ } ]" := (twp wp_default E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e [{ Φ } ]" := (twp wp_default ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.

(** Notations with binder. *)
Notation "'WP' e @ s ; E [{ v , Q } ]" := (twp s E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' '/' [{  '[' v ,  '/' Q  ']' } ] ']'") : bi_scope.
Notation "'WP' e @ E [{ v , Q } ]" := (twp twp_default E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  E  '/' [{  '[' v ,  '/' Q  ']' } ] ']'") : bi_scope.
Notation "'WP' e [{ v , Q } ]" := (twp twp_default ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' [{  '[' v ,  '/' Q  ']' } ] ']'") : bi_scope.

(* Texan triples *)
Notation "'[[{' P } ] ] e @ s ; E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ s; E [{ Φ }])%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' [[{  '[' P  ']' } ] ]  '/  ' e  '/' @  '[' s ;  '/' E  ']' '/' [[{  '[hv' x  ..  y ,  RET  pat ;  '/' Q  ']' } ] ] ']'") : bi_scope.
Notation "'[[{' P } ] ] e @ E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E [{ Φ }])%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' [[{  '[' P  ']' } ] ]  '/  ' e  '/' @  E  '/' [[{  '[hv' x  ..  y ,  RET  pat ;  '/' Q  ']' } ] ] ']'") : bi_scope.
Notation "'[[{' P } ] ] e [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e [{ Φ }])%I
    (at level 20, x closed binder, y closed binder,
       format "'[hv' [[{  '[' P  ']' } ] ]  '/  ' e  '/' [[{  '[hv' x  ..  y ,  RET  pat ;  '/' Q  ']' } ] ] ']'") : bi_scope.

Notation "'[[{' P } ] ] e @ s ; E [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e @ s; E [{ Φ }])%I
    (at level 20,
     format "'[hv' [[{  '[' P  ']' } ] ]  '/  ' e  '/' @  '[' s ;  '/' E  ']' '/' [[{  '[hv' RET  pat ;  '/' Q  ']' } ] ] ']'") : bi_scope.
Notation "'[[{' P } ] ] e @ E [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e @ E [{ Φ }])%I
    (at level 20,
     format "'[hv' [[{  '[' P  ']' } ] ]  '/  ' e  '/' @  E  '/' [[{  '[hv' RET  pat ;  '/' Q  ']' } ] ] ']'") : bi_scope.
Notation "'[[{' P } ] ] e [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e [{ Φ }])%I
    (at level 20,
     format "'[hv' [[{  '[' P  ']' } ] ]  '/  ' e  '/' [[{  '[hv' RET  pat ;  '/' Q  ']' } ] ] ']'") : bi_scope.

(** Aliases for stdpp scope -- they inherit the levels and format from above. *)
Notation "'[[{' P } ] ] e @ s ; E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ s; E [{ Φ }]) : stdpp_scope.
Notation "'[[{' P } ] ] e @ E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E [{ Φ }]) : stdpp_scope.
Notation "'[[{' P } ] ] e [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e [{ Φ }]) : stdpp_scope.
Notation "'[[{' P } ] ] e @ s ; E [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e @ s; E [{ Φ }]) : stdpp_scope.
Notation "'[[{' P } ] ] e @ E [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e @ E [{ Φ }]) : stdpp_scope.
Notation "'[[{' P } ] ] e [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP e [{ Φ }]) : stdpp_scope. 
