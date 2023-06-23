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

Class Rwp (PROP EXPR VAL A : Type) := {
  rwp : A → coPset → EXPR → (VAL → PROP) → PROP;
  rwp_default : A
}.
Global Arguments rwp {_ _ _ _ _} _ _ _%E _%I.
Global Instance: Params (@rwp) 9 := {}.
Global Arguments rwp_default : simpl never.

Class Rswp (PROP EXPR VAL A : Type) := {
  rswp : nat → A → coPset → EXPR → (VAL → PROP) → PROP;
  rswp_default : A
}.
Global Arguments rswp {_ _ _ _ _} _ _ _%E _%I.
Global Instance: Params (@rswp) 9 := {}.
Global Arguments rswp_default : simpl never.

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

(* Texan triples *)
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


(** Notations for refinement weakest preconditions *)
(** Notations without binder -- only parsing because they overlap with the
notations with binder. *)
Notation "'RWP' e @ s ; E ⟨⟨ Φ ⟩ ⟩" := (rwp s E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'RWP' e @ E ⟨⟨ Φ ⟩ ⟩" := (rwp rwp_default E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'RWP' e ⟨⟨ Φ ⟩ ⟩" := (rwp rwp_default ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.


(** Notations with binder.  The indentation for the inner format block is chosen
such that *if* one has a single-character mask (e.g. [E]), the second line
should align with the binder(s) on the first line. *)
Notation "'RWP' e @ s ; E ⟨⟨ v , Q ⟩ ⟩" := (rwp s E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'RWP'  e  '/' '[          ' @  s ;  E  ⟨⟨  v ,  Q  ⟩ ⟩ ']' ']'") : bi_scope.
Notation "'RWP' e @ E ⟨⟨ v , Q ⟩ ⟩" := (rwp rwp_default E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'RWP'  e  '/' '[       ' @  E  ⟨⟨  v ,  Q  ⟩ ⟩ ']' ']'") : bi_scope.
Notation "'RWP' e ⟨⟨ v , Q ⟩ ⟩" := (rwp rwp_default ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'RWP'  e  '/' '[   ' ⟨⟨  v ,  Q  ⟩ ⟩ ']' ']'") : bi_scope.

(* Texan triples *)
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e @ s ; E ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RWP e @ s; E ⟨⟨ Φ ⟩⟩)%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  '/' @  s ;  E  ⟨⟨⟨  x  ..  y ,  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e @ E ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RWP e @ E ⟨⟨ Φ ⟩⟩)%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  '/' @  E  ⟨⟨⟨  x  ..  y ,  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RWP e ⟨⟨ Φ ⟩⟩)%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  '/' ⟨⟨⟨  x  ..  y ,  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.

Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e @ s ; E ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ RWP e @ s; E ⟨⟨ Φ ⟩⟩)%I
    (at level 20,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  '/' @  s ;  E  ⟨⟨⟨  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e @ E ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ RWP e @ E ⟨⟨ Φ ⟩⟩)%I
    (at level 20,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  '/' @  E  ⟨⟨⟨  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ RWP e ⟨⟨ Φ ⟩⟩)%I
    (at level 20,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  '/' ⟨⟨⟨  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.

(** Aliases for stdpp scope -- they inherit the levels and format from above. *)
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e @ s ; E ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RWP e @ s; E ⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e @ E ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RWP e @ E ⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RWP e ⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e @ s ; E ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ RWP e @ s; E ⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e @ E ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ RWP e @ E ⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ RWP e ⟨⟨ Φ ⟩⟩) : stdpp_scope.

(** Notations for stronger weakest preconditions *)
(** Notations without binder -- only parsing because they overlap with the
notations with binder. *)
Notation "'RSWP' e 'at' k @ s ; E ⟨⟨ Φ ⟩ ⟩" := (rswp k%nat s E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'RSWP' e 'at' k @ E ⟨⟨ Φ ⟩ ⟩" := (rswp k%nat rswp_default E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'RSWP' e 'at' k ⟨⟨ Φ ⟩ ⟩" := (rswp k%nat rswp_default ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.

(** Notations with binder.  The indentation for the inner format block is chosen
such that *if* one has a single-character mask (e.g. [E]), the second line
should align with the binder(s) on the first line. *)
Notation "'RSWP' e 'at' k @ s ; E ⟨⟨ v , Q ⟩ ⟩" := (rswp k%nat s E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'RSWP'  e  'at'  k  '/' '[          ' @  s ;  E  ⟨⟨  v ,  Q  ⟩ ⟩ ']' ']'") : bi_scope.
Notation "'RSWP' e 'at' k @ E ⟨⟨ v , Q ⟩ ⟩" := (rswp k%nat rswp_default E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'RSWP'  e  'at'  k  '/' '[       ' @  E  ⟨⟨  v ,  Q  ⟩ ⟩ ']' ']'") : bi_scope.
Notation "'RSWP' e 'at' k ⟨⟨ v , Q ⟩ ⟩" := (rswp k%nat rswp_default ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'RSWP'  e  'at'  k  '/' '[   ' ⟨⟨  v ,  Q  ⟩ ⟩ ']' ']'") : bi_scope.

(* Texan triples *)
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k @ s ; E ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ,
      P -∗ ▷^k (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩)%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  'at'  k  '/' @  s ;  E  ⟨⟨⟨  x  ..  y ,  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k @ E ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ,
      P -∗ ▷^k (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RSWP e at k @ E ⟨⟨ Φ ⟩⟩)%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  'at'  k  '/' @  E  ⟨⟨⟨  x  ..  y ,  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ,
      P -∗ ▷^k (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RSWP e at k ⟨⟨ Φ ⟩⟩)%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e   'at'  k  '/' ⟨⟨⟨  x  ..  y ,  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.

Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k @ s ; E ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ, P -∗ ▷^k (Q -∗ Φ pat%V) -∗ RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩)%I
    (at level 20,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  'at'  k  '/' @  s ;  E  ⟨⟨⟨  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k @ E ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ, P -∗ ▷^k (Q -∗ Φ pat%V) -∗ RSWP e at k @ E ⟨⟨ Φ ⟩⟩)%I
    (at level 20,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  'at'  k  '/' @  E  ⟨⟨⟨  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (□ ∀ Φ, P -∗ ▷^k(Q -∗ Φ pat%V) -∗ RSWP e at k ⟨⟨ Φ ⟩⟩)%I
    (at level 20,
     format "'[hv' ⟨⟨⟨  P  ⟩ ⟩ ⟩  '/  ' e  'at'  k  '/' ⟨⟨⟨  RET  pat ;  Q  ⟩ ⟩ ⟩ ']'") : bi_scope.

(** Aliases for stdpp scope -- they inherit the levels and format from above. *)
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k @ s ; E ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ ▷^k (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k @ E ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ ▷^k (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RSWP e at k @ E ⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k ⟨⟨⟨ x .. y , 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ ▷^k (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ RSWP e at k ⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k @ s ; E ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ ▷^k (Q -∗ Φ pat%V) -∗ RSWP e at k @ s; E ⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k @ E ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ ▷^k (Q -∗ Φ pat%V) -∗ RSWP e at k @ E ⟨⟨ Φ ⟩⟩) : stdpp_scope.
Notation "'⟨⟨⟨' P ⟩ ⟩ ⟩ e 'at' k ⟨⟨⟨ 'RET' pat ; Q ⟩ ⟩ ⟩" :=
  (∀ Φ, P -∗ ▷^k (Q -∗ Φ pat%V) -∗ RSWP e at k ⟨⟨ Φ ⟩⟩) : stdpp_scope.
