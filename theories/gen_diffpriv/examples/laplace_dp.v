(** A differential-privacy example on the GENERIC language: the Laplace
    mechanism is ε-DP.

    This is the USABILITY demonstration.  All the per-distribution machinery
    (the [Laplace] notation, the [wp_couple_laplace] coupling rule, the proof
    that it is sound) lives in the reusable library [gen_diffpriv.lib.laplace].
    A client "enables" the Laplace distribution for its development by:
      (1) declaring a signature containing [laplace_family], and
      (2) providing a [SampleIn laplace_family _] instance (one line).
    After that, the section needs nothing but [Context `{!diffprivGS Slap Σ}] —
    no canonical structures, no [spec_updateGS] instance, no [fill] notation,
    no hardcoded family index — and one writes [Laplace]/[wp_couple_laplace]
    exactly as in a hand-written single-distribution development. *)
From clutch.gen_diffpriv Require Import primitive_laws adequacy.
From clutch.gen_diffpriv.lib Require Import laplace.
From clutch.gen_prob_lang Require Import families.
From iris.prelude Require Import options.

Local Open Scope R.

(** (1) the signature, and (2) "enable" Laplace for it — the entire setup. *)
Definition Slap : Sig := [laplace_family].
#[global] Instance SampleIn_laplace : SampleIn laplace_family Slap := ltac:(solve_SampleIn).

Section laplace_example.
  Context `{!diffprivGS Slap Σ}.
  (* The only residual per-file line: pin the spec-context [fill] to this
     development's signature.  (Needed only when a statement mentions an explicit
     evaluation context [K]; logical-relation case studies use [REL] and need
     not write [fill] at all.) *)
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Slap)).

  (** The full λ-program ε-DP statement: the one-line Laplace mechanism
      [λ loc, Laplace(num/den, loc)] is ε-DP for 1-sensitive inputs
      (|loc − loc'| ≤ 1).  Proved with the STANDARD proof-mode tactics and the
      library's [wp_couple_laplace] — no per-development boilerplate at all. *)
  Lemma wp_laplace_diffpriv (loc loc' num den : Z) (ε : R) K E :
    IZR num / IZR den = ε →
    0 < IZR num / IZR den →
    (Z.abs (loc - loc') <= 1)%Z →
    {{{ ⤇ fill K ((λ: "l", Laplace #num #den "l" #())%V #loc') ∗ ↯m ε }}}
      (λ: "l", Laplace #num #den "l" #())%V #loc @ E
    {{{ (z : Z), RET #z; ⤇ fill K #z }}}.
  Proof.
    iIntros (Hε εpos Hsens Φ) "(Hr & Hε) HΦ".
    wp_pures.
    tp_pures.
    iApply (wp_couple_laplace loc loc' 0%Z 1%Z _ num den ε ε K E Hε εpos _ with "[$Hr $Hε]").
    iModIntro. iIntros (z) "Hr".
    replace (z + 0)%Z with z by lia.
    iApply ("HΦ" with "Hr").
    Unshelve.
    - replace (0 + loc - loc')%Z with (loc - loc')%Z by lia. exact Hsens.
    - simpl; lra.
  Qed.

End laplace_example.
