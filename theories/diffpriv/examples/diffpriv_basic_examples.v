From clutch.diffpriv Require Import adequacy diffpriv.

Section logex.
  Context `{!diffprivGS Σ}.

  #[local] Open Scope R.

  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.

  Fact foo (loc loc' k k' : Z)
    (Hdist : (Z.abs (k + loc - loc') <= k')%Z)
    (num den : Z) (ε ε' : R) K E :
    IZR num / IZR den = ε →
    0 < IZR num / IZR den →
    ε' = (IZR k' * ε) →
    {{{ ⤇ fill K (Laplace #num #den #loc') ∗ ↯ ε' }}}
      Laplace #num #den #loc @ E
      {{{ (z : Z), RET #z; ⤇ fill K #(z+k) }}}.
  Proof.
  Abort.

End logex.
