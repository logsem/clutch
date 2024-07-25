From clutch.prob Require Import distribution.
From clutch.common Require Import language.

Section scheduler.
  Context {Λ : language}.
  
  Record scheduler (A : Type) `{Countable A} :=
    Scheduler {
        scheduler_f :> A → list (cfg Λ) -> (A*nat)
      }.
  
  
End scheduler.
