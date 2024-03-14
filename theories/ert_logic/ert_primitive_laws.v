(** This file proves the basic laws of the ProbLang weakest precondition by
    applying the lifting lemmas. *)
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth excl.
From iris.base_logic.lib Require Export ghost_map.
From clutch.prob_lang Require Export class_instances.
From clutch.prob_lang Require Import tactics lang notation.
From iris.prelude Require Import options.
From clutch.ert_logic Require Export expected_time_credits ert_weakestpre lifting.
