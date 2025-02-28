From clutch.meas_lang.lang Require Import state.
From mathcomp.analysis Require Import reals measure itv lebesgue_measure probability.
Definition cfg : measurableType _ := (expr * state)%type.
