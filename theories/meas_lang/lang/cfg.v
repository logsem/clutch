From clutch.meas_lang.lang Require Export prelude types tapes state.
From mathcomp.analysis Require Import reals measure itv lebesgue_measure probability.
Definition cfg : measurableType _ := (expr * state)%type.
