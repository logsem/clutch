From clutch.meas_lang.lang Require Import state.
From mathcomp.analysis Require Import measure lebesgue_measure probability.
Require Import mathcomp.reals_stdlib.Rstruct.
Require Import mathcomp.reals.reals.
Definition cfg : measurableType _ := (expr * state)%type.
