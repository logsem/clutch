From clutch Require Import clutch.
From mathcomp Require Import eqtype choice fintype.
From deriving Require Import deriving instances.

Set Primitive Projections.

Scheme loc_rect := Induction for loc Sort Type.

Definition un_op_indDef := [indDef for prob_lang.un_op_rect].
Canonical un_op_indType := IndType prob_lang.un_op un_op_indDef.
Definition bin_op_indDef := [indDef for prob_lang.bin_op_rect].
Canonical bin_op_indType := IndType prob_lang.bin_op bin_op_indDef.
Definition loc_indDef := [indDef for loc_rect].
Canonical loc_indType := IndType loc loc_indDef.
Definition binder_indDef := [indDef for stdpp.binders.binder_rect].
Canonical binder_indType := IndType stdpp.binders.binder binder_indDef.
Definition base_lit_indDef := [indDef for base_lit_rect].
Canonical base_lit_indType := IndType base_lit base_lit_indDef.

Scheme val_mrect := Induction for prob_lang.val Sort Type
    with expr_mrect := Induction for prob_lang.expr Sort Type.

Combined Scheme val_expr_rect from val_mrect, expr_mrect.
Definition val_expr_indDef := [indDef for val_expr_rect].
Canonical val_indType := IndType prob_lang.val val_expr_indDef.
Canonical expr_indType := IndType prob_lang.expr val_expr_indDef.


Definition un_op_eqMixin := [derive eqMixin for un_op].
Canonical un_op_eqType := EqType un_op un_op_eqMixin.
Definition bin_op_eqMixin := [derive eqMixin for bin_op].
Canonical bin_op_eqType := EqType bin_op bin_op_eqMixin.
Definition loc_eqMixin := [derive eqMixin for loc].
Canonical loc_eqType := EqType loc loc_eqMixin.
Definition binder_eqMixin := [derive eqMixin for binder].
Canonical binder_eqType := EqType binder binder_eqMixin.
Definition base_lit_eqMixin := [derive eqMixin for base_lit].
Canonical base_lit_eqType := EqType base_lit base_lit_eqMixin.

Definition val_eqMixin := [derive lazy eqMixin for prob_lang.val].
Canonical val_eqType := EqType prob_lang.val val_eqMixin.
Definition expr_eqMixin := [derive lazy eqMixin for prob_lang.expr].
Canonical expr_eqType := EqType prob_lang.expr expr_eqMixin.

Definition un_op_choiceMixin := [derive choiceMixin for un_op].
Canonical un_op_choiceType := ChoiceType un_op un_op_choiceMixin.
Definition bin_op_choiceMixin := [derive choiceMixin for bin_op].
Canonical bin_op_choiceType := ChoiceType bin_op bin_op_choiceMixin.
Definition loc_choiceMixin := [derive choiceMixin for loc].
Canonical loc_choiceType := ChoiceType loc loc_choiceMixin.
Definition binder_choiceMixin := [derive choiceMixin for binder].
Canonical binder_choiceType := ChoiceType binder binder_choiceMixin.
Definition base_lit_choiceMixin := [derive choiceMixin for base_lit].
Canonical base_lit_choiceType := ChoiceType base_lit base_lit_choiceMixin.

Definition val_choiceMixin := [derive choiceMixin for prob_lang.val].
Canonical val_choiceType := Eval hnf in ChoiceType prob_lang.val val_choiceMixin.
Definition expr_choiceMixin := [derive choiceMixin for prob_lang.expr].
Canonical expr_choiceType := Eval hnf in ChoiceType prob_lang.expr expr_choiceMixin.


Definition un_op_countMixin := [derive countMixin for un_op].
Canonical un_op_countType := CountType un_op un_op_countMixin.
Definition bin_op_countMixin := [derive countMixin for bin_op].
Canonical bin_op_countType := CountType bin_op bin_op_countMixin.
Definition loc_countMixin := [derive countMixin for loc].
Canonical loc_countType := CountType loc loc_countMixin.
Definition binder_countMixin := [derive countMixin for binder].
Canonical binder_countType := CountType binder binder_countMixin.
Definition base_lit_countMixin := [derive countMixin for base_lit].
Canonical base_lit_countType := CountType base_lit base_lit_countMixin.

Definition val_countMixin := [derive countMixin for prob_lang.val].
Canonical val_countType := Eval hnf in CountType prob_lang.val val_countMixin.
Definition expr_countMixin := [derive countMixin for prob_lang.expr].
Canonical expr_countType := Eval hnf in CountType prob_lang.expr expr_countMixin.
