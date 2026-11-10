(** * Extraction for the executable semantics ([exec/src])

    Integers, naturals and labels become [Big_int_Z.big_int] (zarith),
    effect and variable names become OCaml strings.  The interpreter uses
    the extracted substitutions and operator evaluations, so that these
    agree with [semantics.v] by construction, and the extracted [decomp]
    and [fill] as the reference against which [--check] validates its
    evaluation contexts.

    The case studies are sections over their class parameters, so each
    system is a function of the class records.  The group [Zpˣ] of
    [valgroup_Zpx] is used through its operations (see [zpx_ops]); its
    records are built in OCaml ([exec/src/instances.ml]), which also avoids
    extracting mathcomp's finite group structures. *)
From Stdlib Require Extraction.
From Stdlib Require Import ZArith.
From Stdlib Require Import ExtrOcamlBasic ExtrOcamlNativeString ExtrOcamlZBigInt ExtrOcamlNatBigInt.
From clutch.prob_eff_lang.probblaze Require Import syntax semantics.
From clutch.prob_eff_lang.probblaze.uc Require Import comp_operators uc_systems.
From clutch.prob_eff_lang.probblaze.examples Require Import valgroup valgroup_Zpx.
From clutch.prob_eff_lang.probblaze.examples Require dhke_def sec_channel_def secure_add_def add3_def auth_def.
From clutch.prob_eff_lang.probblaze.examples Require definition_thunk_receiver_corrupt.
From clutch.prob_eff_lang.probblaze.examples Require fin_val_type fin_val_type_prod valgroup_finval ske ske_prf ske_sec_chan_def.
From clutch_exec Require Import zpx_ops qr_ops fin_ops exec_common env_dhke env_schan env_add env_add3 env_auth env_ot env_ske.

(* [nat] and [Z] are both big integers. *)
Extract Constant Z.of_nat => "(fun x -> x)".
(* stdpp's decision procedure for string equality, on OCaml strings. *)
Extract Inlined Constant stdpp.strings.String.eq_dec => "(=)".

(* Finite value types: in the executable instances, the [finType] field
   holds a descriptor ([exec_fin.ml]) from which the cardinality is
   computed; the product type and the group as a finite type are built on
   descriptors as well.  The group's [vgG] field holds the descriptor of
   its order ([exec/src/instances.ml]). *)
Extract Constant fin_val_type.card => "(fun fvt -> Exec_fin.card (Obj.magic fvt.fvT))".
Extract Constant fin_val_type_prod.prod_fvt =>
  "(fun t1 t2 -> { fvT = Obj.magic (Exec_fin.Prod (Obj.magic t1.fvT, Obj.magic t2.fvT));
                   fvtval = (fun xy -> let (x, y) = Obj.magic xy in PairV (t1.fvtval x, t2.fvtval y)) })".
Extract Constant valgroup_finval.vg_fvt => "(fun vg -> { fvT = Obj.magic vg.vgG; fvtval = vg.vgval })".

Extraction "probblaze.ml"
  (* semantics *)
  val_subst val_subst' lbl_subst un_op_eval bin_op_eval
  decomp fill to_eff ectx_labels
  (* the group Zpˣ *)
  vunit_z vmult_p vinv_z veq_p int_of_vg_p vg_of_int_p
  (* the prime-order subgroup of squares *)
  qr_vg_of_int qr_int_of_vg
  (* UC operators *)
  fac_op fac_app func_comp parallel_composition functionality_composition
  (* DHKE *)
  dhke_def.F_AUTH dhke_def.DH_KE dhke_def.DH_KE_tapeless dhke_def.DH_SIM
  dhke_def.F_KE dhke_def.F_KE_just_lazy dhke_def.F_KE_lazy_alice
  dhke_def.C_lazy dhke_def.C_lazy_sess dhke_def.C_DH_real dhke_def.C_DH_rand
  dhke_def.DH_real dhke_def.DH_rand
  dhke_def.REAL_DHKE dhke_def.IDEAL_DHKE dhke_def.SIM_DHKE dhke_def.RED_DHKE
  (* one-message secure channel, and its composition with DHKE *)
  sec_channel_def.F_OAUTH sec_channel_def.CHAN sec_channel_def.F_CHAN sec_channel_def.CHAN_SIM_lazy
  sec_channel_def.REAL_SCHAN sec_channel_def.IDEAL_SCHAN sec_channel_def.SIM_SCHAN
  REAL_DHKE_CHAN SIM_DHKE_CHAN RED_DHKE_CHAN
  (* secure addition *)
  secure_add_def.π_ADD secure_add_def.F_ADD secure_add_def.S_ADD
  secure_add_def.REAL_ADD secure_add_def.IDEAL_ADD secure_add_def.SIM_ADD secure_add_def.SIM_IDEAL_ADD
  (* three-party secure addition *)
  add3_def.F_NET add3_def.Π add3_def.F_ADD3 add3_def.S_ADD3
  add3_def.REAL_ADD3 add3_def.IDEAL_ADD3 add3_def.SIM_ADD3 add3_def.SIM_IDEAL_ADD3
  (* authenticated channel *)
  auth_def.MAC auth_def.MAC_pad auth_def.MAC_ideal
  auth_def.AUTH auth_def.AUTH_pad auth_def.AUTH_ideal auth_def.S_AUTH
  (* oblivious transfer, corrupt receiver *)
  definition_thunk_receiver_corrupt.F_CRS
  definition_thunk_receiver_corrupt.OT_Real_Receiver_Corrupted
  definition_thunk_receiver_corrupt.OT_SIM_FOT_thunk
  OT_REAL_RC
  (* the secure channel with the PRF-based symmetric scheme *)
  fin_int_of fin_of_int toy_prf
  fin_val_type_prod.prod_fvt fin_val_type_prod.prod_fvts valgroup_finval.vg_fvt valgroup_finval.vg_fvts
  ske_prf.prf_sym_struct ske_prf.prf_real ske_prf.prf_ideal ske_prf.red_prf
  ske.enc_real ske.enc_ideal
  ske_sec_chan_def.REAL_SKE ske_sec_chan_def.SIM_IDEAL_SKE ske_sec_chan_def.GAME1 ske_sec_chan_def.GAME2
  ske_sec_chan_def.RED_SKE RED_SKE_PRF
  (* environments *)
  dlog toy_mask env_dhke_honest env_dhke_dlog env_dhke_block
  env_chan_honest env_chan_retry env_chan_peek env_dhke_chan_dlog
  env_add_honest env_add_peek
  env_add3_honest env_add3_peek
  env_auth_honest env_auth_forge
  env_ot_receiver
  env_ske_honest env_ske_peek.
