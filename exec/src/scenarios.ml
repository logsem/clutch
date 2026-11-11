(* The registry of executable case studies: systems, environments and the
   claims that [check] tests. *)
open Syn
module P = Probblaze
module I = Instances

type sys = { s_name : string; s_doc : string; s_build : I.group -> value }
type env = { e_name : string; e_doc : string; e_build : I.group -> (string -> value) -> value }

(* A world is an environment applied to a system. *)
type world = { env : string; sys : string }

type claim =
  | Always of { w : world; expect : string; doc : string }
      (** every run of [w] returns [expect] *)
  | Adv_zero of { env : string; x : string; y : string; doc : string }
      (** [env] cannot tell [x] from [y] *)
  | Adv_le of { lhs : string * string * string; rhs : string * string * string; doc : string }
      (** adv(env, x, y) ≤ adv(env', x', y') *)
  | Adv_bound of { env : string; x : string; y : string; bound : string * (I.group -> Q.t); doc : string }
      (** adv(env, x, y) ≤ bound, given as a formula and its value *)

type case = {
  name : string;
  doc : string;
  systems : sys list;
  envs : env list;
  claims : claim list;
  instances : (I.kind * int) list;  (** the instances [check] uses by default *)
}

let sys s_name s_doc s_build = { s_name; s_doc; s_build }
let env e_name e_doc e_build = { e_name; e_doc; e_build }

(* The factory operators of [uc_systems]. *)
let comp f g = P.fac_op P.func_comp f g (* F ∘f G *)
let par f g = P.fac_op P.parallel_composition f g (* F ||ᵣ G *)
let fcomp f g = P.fac_op P.functionality_composition f g (* F ∘F G *)

let grp f (g : I.group) = f g.vg g.cg g.vgg

(* ------------------------------------------------------------------------ *)
(* Diffie–Hellman key exchange                                              *)

let dhke =
  {
    name = "dhke";
    doc = "Diffie–Hellman key exchange over F_AUTH (examples/dhke)";
    systems =
      [
        sys "real" "F_AUTH ∘f DH_KE  (REAL_DHKE)" (grp P.rEAL_DHKE);
        sys "ideal" "(F_AUTH ∘f DH_SIM) ∘f F_KE_lazy_alice  (SIM_DHKE ∘f IDEAL_DHKE)" (fun g ->
            comp (grp P.sIM_DHKE g) (grp P.iDEAL_DHKE g));
        sys "real-tapeless" "F_AUTH ∘f DH_KE_tapeless" (fun g -> comp P.f_AUTH (grp P.dH_KE_tapeless g));
        sys "hyb-real" "F_AUTH ∘f C_DH_real  (the protocol with the real DDH oracle)" (fun g ->
            comp P.f_AUTH (grp P.c_DH_real g));
        sys "hyb-rand" "F_AUTH ∘f C_DH_rand  (the protocol with the random DDH oracle)" (fun g ->
            comp P.f_AUTH (grp P.c_DH_rand g));
        sys "ddh-real" "DH_real: the real DDH game, for the reduction" (grp P.dH_real);
        sys "ddh-rand" "DH_rand: the random DDH game, for the reduction" (grp P.dH_rand);
      ];
    envs =
      [
        env "honest" "Alice, Bob, Alice query their keys; all messages delivered; true iff the keys agree"
          (fun g obs -> P.env_dhke_honest g.cg obs);
        env "dlog" "solves the discrete log of Alice's half; true iff Bob's key is gB^(log gA)" (fun g obs ->
            P.env_dhke_dlog g.vg g.cg g.vgg obs);
        env "block" "delivers nothing; true iff no party gets a key" (fun _ obs -> P.env_dhke_block obs);
        env "red-honest" "RED_DHKE honest: the DDH reduction around the honest environment" (fun g obs ->
            P.rED_DHKE (P.env_dhke_honest g.cg obs));
        env "red-dlog" "RED_DHKE dlog: the DDH reduction around the dlog distinguisher" (fun g obs ->
            P.rED_DHKE (P.env_dhke_dlog g.vg g.cg g.vgg obs));
      ];
    claims =
      [
        Always { w = { env = "honest"; sys = "real" }; expect = "true"; doc = "honest parties agree on the key" };
        Always { w = { env = "honest"; sys = "ideal" }; expect = "true"; doc = "the ideal world gives both parties the key" };
        Always { w = { env = "block"; sys = "real" }; expect = "true"; doc = "no key without delivery" };
        Always { w = { env = "block"; sys = "ideal" }; expect = "true"; doc = "no key without delivery (ideal)" };
        Adv_zero { env = "dlog"; x = "real"; y = "hyb-real"; doc = "REAL_DHKE ≈ F_AUTH ∘f C_DH_real (dhke_real.v)" };
        Adv_zero { env = "dlog"; x = "ideal"; y = "hyb-rand"; doc = "SIM ∘f IDEAL ≈ F_AUTH ∘f C_DH_rand (dhke_sim.v)" };
        Adv_zero { env = "dlog"; x = "real"; y = "real-tapeless"; doc = "DH_KE ≈ DH_KE_tapeless (dhke_tapeless.v)" };
        Adv_le
          {
            lhs = ("dlog", "real", "ideal");
            rhs = ("red-dlog", "ddh-real", "ddh-rand");
            doc = "adv_DHKE: bounded by the DDH advantage of the reduction";
          };
        Adv_le
          {
            lhs = ("honest", "real", "ideal");
            rhs = ("red-honest", "ddh-real", "ddh-rand");
            doc = "adv_DHKE for the honest environment";
          };
      ];
    instances = [ (I.Zpx, 5); (I.Zpx, 7); (I.Zpx, 11) ];
  }

(* ------------------------------------------------------------------------ *)
(* One-message secure channel                                              *)

(* An involutive mask, [k · m⁻¹] ([exec_common.toy_mask]); the record's
   other fields are not used at run time. *)
let mask (g : I.group) : Obj.t P.mask0 =
  { P.mask1 = P.toy_mask g.cg; _UU03c4_mask = P.TInt; mask_sem = (fun a _ -> a) }

let schan =
  {
    name = "schan";
    doc = "one-message secure channel with a group mask (examples/secure_channel)";
    systems =
      [
        sys "real" "(F_KE_lazy_alice ||ᵣ F_OAUTH) ∘f CHAN  (REAL_SCHAN)" (fun g -> P.rEAL_SCHAN g.vg g.cg g.vgg (mask g));
        sys "ideal" "CHAN_SIM_lazy ∘f F_CHAN  (SIM_SCHAN ∘f IDEAL_SCHAN)" (fun g ->
            comp (grp P.sIM_SCHAN g) (P.iDEAL_SCHAN g.cg));
      ];
    envs =
      [
        env "honest" "Alice sends a uniform message, Bob receives; true iff he gets it" (fun g ->
            grp P.env_chan_honest g);
        env "retry" "receive, send, receive, send, receive; true iff some receive gets the message" (fun g ->
            grp P.env_chan_retry g);
        env "peek" "true iff the ciphertext equals the message" (fun g -> grp P.env_chan_peek g);
      ];
    claims =
      [
        Always { w = { env = "honest"; sys = "real" }; expect = "true"; doc = "the channel delivers the message" };
        Always { w = { env = "honest"; sys = "ideal" }; expect = "true"; doc = "the ideal channel delivers it" };
        Always { w = { env = "retry"; sys = "real" }; expect = "true"; doc = "the channel delivers the message" };
        Adv_zero { env = "honest"; x = "real"; y = "ideal"; doc = "adv_SCHAN (perfect)" };
        Adv_zero { env = "peek"; x = "real"; y = "ideal"; doc = "adv_SCHAN (perfect)" };
      ];
    instances = [ (I.Zpx, 5); (I.Zpx, 7); (I.Zpx, 11) ];
  }

let dhke_chan =
  {
    name = "dhke-chan";
    doc = "the secure channel over DHKE, by the composition theorem (advantage_dhke_sec_channel)";
    systems =
      [
        sys "real" "(REAL_DHKE ||ᵣ F_OAUTH) ∘f CHAN  (REAL_DHKE_CHAN)" (fun g ->
            P.rEAL_DHKE_CHAN g.vg g.cg g.vgg (mask g));
        sys "ideal" "(SIM_DHKE ∘F SIM_SCHAN) ∘f F_CHAN  (SIM_DHKE_CHAN ∘f IDEAL_DHKE_CHAN)" (fun g ->
            comp (grp P.sIM_DHKE_CHAN g) (P.iDEAL_SCHAN g.cg));
        sys "ddh-real" "DH_real" (grp P.dH_real);
        sys "ddh-rand" "DH_rand" (grp P.dH_rand);
      ];
    envs =
      [
        env "honest" "Alice sends a uniform message, Bob receives; true iff he gets it" (fun g ->
            grp P.env_chan_honest g);
        env "retry" "receive, send, receive, send, receive; true iff some receive gets the message" (fun g ->
            grp P.env_chan_retry g);
        env "dlog" "recovers the key by a discrete log and unmasks the ciphertext" (fun g obs ->
            P.env_dhke_chan_dlog g.vg g.cg g.vgg (mask g) obs);
        env "sched" "the scheduler of dhke_chan_delivery.v: Alice's share leak runs Bob by a nested call of the session" (fun g ->
            grp P.env_chan_sched g);
        env "red-honest" "RED_DHKE_CHAN honest" (fun g obs ->
            P.rED_DHKE_CHAN g.vg g.cg (mask g) (grp P.env_chan_honest g obs));
        env "red-dlog" "RED_DHKE_CHAN dlog" (fun g obs ->
            P.rED_DHKE_CHAN g.vg g.cg (mask g) (P.env_dhke_chan_dlog g.vg g.cg g.vgg (mask g) obs));
      ];
    claims =
      [
        (* Liveness: the composed channel never delivers to a client that
           enters the session once.  CHAN commits the message before asking
           for Alice's key, and Alice's first key query in DH_KE fails
           because Bob has not sent his half yet; the simulator reproduces
           this in the ideal world.  With F_KE_lazy_alice instead of DH_KE
           ([schan]) the channel delivers. *)
        Always
          { w = { env = "honest"; sys = "real" }; expect = "false";
            doc = "never delivers: Alice's first key query fails, and CHAN has already committed the message" };
        Always { w = { env = "retry"; sys = "real" }; expect = "false"; doc = "no single-entry schedule of the client delivers" };
        Always { w = { env = "retry"; sys = "ideal" }; expect = "false"; doc = "nor in the ideal world" };
        (* The scheduler of dhke_chan_delivery.v interleaves the parties:
           Bob runs inside the leak of Alice's share, by a nested call of the
           same session ([τ__F] is unrestricted since e74cf72e). *)
        Always
          { w = { env = "sched"; sys = "real" }; expect = "true";
            doc = "dhke_chan_delivers: the scheduled run delivers the message" };
        Always { w = { env = "sched"; sys = "ideal" }; expect = "true"; doc = "and so does the ideal world" };
        Adv_le
          {
            lhs = ("dlog", "real", "ideal");
            rhs = ("red-dlog", "ddh-real", "ddh-rand");
            doc = "dhke_chan_realises: bounded by the DDH advantage of the reduction";
          };
        Adv_le
          { lhs = ("honest", "real", "ideal"); rhs = ("red-honest", "ddh-real", "ddh-rand"); doc = "dhke_chan_realises" };
      ];
    instances = [ (I.Zpx, 5); (I.Zpx, 7) ];
  }

(* ------------------------------------------------------------------------ *)
(* Secure addition                                                          *)

let add =
  {
    name = "add";
    doc = "secure addition with a corrupt aggregator (examples/secure_add)";
    systems =
      [
        sys "real" "F_CHAN ∘F π_ADD  (REAL_ADD)" (grp P.rEAL_ADD);
        sys "ideal" "S_ADD ∘f F_ADD  (SIM_IDEAL_ADD)" (grp P.sIM_IDEAL_ADD);
      ];
    envs =
      [
        env "honest" "uniform inputs; true iff Charlie's messages multiply to x · y" (fun g ->
            grp P.env_add_honest g);
        env "peek" "true iff Alice's message to Charlie is her input" (fun g -> grp P.env_add_peek g);
      ];
    claims =
      [
        Always { w = { env = "honest"; sys = "real" }; expect = "true"; doc = "Charlie learns x · y" };
        Always { w = { env = "honest"; sys = "ideal" }; expect = "true"; doc = "Charlie learns x · y (ideal)" };
        Adv_zero { env = "honest"; x = "real"; y = "ideal"; doc = "adv_ADD (perfect)" };
        Adv_zero { env = "peek"; x = "real"; y = "ideal"; doc = "adv_ADD (perfect)" };
      ];
    instances = [ (I.Zpx, 5); (I.Zpx, 7); (I.Zpx, 11) ];
  }

(* ------------------------------------------------------------------------ *)
(* Three-party secure addition                                              *)

let add3 =
  let inputs (g : I.group) = List.map (fun i -> Z.of_int (i mod g.order)) [ 1; 2; 3 ] in
  let honest g obs = match inputs g with [ a; b; c ] -> P.env_add3_honest g.cg a b c obs | _ -> assert false in
  let peek g obs = match inputs g with [ a; b; c ] -> P.env_add3_peek g.cg a b c obs | _ -> assert false in
  let sc c = Z.of_int c in
  {
    name = "add3";
    doc = "three-party secure addition, one party passively corrupted, multi-session (examples/secure_add3)";
    systems =
      List.concat_map
        (fun c ->
          [
            sys (Printf.sprintf "real%d" c) (Printf.sprintf "F_NET ∘F Π %d  (REAL_ADD3 %d)" c c) (fun g ->
                P.rEAL_ADD3 g.vg g.cg g.vgg (sc c));
            sys (Printf.sprintf "ideal%d" c) (Printf.sprintf "S_ADD3 %d ∘f F_ADD3 %d  (SIM_IDEAL_ADD3 %d)" c c c)
              (fun g -> P.sIM_IDEAL_ADD3 g.vg g.cg g.vgg (sc c));
          ])
        [ 0; 1; 2 ];
    envs =
      [
        env "honest" "schedules the three parties on inputs 1, 2, 3; true iff all output the product" honest;
        env "peek" "true iff the first message the corrupt party receives is the unit" peek;
      ];
    claims =
      [
        Always { w = { env = "honest"; sys = "real0" }; expect = "true"; doc = "all parties output the product" };
        Always { w = { env = "honest"; sys = "ideal0" }; expect = "true"; doc = "all parties output the product (ideal)" };
        Always { w = { env = "honest"; sys = "real2" }; expect = "true"; doc = "all parties output the product" };
        Adv_zero { env = "honest"; x = "real0"; y = "ideal0"; doc = "adv_ADD3 (perfect)" };
        Adv_zero { env = "peek"; x = "real0"; y = "ideal0"; doc = "adv_ADD3 (perfect)" };
        Adv_zero { env = "peek"; x = "real1"; y = "ideal1"; doc = "adv_ADD3 (perfect)" };
      ];
    instances = [ (I.Zpx, 5); (I.Qr, 7) ];
  }

(* ------------------------------------------------------------------------ *)
(* Authenticated channel                                                    *)

let two_over_q = ("2/q", fun (g : I.group) -> Q.make (Z.of_int 2) (Z.of_int g.order))

let auth =
  {
    name = "auth";
    doc = "the authenticated channel F_AUTH from one-time MACs (examples/auth)";
    systems =
      [
        sys "real" "AUTH = AUTH_of MAC" (grp P.aUTH);
        sys "pad" "AUTH_pad = AUTH_of MAC_pad" (grp P.aUTH_pad);
        sys "ideal-mac" "AUTH_ideal = AUTH_of MAC_ideal" (grp P.aUTH_ideal);
        sys "ideal" "S_AUTH ∘f F_AUTH" (fun g -> comp (grp P.s_AUTH g) P.f_AUTH);
      ];
    envs =
      [
        env "honest" "Alice sends a uniform group element to Bob; true iff he receives it" (fun g ->
            grp P.env_auth_honest g);
        env "forge" "delivers (m · g, t) for the tagged (m, t); true iff Bob accepts" (fun g ->
            grp P.env_auth_forge g);
      ];
    claims =
      [
        Always { w = { env = "honest"; sys = "real" }; expect = "true"; doc = "Bob receives Alice's message" };
        Always { w = { env = "honest"; sys = "ideal" }; expect = "true"; doc = "Bob receives Alice's message (ideal)" };
        Adv_zero { env = "forge"; x = "real"; y = "pad"; doc = "MAC ≈ MAC_pad (auth_mac.v)" };
        Adv_bound { env = "forge"; x = "pad"; y = "ideal-mac"; bound = two_over_q; doc = "MAC_pad ≈ MAC_ideal up to 1/q per instance" };
        Adv_zero { env = "forge"; x = "ideal-mac"; y = "ideal"; doc = "AUTH_ideal ≈ S_AUTH ∘f F_AUTH (auth_prf.v)" };
        Adv_bound { env = "forge"; x = "real"; y = "ideal"; bound = two_over_q; doc = "adv_AUTH" };
      ];
    instances = [ (I.Qr, 7); (I.Qr, 11); (I.Qr, 23) ];
  }

(* ------------------------------------------------------------------------ *)
(* Oblivious transfer, corrupt receiver                                     *)

let ot_rc =
  {
    name = "ot-rc";
    doc = "1-out-of-2 oblivious transfer in the CRS model, corrupt receiver (examples/ot)";
    systems =
      [
        sys "real" "λ f effs, F_CRS (λ doCRS, OT_Real_Receiver_Corrupted f (effs, doCRS))" (grp P.oT_REAL_RC);
        sys "ideal" "OT_SIM_FOT_thunk" (grp P.oT_SIM_FOT_thunk);
      ];
    envs =
      [
        env "receiver0" "an honest receiver with choice bit 0; true iff it decrypts m0 (or the sender aborts)"
          (fun g -> P.env_ot_receiver g.vg g.cg g.vgg false);
        env "receiver1" "an honest receiver with choice bit 1" (fun g -> P.env_ot_receiver g.vg g.cg g.vgg true);
      ];
    claims =
      (let three_over_n = ("3/n", fun (g : I.group) -> Q.make (Z.of_int 3) (Z.of_int g.order)) in
       [
         Always { w = { env = "receiver0"; sys = "real" }; expect = "true"; doc = "the receiver learns m0" };
         Always { w = { env = "receiver1"; sys = "real" }; expect = "true"; doc = "the receiver learns m1" };
         Adv_bound { env = "receiver0"; x = "real"; y = "ideal"; bound = three_over_n; doc = "adv_ot_rc" };
         Adv_bound { env = "receiver1"; x = "real"; y = "ideal"; bound = three_over_n; doc = "adv_ot_rc" };
       ]);
    instances = [ (I.Qr, 7) ];
  }

(* ------------------------------------------------------------------------ *)
(* Secure channel with the PRF-based symmetric scheme                       *)

(* Messages are 0..2 and nonces 0..1; keys are group elements; the
   ciphertext type is nonce × message; the PRF is [toy_prf]. *)
let n_msg = 3
let n_nonce = 2

type ske = {
  mt : P.fin_val_type; ms : P.fin_val_type_struct;
  nt : P.fin_val_type; ns : P.fin_val_type_struct;
  kt : P.fin_val_type; ks : P.fin_val_type_struct;
  ct : P.fin_val_type; cs : P.fin_val_type_struct;
  prf : P.pRF_struct; scheme : P.sYM_struct;
}

let ske (g : I.group) =
  let mt = I.fin_type n_msg and ms = I.fin_struct n_msg in
  let nt = I.fin_type n_nonce and ns = I.fin_struct n_nonce in
  let kt = P.vg_fvt g.vg and ks = P.vg_fvts g.vg g.cg in
  let ct = P.prod_fvt nt mt and cs = P.prod_fvts nt mt ns ms in
  let prf = P.toy_prf (Z.of_int n_msg) in
  let inh = Obj.magic Z.zero in
  let scheme = P.prf_sym_struct kt nt mt ks ns ms prf inh inh inh in
  { mt; ms; nt; ns; kt; ks; ct; cs; prf; scheme }

let ske_case =
  let w f (g : I.group) = f g (ske g) in
  {
    name = "ske";
    doc = "secure channel with the PRF-based symmetric scheme (secure_channel/ske_*, prf/)";
    systems =
      [
        sys "real" "(F_KE_lazy_alice ||ᵣ F_OAUTH) ∘f CHAN  (REAL_SKE)"
          (w (fun g k -> P.rEAL_SKE g.vg g.cg g.vgg k.mt k.ct k.ms k.cs k.scheme));
        sys "ideal" "CHAN_SIM ∘f F_CHAN  (SIM_IDEAL_SKE)"
          (w (fun g k -> P.sIM_IDEAL_SKE g.vg g.cg k.mt k.ct k.ms k.cs k.scheme));
        sys "game1" "the protocol with the real encryption oracle (GAME1)"
          (w (fun g k -> P.gAME1 g.vg g.cg g.vgg k.mt k.ct k.ms k.cs k.scheme));
        sys "game2" "the protocol with the ideal encryption oracle (GAME2)"
          (w (fun g k -> P.gAME2 g.vg g.cg g.vgg k.mt k.ct k.ms k.cs k.scheme));
        sys "enc-real" "enc_real: the real encryption oracle"
          (w (fun _ k -> P.enc_real k.kt k.ks k.mt k.ms k.ct k.cs k.scheme));
        sys "enc-ideal" "enc_ideal: the ideal encryption oracle"
          (w (fun _ k -> P.enc_ideal k.kt k.ks k.mt k.ms k.ct k.cs k.scheme));
        sys "prf-real" "prf_real: the real PRF game" (w (fun _ k -> P.prf_real k.kt k.nt k.mt k.ks k.ns k.ms k.prf));
        sys "prf-ideal" "prf_ideal: a lazily sampled random function" (w (fun _ k -> P.prf_ideal k.nt k.mt k.ns k.ms));
      ];
    envs =
      [
        env "honest" "Alice sends a uniform message, Bob receives; true iff he gets it" (fun g obs ->
            let k = ske g in
            P.env_ske_honest k.mt k.ms obs);
        env "peek" "true iff the ciphertext's pad is zero" (fun g obs ->
            let k = ske g in
            P.env_ske_peek k.mt k.ms obs);
        env "red-peek" "RED_SKE peek: the reduction to the encryption oracles" (fun g obs ->
            let k = ske g in
            P.rED_SKE g.vg g.cg g.vgg k.mt k.ms (P.env_ske_peek k.mt k.ms obs));
        env "prf-peek" "λ F, RED_SKE peek (red_prf F): the reduction to the PRF games" (fun g obs ->
            let k = ske g in
            P.rED_SKE_PRF g.vg g.cg g.vgg k.nt k.mt k.ns k.ms (P.env_ske_peek k.mt k.ms obs));
      ];
    claims =
      [
        Always { w = { env = "honest"; sys = "real" }; expect = "true"; doc = "the channel delivers the message" };
        Always { w = { env = "honest"; sys = "ideal" }; expect = "true"; doc = "the ideal channel delivers it" };
        Adv_zero { env = "peek"; x = "real"; y = "game1"; doc = "REAL_SKE ≈ GAME1 (ske_sec_chan_prf.v)" };
        Adv_zero { env = "peek"; x = "game2"; y = "ideal"; doc = "GAME2 ≈ SIM_SKE ∘f IDEAL_SKE (ske_sec_chan_ideal_prf.v)" };
        Adv_le
          { lhs = ("peek", "real", "ideal"); rhs = ("red-peek", "enc-real", "enc-ideal"); doc = "adv_SKE" };
        Adv_le
          { lhs = ("peek", "real", "ideal"); rhs = ("prf-peek", "prf-real", "prf-ideal"); doc = "adv_schan_prf" };
      ];
    instances = [ (I.Zpx, 5); (I.Zpx, 7) ];
  }

let cases = [ dhke; schan; dhke_chan; add; add3; auth; ot_rc; ske_case ]

let find_case name =
  match List.find_opt (fun c -> c.name = name) cases with
  | Some c -> c
  | None ->
      failwith
        (Printf.sprintf "unknown case study %S (known: %s)" name (String.concat ", " (List.map (fun c -> c.name) cases)))

let find_sys c name =
  match List.find_opt (fun s -> s.s_name = name) c.systems with
  | Some s -> s
  | None ->
      failwith
        (Printf.sprintf "%s: unknown system %S (known: %s)" c.name name
           (String.concat ", " (List.map (fun s -> s.s_name) c.systems)))

let find_env c name =
  match List.find_opt (fun e -> e.e_name = name) c.envs with
  | Some e -> e
  | None ->
      failwith
        (Printf.sprintf "%s: unknown environment %S (known: %s)" c.name name
           (String.concat ", " (List.map (fun e -> e.e_name) c.envs)))

(* The program [env sys], with fresh observers. *)
let program c (g : I.group) ~env ~sys =
  Machine.reset_observers ();
  let memo = Hashtbl.create 8 in
  let obs tag =
    match Hashtbl.find_opt memo tag with
    | Some f -> f
    | None ->
        let f = Machine.new_observer tag in
        Hashtbl.add memo tag f;
        f
  in
  let e = (find_env c env).e_build g obs in
  let s = (find_sys c sys).s_build g in
  App (Val e, Val s)
