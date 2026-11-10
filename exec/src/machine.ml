(* A small-step machine for probblaze ([theories/prob_eff_lang/probblaze/semantics.v]).

   One call of [step] performs exactly one step of [prim_step]: it refocuses
   (descends into the next redex, or plugs a value into the enclosing frame)
   and then performs one [head_step].  Substitution, label substitution,
   frame filling and the operator evaluations are the extracted Rocq
   functions.  Sampling does not draw randomness: it returns a [Branch],
   and the driver ([Explore]) decides the outcome, so the same machine runs
   seeded, replays a recorded run, or enumerates all runs.

   The evaluation context is a stack of frames, innermost first.  Besides
   the frames of the semantics it holds two kinds of markers that the
   semantics does not see: [Clause a] while the clause of handler [a] runs,
   and [Resumed a] while a continuation captured from actor [a] runs.  They
   only serve to attribute events to an actor in traces; they are skipped
   when a value returns through them and are never part of a continuation
   value.  With [~validate:true], every step is compared with the step of
   the extracted reference decomposition [decomp]/[fill]. *)
open Syn
module P = Probblaze
module ZMap = Map.Make (Z)

type actor = string

type mframe = F of frame | Clause of actor | Resumed of actor

(* What the trace needs to know about a captured continuation: its frames
   with markers (outermost first) and the actor that performed the effect. *)
type kinfo = { marked : mframe list; performer : actor }

type tape = { bound : z; contents : z list }

type state = {
  heap : value ZMap.t;
  tapes : tape ZMap.t;
  next_label : z;
  names : string ZMap.t;  (* effect label -> the effect name it was created for *)
  os_konts : kinfo ZMap.t;  (* one-shot continuation flag location -> info *)
  ms_konts : (frame list * kinfo) list;  (* multi-shot continuation (by identity) -> info *)
}

type config = { stack : mframe list; focus : expr; st : state; steps : int }

let empty_state =
  {
    heap = ZMap.empty;
    tapes = ZMap.empty;
    next_label = Z.zero;
    names = ZMap.empty;
    os_konts = ZMap.empty;
    ms_konts = [];
  }

let init ?(st = empty_state) e = { stack = []; focus = e; st; steps = 0 }

(* [fresh] of stdpp on [gset Z]: the maximum of [0] and the successors of
   the keys. *)
let fresh_key m =
  match ZMap.max_binding_opt m with None -> Z.zero | Some (k, _) -> Z.max Z.zero (Z.succ k)

let to_nat z = if Z.sign z <= 0 then Z.zero else z

(* ------------------------------------------------------------------------ *)
(* Events                                                                   *)

type event =
  | Step of { n : int; actor : actor; depth : int; rule : string; redex : string }
  | New_effect of { actor : actor; depth : int; name : string; label : z }
  | Perform of {
      actor : actor;
      depth : int;
      eff : string;
      payload : value;
      handler : actor;
      mode : mode;
      hs : handler_semantics;
    }
  | Resume of { actor : actor; depth : int; target : actor; arg : value; one_shot : z option }
  | Return of { actor : actor; depth : int; handler : actor; ret : value }
  | Sample of { actor : actor; depth : int; range : z; outcome : z; tape : z option; index : int }
  | Observe of { actor : actor; depth : int; tag : string; obs : value }
  | Heap of { actor : actor; depth : int; op : string; loc : z; v : value }
  | Result of value
  | Stuck_at of string

let label_name st l =
  match ZMap.find_opt l st.names with
  | Some s -> s ^ "#" ^ Z.to_string l
  | None -> "#" ^ Z.to_string l

let actor_of stack =
  let rec go = function
    | [] -> "main"
    | (Clause a | Resumed a) :: _ -> a
    | F _ :: r -> go r
  in
  go stack

let depth_of stack =
  List.fold_left (fun n f -> match f with F _ -> n | _ -> n + 1) 0 stack

(* Push a marker; a marker directly on top of another one makes the lower one
   unreachable (nothing runs between them), so it is replaced. *)
let push_mark m = function
  | (Clause _ | Resumed _) :: rest -> m :: rest
  | stack -> m :: stack

(* ------------------------------------------------------------------------ *)
(* Observers: closures handed to the environments as [obs t].               *)

let observers : (value * string) list ref = ref []
let obs_param = BNamed "@obs"

let new_observer tag =
  let f = RecV (BAnon, obs_param, Val unit_v) in
  observers := (f, tag) :: !observers;
  f

let reset_observers () = observers := []

let observer_tag f =
  match f with
  | RecV (BAnon, BNamed "@obs", _) -> (
      match List.find_opt (fun (o, _) -> o == f) !observers with
      | Some (_, t) -> Some t
      | None -> None)
  | _ -> None

(* ------------------------------------------------------------------------ *)
(* Decomposition                                                            *)

(* [decomp_frame] of the semantics, except that a handler is always entered:
   an effect is matched with its handler when the [do] is reached (the
   nearest handler with its label), which is the handler at which
   [decomp_frame] stops. *)
let decomp1 e =
  let noval e f = match e with Val _ -> None | _ -> Some (f, e) in
  match e with
  | App (e1, e2) -> ( match e2 with Val v -> noval e1 (AppLCtx v) | _ -> Some (AppRCtx e1, e2))
  | UnOp (op, e) -> noval e (UnOpCtx op)
  | BinOp (op, e1, e2) -> (
      match e2 with Val v -> noval e1 (BinOpLCtx (op, v)) | _ -> Some (BinOpRCtx (op, e1), e2))
  | If (e0, e1, e2) -> noval e0 (IfCtx (e1, e2))
  | Pair (e1, e2) -> ( match e2 with Val v -> noval e1 (PairLCtx v) | _ -> Some (PairRCtx e1, e2))
  | Fst e -> noval e FstCtx
  | Snd e -> noval e SndCtx
  | InjL e -> noval e InjLCtx
  | InjR e -> noval e InjRCtx
  | Case (e0, e1, e2) -> noval e0 (CaseCtx (e1, e2))
  | AllocN (e1, e2) -> (
      match e2 with Val v -> noval e1 (AllocNLCtx v) | _ -> Some (AllocNRCtx e1, e2))
  | Load e -> noval e LoadCtx
  | Store (e1, e2) -> ( match e2 with Val v -> noval e1 (StoreLCtx v) | _ -> Some (StoreRCtx e1, e2))
  | AllocTape e -> noval e AllocTapeCtx
  | Rand (e1, e2) -> ( match e2 with Val v -> noval e1 (RandLCtx v) | _ -> Some (RandRCtx e1, e2))
  | Do (EffLabel l, e) -> noval e (DoCtx l)
  | Handle (hs, m, EffLabel l, e0, e1, e2) -> noval e0 (HandleCtx (hs, m, l, e1, e2))
  | _ -> None

type focus_result = Final of value | Redex of mframe list * expr

let rec refocus stack focus =
  match focus with
  | Val v -> (
      match stack with
      | [] -> Final v
      | (Clause _ | Resumed _) :: rest -> refocus rest focus
      | F f :: rest -> refocus rest (P.fill_frame f focus))
  | _ -> (
      match decomp1 focus with
      | Some (f, e') -> refocus (F f :: stack) e'
      | None -> Redex (stack, focus))

(* The whole program denoted by a configuration. *)
let to_expr stack focus =
  List.fold_left (fun e f -> match f with F f -> P.fill_frame f e | _ -> e) focus stack

(* ------------------------------------------------------------------------ *)
(* Head steps                                                               *)

type outcome =
  | Next of config
  | Branch of z * (int -> config)  (* number of outcomes, and the step for each *)
  | Done of value * config
  | Stuck of string * config

exception Stuck_exn of string

let stuck fmt = Printf.ksprintf (fun s -> raise (Stuck_exn s)) fmt

(* The head steps that do not involve the evaluation context, as in
   [head_step].  Returns the rule, and either the reduct with its state or
   the number of outcomes of a sampling step with the reduct per outcome. *)
type head =
  | Det of string * expr * state
  | Rand_of of z * z option * (int -> expr * state)

let names_of st l = label_name st l

let head_simple st e =
  match e with
  | Rec (f, x, b) -> Det ("RecS", Val (RecV (f, x, b)), st)
  | Pair (Val v1, Val v2) -> Det ("PairS", Val (PairV (v1, v2)), st)
  | InjL (Val v) -> Det ("InjLS", Val (InjLV v), st)
  | InjR (Val v) -> Det ("InjRS", Val (InjRV v), st)
  | App (Val (RecV (f, x, body) as fv), Val v2) ->
      Det ("BetaS", P.val_subst' x v2 (P.val_subst' f fv body), st)
  | UnOp (op, Val v) -> (
      match P.un_op_eval op v with
      | Some w -> Det ("UnOpS", Val w, st)
      | None -> stuck "%s applied to %s" (Pp.un_op op) (Pp.value v))
  | BinOp (op, Val v1, Val v2) -> (
      match P.bin_op_eval op v1 v2 with
      | Some w -> Det ("BinOpS", Val w, st)
      | None -> stuck "%s applied to %s and %s" (Pp.bin_op op) (Pp.value v1) (Pp.value v2))
  | If (Val (LitV (LitBool b)), e1, e2) -> Det ((if b then "IfTrueS" else "IfFalseS"), (if b then e1 else e2), st)
  | Fst (Val (PairV (v1, _))) -> Det ("FstS", Val v1, st)
  | Snd (Val (PairV (_, v2))) -> Det ("SndS", Val v2, st)
  | Case (Val (InjLV v), e1, _) -> Det ("CaseLS", App (e1, Val v), st)
  | Case (Val (InjRV v), _, e2) -> Det ("CaseRS", App (e2, Val v), st)
  | AllocN (Val (LitV (LitInt n)), Val v) ->
      let n = to_nat n in
      if Z.sign n <= 0 then stuck "allocation of %s cells" (Z.to_string n);
      let l = fresh_key st.heap in
      let rec cells i h = if Z.geq i n then h else cells (Z.succ i) (ZMap.add (Z.add l i) v h) in
      Det ("AllocNS", Val (LitV (LitLoc l)), { st with heap = cells Z.zero st.heap })
  | Load (Val (LitV (LitLoc l))) -> (
      match ZMap.find_opt l st.heap with
      | Some v -> Det ("LoadS", Val v, st)
      | None -> stuck "load from unallocated ℓ%s" (Z.to_string l))
  | Store (Val (LitV (LitLoc l)), Val w) ->
      if ZMap.mem l st.heap then
        Det ("StoreS", Val unit_v, { st with heap = ZMap.add l w st.heap })
      else stuck "store to unallocated ℓ%s" (Z.to_string l)
  | Rand (Val (LitV (LitInt n)), Val (LitV LitUnit)) ->
      Rand_of (Z.succ (to_nat n), None, fun i -> (Val (int_v i), st))
  | AllocTape (Val (LitV (LitInt z))) ->
      let l = fresh_key st.tapes in
      Det
        ( "AllocTapeS",
          Val (LitV (LitLbl l)),
          { st with tapes = ZMap.add l { bound = to_nat z; contents = [] } st.tapes } )
  | Rand (Val (LitV (LitInt n)), Val (LitV (LitLbl l))) -> (
      match ZMap.find_opt l st.tapes with
      | None -> stuck "sampling from unallocated tape ι%s" (Z.to_string l)
      | Some { bound; contents } ->
          if Z.equal bound (to_nat n) then
            match contents with
            | x :: rest ->
                Det
                  ( "RandTapeS",
                    Val (LitV (LitInt x)),
                    { st with tapes = ZMap.add l { bound; contents = rest } st.tapes } )
            | [] -> Rand_of (Z.succ bound, Some l, fun i -> (Val (int_v i), st))
          else Rand_of (Z.succ (to_nat n), Some l, fun i -> (Val (int_v i), st)))
  | Effect (s, e) ->
      let l = st.next_label in
      Det
        ( "EffectS",
          P.lbl_subst s l e,
          { st with next_label = Z.succ l; names = ZMap.add l s st.names } )
  | Var x -> stuck "free variable %s" x
  | Do (EffName s, _) -> stuck "do: effect name %s is not bound by an enclosing [effect]" s
  | Handle (_, _, EffName s, _, _, _) ->
      stuck "handle: effect name %s is not bound by an enclosing [effect]" s
  | _ -> stuck "no rule applies to %s" (Pp.expr ~names:(names_of st) e)

(* ------------------------------------------------------------------------ *)
(* The reference step, for validation                                       *)

(* [head_step] on the redex found by the extracted [decomp], with the
   sampling outcome [choice]; the handler cases use the extracted [to_eff]
   and [ectx_labels] as in the semantics. *)
let reference_step st e choice =
  let k, r = P.decomp e in
  let r', st' =
    match r with
    | App (Val (KontV k'), Val w) -> (P.fill k' (Val w), st)
    | App (Val (ContV (loc, k')), Val w) -> (
        match ZMap.find_opt loc st.heap with
        | Some (LitV (LitBool true)) ->
            (P.fill k' (Val w), { st with heap = ZMap.add loc (bool_v false) st.heap })
        | _ -> stuck "reference: resumption of a used one-shot continuation")
    | Handle (hs, m, EffLabel l, e1, e2, e3) -> (
        match P.to_eff e1 with
        | None -> (
            match e1 with
            | Val v -> (App (e3, Val v), st)
            | _ -> stuck "reference: handler body is neither a value nor an effect")
        | Some ((l', v), k') ->
            if not (Z.equal l l') then stuck "reference: effect of another label";
            if List.exists (Z.equal l') (P.ectx_labels k') then
              stuck "reference: effect caught inside";
            let k'' = match hs with Deep -> HandleCtx (hs, m, l, e2, e3) :: k' | Shallow -> k' in
            (match m with
            | MS -> (App (App (e2, Val v), Val (KontV k'')), st)
            | OS ->
                let r = fresh_key st.heap in
                ( App (App (e2, Val v), Val (ContV (r, k''))),
                  { st with heap = ZMap.add r (bool_v true) st.heap } )))
    | _ -> (
        match head_simple st r with
        | Det (_, r', st') -> (r', st')
        | Rand_of (_, _, f) -> f (Option.value choice ~default:0))
  in
  (P.fill k r', st')

let validate_step before before_st after =
  let expect, st' = reference_step before_st before None in
  let got = to_expr after.stack after.focus in
  if got <> expect then
    failwith
      (Printf.sprintf "validation failed at step %d: the machine's expression differs from the reference" after.steps);
  if not (ZMap.equal ( = ) st'.heap after.st.heap) then
    failwith (Printf.sprintf "validation failed at step %d: heaps differ" after.steps)

let validate_branch before before_st i after =
  let expect, st' = reference_step before_st before (Some i) in
  let got = to_expr after.stack after.focus in
  if got <> expect || not (ZMap.equal ( = ) st'.heap after.st.heap) then
    failwith (Printf.sprintf "validation failed at sampling step %d" after.steps)

(* ------------------------------------------------------------------------ *)
(* The machine step                                                         *)

let step ?emit ?(validate = false) cfg =
  let emitting = Option.is_some emit in
  let ev_at n f = match emit with Some g -> g n (f ()) | None -> () in
  match refocus cfg.stack cfg.focus with
  | Final v ->
      ev_at cfg.steps (fun () -> Result v);
      Done (v, { cfg with stack = []; focus = Val v })
  | Redex (stack, e) -> (
      let st = cfg.st in
      let n = cfg.steps + 1 in
      let ev f = ev_at n f in
      let actor () = actor_of stack in
      let depth () = depth_of stack in
      let trace_step rule =
        if emitting then
          ev (fun () ->
              Step { n; actor = actor (); depth = depth (); rule; redex = Pp.expr ~names:(names_of st) e })
      in
      let before = if validate then Some (to_expr stack e) else None in
      let finish c =
        (match before with Some b -> validate_step b st c | None -> ());
        Next c
      in
      try
        match e with
        (* An effect: the nearest enclosing handler with its label handles it. *)
        | Do (EffLabel l, Val v) -> (
            let rec split above = function
              | [] -> None
              | F (HandleCtx (hs, m, l', e2, e3)) :: rest when Z.equal l l' -> Some (above, (hs, m, e2, e3), rest)
              | fr :: rest -> split (fr :: above) rest
            in
            match split [] stack with
            | None -> stuck "unhandled effect %s" (label_name st l)
            | Some (above, (hs, m, e2, e3), rest) ->
                (* [above] is outermost first, as continuations are. *)
                let k = List.filter_map (function F f -> Some f | _ -> None) above in
                let hframe = HandleCtx (hs, m, l, e2, e3) in
                let k', marked = match hs with Deep -> (hframe :: k, F hframe :: above) | Shallow -> (k, above) in
                let performer = actor_of stack in
                let handler = label_name st l in
                trace_step (match m with MS -> "HandleMSEffS" | OS -> "HandleOSEffS");
                ev (fun () ->
                    Perform { actor = performer; depth = depth (); eff = handler; payload = v; handler; mode = m; hs });
                let info = { marked; performer } in
                let kv, st' =
                  match m with
                  | MS -> (KontV k', { st with ms_konts = (k', info) :: st.ms_konts })
                  | OS ->
                      let r = fresh_key st.heap in
                      ( ContV (r, k'),
                        { st with heap = ZMap.add r (bool_v true) st.heap; os_konts = ZMap.add r info st.os_konts } )
                in
                finish
                  {
                    stack = push_mark (Clause handler) rest;
                    focus = App (App (e2, Val v), Val kv);
                    st = st';
                    steps = n;
                  })
        (* The return clause. *)
        | Handle (_, _, EffLabel l, Val v, _, e3) ->
            let handler = label_name st l in
            trace_step "HandleRetS";
            ev (fun () -> Return { actor = actor (); depth = depth (); handler; ret = v });
            finish
              { stack = push_mark (Clause (handler ^ "/ret")) stack; focus = App (e3, Val v); st; steps = n }
        (* Resuming a continuation. *)
        | App (Val (KontV k), Val w) ->
            let info = List.find_opt (fun (k', _) -> k' == k) st.ms_konts in
            let resumer = actor () in
            let marked, performer =
              match info with
              | Some (_, i) -> (i.marked, i.performer)
              | None -> (List.map (fun f -> F f) k, resumer)
            in
            trace_step "KontS";
            ev (fun () -> Resume { actor = resumer; depth = depth (); target = performer; arg = w; one_shot = None });
            finish
              {
                stack = List.rev_append marked (push_mark (Resumed performer) stack);
                focus = Val w;
                st;
                steps = n;
              }
        | App (Val (ContV (r, k)), Val w) -> (
            match ZMap.find_opt r st.heap with
            | Some (LitV (LitBool true)) ->
                let resumer = actor () in
                let marked, performer =
                  match ZMap.find_opt r st.os_konts with
                  | Some i -> (i.marked, i.performer)
                  | None -> (List.map (fun f -> F f) k, resumer)
                in
                trace_step "ContS";
                ev (fun () ->
                    Resume { actor = resumer; depth = depth (); target = performer; arg = w; one_shot = Some r });
                finish
                  {
                    stack = List.rev_append marked (push_mark (Resumed performer) stack);
                    focus = Val w;
                    st = { st with heap = ZMap.add r (bool_v false) st.heap };
                    steps = n;
                  }
            | _ -> stuck "one-shot continuation cont@ℓ%s resumed twice" (Z.to_string r))
        | _ -> (
            (match e with
            | App (Val f, Val v) -> (
                match observer_tag f with
                | Some tag -> ev (fun () -> Observe { actor = actor (); depth = depth (); tag; obs = v })
                | None -> ())
            | _ -> ());
            match head_simple st e with
            | Det (rule, e', st') ->
                trace_step rule;
                (if emitting then
                   match (e, e') with
                   | AllocN _, Val (LitV (LitLoc l)) ->
                       ev (fun () ->
                           Heap { actor = actor (); depth = depth (); op = "alloc"; loc = l; v = ZMap.find l st'.heap })
                   | Store (Val (LitV (LitLoc l)), Val w), _ ->
                       ev (fun () -> Heap { actor = actor (); depth = depth (); op = "store"; loc = l; v = w })
                   | Load (Val (LitV (LitLoc l))), Val w ->
                       ev (fun () -> Heap { actor = actor (); depth = depth (); op = "load"; loc = l; v = w })
                   | Effect (s, _), _ ->
                       ev (fun () -> New_effect { actor = actor (); depth = depth (); name = s; label = st.next_label })
                   | _ -> ());
                finish { stack; focus = e'; st = st'; steps = n }
            | Rand_of (range, tape, f) ->
                Branch
                  ( range,
                    fun i ->
                      let e', st' = f i in
                      trace_step (match tape with None -> "RandNoTapeS" | Some _ -> "RandTapeEmptyS");
                      ev (fun () ->
                          Sample { actor = actor (); depth = depth (); range; outcome = Z.of_int i; tape; index = i });
                      let c = { stack; focus = e'; st = st'; steps = n } in
                      (match before with Some b -> validate_branch b st i c | None -> ());
                      c ))
      with Stuck_exn msg ->
        ev (fun () -> Stuck_at msg);
        Stuck (msg, { cfg with stack; focus = e }))
