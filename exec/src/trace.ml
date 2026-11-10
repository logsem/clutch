(* Rendering of machine events: text (protocol or execution level), JSON,
   Mermaid sequence diagrams, and a line diff of two protocol traces. *)
open Syn
open Machine

(* [View]: what the environment sees, i.e. its observations and the result. *)
type level = View | Proto | Exec

let in_level level ev =
  match (level, ev) with
  | Exec, _ -> true
  | Proto, (Step _ | Heap _) -> false
  | Proto, _ -> true
  | View, (Observe _ | Result _ | Stuck_at _) -> true
  | View, _ -> false

let indent d = String.make (2 * min d 24) ' '
let v = Pp.value

let mode_s = function OS -> "one-shot" | MS -> "multi-shot"
let hs_s = function Deep -> "deep" | Shallow -> "shallow"

(* The description of an event, without step number and actor. *)
let describe ev =
  match ev with
  | Step { rule; redex; _ } -> Printf.sprintf "%-14s %s" rule redex
  | New_effect { name; label; _ } -> Printf.sprintf "effect %s ↦ %s#%s" name name (Z.to_string label)
  | Perform { eff; payload; mode; hs; _ } ->
      Printf.sprintf "▶ %s %s   (%s %s handler)" eff (Pp.atom payload) (hs_s hs) (mode_s mode)
  | Resume { target; arg; one_shot; _ } ->
      Printf.sprintf "◀ resume %s with %s%s" target (v arg)
        (match one_shot with Some r -> Printf.sprintf "   (cont@ℓ%s)" (Z.to_string r) | None -> "")
  | Return { handler; ret; _ } -> Printf.sprintf "↩ %s returns %s to its return clause" handler (v ret)
  | Sample { range; outcome; tape; _ } ->
      Printf.sprintf "⚄ sample %s from 0..%s%s" (Z.to_string outcome)
        (Z.to_string (Z.pred range))
        (match tape with Some l -> Printf.sprintf " on tape ι%s" (Z.to_string l) | None -> "")
  | Observe { tag; obs; _ } -> Printf.sprintf "◆ %s %s" tag (v obs)
  | Heap { op; loc; v = w; _ } -> Printf.sprintf "%s ℓ%s %s" op (Z.to_string loc) (v w)
  | Result w -> "result " ^ v w
  | Stuck_at m -> "STUCK: " ^ m

let actor_depth = function
  | Step { actor; depth; _ }
  | New_effect { actor; depth; _ }
  | Perform { actor; depth; _ }
  | Resume { actor; depth; _ }
  | Return { actor; depth; _ }
  | Sample { actor; depth; _ }
  | Observe { actor; depth; _ }
  | Heap { actor; depth; _ } ->
      (actor, depth)
  | Result _ | Stuck_at _ -> ("main", 0)

let text_line (n, ev) =
  let actor, depth = actor_depth ev in
  Printf.sprintf "%7d  %-16s %s%s" n actor (indent depth) (describe ev)

(* Without step numbers, for diffs. *)
let plain_line (_, ev) =
  let actor, depth = actor_depth ev in
  Printf.sprintf "%-16s %s%s" actor (indent depth) (describe ev)

(* ------------------------------------------------------------------------ *)
(* JSON                                                                     *)

let json_event (n, ev) : Yojson.Safe.t =
  let actor, depth = actor_depth ev in
  let base kind fields = `Assoc ([ ("step", `Int n); ("kind", `String kind); ("actor", `String actor); ("depth", `Int depth) ] @ fields) in
  let vs w = `String (v w) and zs z = `String (Z.to_string z) in
  match ev with
  | Step { rule; redex; _ } -> base "step" [ ("rule", `String rule); ("redex", `String redex) ]
  | New_effect { name; label; _ } -> base "effect" [ ("name", `String name); ("label", zs label) ]
  | Perform { eff; payload; mode; hs; handler; _ } ->
      base "perform"
        [ ("effect", `String eff); ("payload", vs payload); ("handler", `String handler);
          ("mode", `String (mode_s mode)); ("semantics", `String (hs_s hs)) ]
  | Resume { target; arg; one_shot; _ } ->
      base "resume"
        ([ ("target", `String target); ("value", vs arg) ]
        @ match one_shot with Some r -> [ ("flag", zs r) ] | None -> [])
  | Return { handler; ret; _ } -> base "return" [ ("handler", `String handler); ("value", vs ret) ]
  | Sample { range; outcome; tape; _ } ->
      base "sample"
        ([ ("outcome", zs outcome); ("range", zs range) ]
        @ match tape with Some l -> [ ("tape", zs l) ] | None -> [])
  | Observe { tag; obs; _ } -> base "observe" [ ("tag", `String tag); ("value", vs obs) ]
  | Heap { op; loc; v = w; _ } -> base "heap" [ ("op", `String op); ("loc", zs loc); ("value", vs w) ]
  | Result w -> base "result" [ ("value", vs w) ]
  | Stuck_at m -> base "stuck" [ ("reason", `String m) ]

(* ------------------------------------------------------------------------ *)
(* Mermaid                                                                  *)

let mermaid events =
  let parts = ref [] in
  let ids = Hashtbl.create 16 in
  let base a = match String.index_opt a '/' with Some i -> String.sub a 0 i | None -> a in
  let id a =
    let a = base a in
    match Hashtbl.find_opt ids a with
    | Some i -> i
    | None ->
        let i = Printf.sprintf "P%d" (Hashtbl.length ids) in
        Hashtbl.add ids a i;
        parts := (i, a) :: !parts;
        i
  in
  let clean s = String.map (function '#' -> '.' | ';' -> ',' | '\n' -> ' ' | c -> c) s in
  let body = Buffer.create 1024 in
  let add fmt = Printf.ksprintf (fun s -> Buffer.add_string body ("  " ^ s ^ "\n")) fmt in
  ignore (id "main");
  List.iter
    (fun (_, ev) ->
      match ev with
      | Perform { actor; eff; payload; handler; _ } ->
          let a = id actor and h = id handler in
          add "%s->>%s: %s %s" a h (clean eff) (clean (Pp.atom payload))
      | Resume { actor; target; arg; _ } -> add "%s-->>%s: resume %s" (id actor) (id target) (clean (v arg))
      | Return { actor; handler; ret; _ } -> add "%s-->>%s: return %s" (id actor) (id handler) (clean (v ret))
      | Sample { actor; range; outcome; _ } ->
          add "Note over %s: sample %s from 0..%s" (id actor) (Z.to_string outcome) (Z.to_string (Z.pred range))
      | Observe { actor; tag; obs; _ } -> add "%s->>%s: %s %s" (id actor) (id "env") (clean tag) (clean (v obs))
      | Result w -> add "Note over %s: result %s" (id "main") (clean (v w))
      | Stuck_at m -> add "Note over %s: STUCK %s" (id "main") (clean m)
      | _ -> ())
    events;
  let b = Buffer.create 2048 in
  Buffer.add_string b "sequenceDiagram\n";
  List.iter (fun (i, a) -> Buffer.add_string b (Printf.sprintf "  participant %s as %s\n" i (clean a))) (List.rev !parts);
  Buffer.add_buffer b body;
  Buffer.contents b

(* ------------------------------------------------------------------------ *)
(* Line diff (longest common subsequence)                                   *)

let diff a b =
  let a = Array.of_list a and b = Array.of_list b in
  let n = Array.length a and m = Array.length b in
  let t = Array.make_matrix (n + 1) (m + 1) 0 in
  for i = n - 1 downto 0 do
    for j = m - 1 downto 0 do
      t.(i).(j) <- (if a.(i) = b.(j) then t.(i + 1).(j + 1) + 1 else max t.(i + 1).(j) t.(i).(j + 1))
    done
  done;
  let out = ref [] in
  let rec go i j =
    if i < n && j < m && a.(i) = b.(j) then (out := ("  " ^ a.(i)) :: !out; go (i + 1) (j + 1))
    else if j < m && (i = n || t.(i).(j + 1) >= t.(i + 1).(j)) then (out := ("+ " ^ b.(j)) :: !out; go i (j + 1))
    else if i < n then (out := ("- " ^ a.(i)) :: !out; go (i + 1) j)
  in
  go 0 0;
  List.rev !out
