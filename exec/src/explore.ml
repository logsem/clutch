(* Drivers: one run under a choice strategy, exhaustive enumeration of all
   runs with exact probabilities, and independent sampled runs. *)
open Syn

type result = Value of value | Stuck of string | Out_of_steps

let result_key = function
  | Value v -> Pp.value v
  | Stuck m -> "stuck: " ^ m
  | Out_of_steps -> "out of steps"

let is_true = function Value (LitV (LitBool true)) -> true | _ -> false

(* A strategy picks an outcome in [0, range) for the [index]-th sampling. *)
type strategy = index:int -> range:z -> int

let random_below st range =
  if Z.fits_int range then Random.State.full_int st (Z.to_int range)
  else invalid_arg "sampling range too large for this tool"

let seeded ~seed ~run =
  let st = Random.State.make [| seed; run |] in
  fun ~index:_ ~range -> random_below st range

(* Replay a recorded list of outcomes, then continue with [fallback]. *)
let replay outcomes (fallback : strategy) =
  let arr = Array.of_list outcomes in
  fun ~index ~range ->
    if index < Array.length arr then begin
      let i = arr.(index) in
      if i < 0 || Z.leq range (Z.of_int i) then
        invalid_arg (Printf.sprintf "choice %d: outcome %d is outside 0..%s" index i (Z.to_string (Z.pred range)));
      i
    end
    else fallback ~index ~range

type run = {
  result : result;
  final : Machine.config;
  choices : (int * z) list;  (* outcome and range, in order *)
}

let run ?emit ?(validate = false) ?(max_steps = max_int) ~(strategy : strategy) cfg =
  let choices = ref [] in
  let index = ref 0 in
  let rec loop cfg =
    if cfg.Machine.steps >= max_steps then (Out_of_steps, cfg)
    else
      match Machine.step ?emit ~validate cfg with
      | Next c -> loop c
      | Branch (range, k) ->
          let i = strategy ~index:!index ~range in
          incr index;
          choices := (i, range) :: !choices;
          loop (k i)
      | Done (v, c) -> (Value v, c)
      | Stuck (m, c) -> (Stuck m, c)
  in
  let result, final = loop cfg in
  { result; final; choices = List.rev !choices }

(* ------------------------------------------------------------------------ *)
(* Exact enumeration                                                        *)

type dist = (string * (result * Q.t)) list  (* by result key, sorted *)

type enum_stats = { leaves : int; max_choices : int; total_steps : int }

exception Too_many_leaves of int

let enumerate ?(validate = false) ?(max_steps = max_int) ?(max_leaves = 1_000_000) cfg =
  let tbl = Hashtbl.create 16 in
  let leaves = ref 0 and max_choices = ref 0 and total_steps = ref 0 in
  let add r p =
    let key = result_key r in
    let _, q = Option.value (Hashtbl.find_opt tbl key) ~default:(r, Q.zero) in
    Hashtbl.replace tbl key (r, Q.add q p)
  in
  let rec go cfg prob depth =
    let leaf r c =
      incr leaves;
      if !leaves > max_leaves then raise (Too_many_leaves !leaves);
      total_steps := !total_steps + c.Machine.steps;
      if depth > !max_choices then max_choices := depth;
      add r prob
    in
    if cfg.Machine.steps >= max_steps then leaf Out_of_steps cfg
    else
      match Machine.step ~validate cfg with
      | Next c -> go c prob depth
      | Done (v, c) -> leaf (Value v) c
      | Stuck (m, c) -> leaf (Stuck m) c
      | Branch (range, k) ->
          if not (Z.fits_int range) then raise (Too_many_leaves max_int);
          let n = Z.to_int range in
          let p = Q.div prob (Q.of_int n) in
          for i = 0 to n - 1 do
            go (k i) p (depth + 1)
          done
  in
  go cfg Q.one 0;
  let d = Hashtbl.fold (fun k v acc -> (k, v) :: acc) tbl [] |> List.sort compare in
  (d, { leaves = !leaves; max_choices = !max_choices; total_steps = !total_steps })

let prob_true (d : dist) =
  List.fold_left (fun acc (_, (r, q)) -> if is_true r then Q.add acc q else acc) Q.zero d

(* ------------------------------------------------------------------------ *)
(* Sampling                                                                 *)

type counts = { n : int; by_key : (string * (result * int)) list; steps : int }

let sample ?(validate = false) ?(max_steps = max_int) ~seed ~n cfg =
  let tbl = Hashtbl.create 16 in
  let steps = ref 0 in
  for j = 0 to n - 1 do
    let r = run ~validate ~max_steps ~strategy:(seeded ~seed ~run:j) cfg in
    steps := !steps + r.final.steps;
    let key = result_key r.result in
    let _, c = Option.value (Hashtbl.find_opt tbl key) ~default:(r.result, 0) in
    Hashtbl.replace tbl key (r.result, c + 1)
  done;
  let by_key = Hashtbl.fold (fun k v acc -> (k, v) :: acc) tbl [] |> List.sort compare in
  { n; by_key; steps = !steps }

let count_true c = List.fold_left (fun acc (_, (r, k)) -> if is_true r then acc + k else acc) 0 c.by_key
