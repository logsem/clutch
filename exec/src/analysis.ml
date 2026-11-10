(* Output distributions of worlds and advantages, exact when the runs can be
   enumerated within a budget, sampled otherwise. *)
open Syn

type settings = {
  max_steps : int;
  max_leaves : int;  (* enumeration budget; 0 forces sampling *)
  samples : int;
  seed : int;
  confidence : float;
  validate : bool;
}

type estimate =
  | Exact of Explore.dist * Explore.enum_stats
  | Sampled of Explore.counts

let world c g ~env ~sys = Machine.init (Scenarios.program c g ~env ~sys)

let estimate s c g ~env ~sys =
  let exact () =
    if s.max_leaves <= 0 then None
    else
      try
        let d, st =
          Explore.enumerate ~validate:s.validate ~max_steps:s.max_steps ~max_leaves:s.max_leaves
            (world c g ~env ~sys)
        in
        Some (Exact (d, st))
      with Explore.Too_many_leaves _ -> None
  in
  match exact () with
  | Some e -> e
  | None ->
      Sampled
        (Explore.sample ~validate:s.validate ~max_steps:s.max_steps ~seed:s.seed ~n:s.samples
           (world c g ~env ~sys))

(* [check] asks for the same world in several claims. *)
let cache : (string * string * string * string * int, estimate) Hashtbl.t = Hashtbl.create 64

let estimate_cached s c (g : Instances.group) ~env ~sys =
  let key = (c.Scenarios.name, env, sys, Instances.kind_name g.kind, g.p) in
  match Hashtbl.find_opt cache key with
  | Some e -> e
  | None ->
      let e = estimate s c g ~env ~sys in
      Hashtbl.add cache key e;
      e

let describe_estimate = function
  | Exact (d, st) ->
      let lines =
        List.map (fun (k, (_, q)) -> Printf.sprintf "    %-24s %s" k (Stats.q_to_string q)) d
      in
      Printf.sprintf "  exact, by enumeration of %d runs (at most %d samplings per run, %d steps in total)\n%s"
        st.leaves st.max_choices st.total_steps (String.concat "\n" lines)
  | Sampled c ->
      let lines =
        List.map
          (fun (k, (_, n)) -> Printf.sprintf "    %-24s %d/%d = %.6f" k n c.n (float n /. float c.n))
          c.by_key
      in
      Printf.sprintf "  sampled, %d independent runs (%d steps in total)\n%s" c.n c.steps (String.concat "\n" lines)

(* Non-boolean outcomes make an advantage on [true] meaningless. *)
let non_boolean = function
  | Exact (d, _) -> List.filter (fun (k, _) -> k <> "true" && k <> "false") d |> List.map fst
  | Sampled c -> List.filter (fun (k, _) -> k <> "true" && k <> "false") c.by_key |> List.map fst

type pr = Pr_exact of Q.t | Pr_sampled of int * int * (float * float)

let pr_true s = function
  | Exact (d, _) -> Pr_exact (Explore.prob_true d)
  | Sampled c ->
      let k = Explore.count_true c in
      Pr_sampled (k, c.n, Stats.wilson ~z:(Stats.z_of_confidence s.confidence) k c.n)

let pr_to_string = function
  | Pr_exact q -> Stats.q_to_string q
  | Pr_sampled (k, n, (lo, hi)) -> Printf.sprintf "%d/%d = %.6f  [%.6f, %.6f]" k n (float k /. float n) lo hi

type adv = Adv_exact of Q.t | Adv_sampled of float * (float * float)

let adv s a b =
  match (pr_true s a, pr_true s b) with
  | Pr_exact p, Pr_exact q -> Adv_exact (Q.abs (Q.sub p q))
  | pa, pb ->
      let counts = function
        | Pr_sampled (k, n, _) -> (k, n)
        | Pr_exact q ->
            (* An exact probability as a large sample, for the interval. *)
            let n = 1_000_000 in
            (int_of_float (Float.round (Q.to_float q *. float n)), n)
      in
      let (k1, n1) = counts pa and (k2, n2) = counts pb in
      let d = Float.abs ((float k1 /. float n1) -. (float k2 /. float n2)) in
      Adv_sampled (d, Stats.abs_interval (Stats.newcombe ~z:(Stats.z_of_confidence s.confidence) (k1, n1) (k2, n2)))

let adv_to_string = function
  | Adv_exact q -> Stats.q_to_string q
  | Adv_sampled (d, (lo, hi)) -> Printf.sprintf "%.6f  [%.6f, %.6f]" d lo hi

let adv_bounds = function Adv_exact q -> (Q.to_float q, Q.to_float q) | Adv_sampled (_, i) -> i
