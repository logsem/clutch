(* Exact rationals and confidence intervals for sampled proportions. *)

let q_to_string q =
  let f = Q.to_float q in
  if Z.equal (Q.den q) Z.one then Q.to_string q else Printf.sprintf "%s ≈ %.6f" (Q.to_string q) f

(* Wilson score interval for k successes out of n, at normal quantile z. *)
let wilson ~z k n =
  if n = 0 then (0., 1.)
  else
    let n' = float n and p = float k /. float n in
    let z2 = z *. z in
    let centre = (p +. (z2 /. (2. *. n'))) /. (1. +. (z2 /. n')) in
    let half = z /. (1. +. (z2 /. n')) *. sqrt ((p *. (1. -. p) /. n') +. (z2 /. (4. *. n' *. n'))) in
    (Float.max 0. (centre -. half), Float.min 1. (centre +. half))

(* Newcombe's hybrid score interval for the difference p1 - p2 of two
   independent proportions. *)
let newcombe ~z (k1, n1) (k2, n2) =
  let p1 = float k1 /. float n1 and p2 = float k2 /. float n2 in
  let l1, u1 = wilson ~z k1 n1 and l2, u2 = wilson ~z k2 n2 in
  let d = p1 -. p2 in
  (d -. sqrt (((p1 -. l1) ** 2.) +. ((u2 -. p2) ** 2.)), d +. sqrt (((u1 -. p1) ** 2.) +. ((p2 -. l2) ** 2.)))

(* An interval for |p1 - p2|. *)
let abs_interval (lo, hi) =
  if lo >= 0. then (lo, hi) else if hi <= 0. then (-.hi, -.lo) else (0., Float.max (-.lo) hi)

(* The normal quantile for a two-sided confidence level. *)
let z_of_confidence c =
  match c with
  | 0.9 -> 1.6449
  | 0.95 -> 1.96
  | 0.99 -> 2.5758
  | 0.999 -> 3.2905
  | _ -> invalid_arg "confidence must be 0.9, 0.95, 0.99 or 0.999"
