(* Companion file to [awkward_probabilistic.v]. We construct a context that
   compares the functions considered in the lemma `refinement_prob_resample`.
   Load this file in OCaml, and run `test rhs_id` or `test rhs_xor`. *)

let () = Random.init 0
let flip = Random.bool
let xor x y = if x then not y else y

let lhs h = h () ; flip ()

let rhs_template k =
  let x = ref true in
  fun f -> let b = flip () in
           x := b ;
           f () ;
           k !x

let rhs_id = rhs_template (fun x -> x)
let rhs_xor = rhs_template (fun x -> xor (flip ()) x)

(* Call `lhs_or_rhs` with a thunk `f_obs` that records and reveals the result
   of running `f` as `obs`, then compare the result of `lhs_or_rhs` to `obs`.
   For `rhs_id`, `!obs` will always equal `v`, while for `rhs_xor` and for
   `lhs`, `!obs` and `v` are independently sampled. *)
let ctx_template lhs_or_rhs f =
  let obs = ref false in
  let f_obs () =
    let res = f (fun x -> x) in
    obs := res in
  let v = lhs_or_rhs f_obs in
  v = !obs

let ctx f = ctx_template f f

let n = ref 10_000
(* Print the distribution of observing f for n times. *)
let observe f =
  let c = ref 0 in
  for x = 1 to !n do if f () then incr c done ;
  let t = (100 * !c / !n) in
  Printf.printf "true : %d%% \tfalse : %d%%\n" t (100 - t)

(* Compare rhs (should be rhs_id or rhs_xor) and lhs using ctx. *)
let test rhs =
  print_endline "testing rhs:" ;
  observe (fun () -> ctx rhs) ;
  print_endline "testing lhs:" ;
  observe (fun () -> ctx lhs) ;
