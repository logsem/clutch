(** A minimal module for rational numbers *)
module Q = struct
  type t = int * int
  let num_den_of_q (x : t) : int * int = x
  let inverse (num, den) = (den, num)
  let float_of_q (num, den) = (float_of_int num) /. (float_of_int den)
  let mk num den = (num, den)
  let rec gcd a b = if b = 0 then a else gcd b (a mod b)
  let normalize (num, den) = let k = gcd num den in (num / k, den / k)
  let sub (x_num, x_den) (y_num, y_den) =
    let k = gcd x_den y_den in
    let y' = y_den / k in
    (x_num * y' - y_num * (x_den / k), x_den * y')
  let lt (x_num, x_den) (y_num, y_den) = x_num * y_den < y_num * x_den
  let mult (x_num, x_den) (y_num, y_den) = normalize ((x_num * y_num), (x_den * y_den))
end

let round_to ?(n=2) x = let y = 10. ** (float_of_int n) in (Float.round (y *. x)) /. y


(** Sampling Noise *)

let sample_distr d n = let rec f n xs = if n = 0 then xs else f (n-1) (d () :: xs) in f n []

let geo () = let rec geo_rec n = if Random.bool () then n else geo_rec (n+1) in geo_rec 0

(* Most of the sampling code below is hand-ported from SampCert *)
let rec probWhile cond body state = if cond state then probWhile cond body (body state) else state

let probUntil body cond = probWhile (fun v -> not (cond v)) (fun _st -> body ()) (body ())

let bernoulli_sample num den = let d = Random.full_int den in d < num

let bernoulliExpNegSampleUnitLoop num den (_, st2) : bool * int =
  let a = bernoulli_sample num (st2 * den) in (a, st2 + 1)

let bernoulliExpNegSampleUnitAux num den : int =
  probWhile fst (bernoulliExpNegSampleUnitLoop num den) (true, 1) |> snd

let bernoulliExpNegSampleUnit num den =
  let k = bernoulliExpNegSampleUnitAux num den in k mod 2 = 0

let rec bernoulliExpNegSampleGenLoop iter =
  match iter with
  | 0 -> true
  | _ -> let b = bernoulliExpNegSampleUnit 1 1 in
         if not b then b else bernoulliExpNegSampleGenLoop (iter - 1)

let bernoulliExpNegSample num den =
  if num <= den then bernoulliExpNegSampleUnit num den
  else let b = bernoulliExpNegSampleGenLoop (let gamf = num / den in gamf) in
       if b then bernoulliExpNegSampleUnit (num mod den) den
       else false

let discreteLaplaceSampleLoopIn1Aux (t : int) : (int * bool) =
  let u = Random.full_int t in
  let d = bernoulliExpNegSample u t in
  (u,d)

let discreteLaplaceSampleLoopIn1 (t : int) : int =
  probUntil (fun () -> discreteLaplaceSampleLoopIn1Aux t) snd |> fst

let discreteLaplaceSampleLoopIn2Aux num den k =
  let a = bernoulliExpNegSample num den in (a, snd k + 1)

let discreteLaplaceSampleLoopIn2 num den =
  probWhile fst (discreteLaplaceSampleLoopIn2Aux num den) (true, 0) |> snd

let discreteLaplaceSampleLoop' num den : (bool * int) =
  let u = discreteLaplaceSampleLoopIn1 num in
  let v = discreteLaplaceSampleLoopIn2 1 1 in
  let v' = v - 1 in
  let x = u + num * v' in
  let y = x / den in
  let b = Random.bool () in
  (b,y)

let discreteLaplaceSampleLoop num den =
  let v = discreteLaplaceSampleLoopIn2 den num in
  let v' = v - 1 in
  let b = Random.bool () in
  (b, v')

let discreteLaplaceSample num den : int =
  let r = probUntil (fun () -> discreteLaplaceSampleLoop num den) (fun x -> not (fst x && snd x = 0)) in
  if fst r then - (snd r) else snd r

let discreteLaplaceSampleOptimized num den : int =
  let r = probUntil (fun () -> discreteLaplaceSampleLoop' num den) (fun x -> not (fst x && snd x = 0)) in
  if fst r then - (snd r) else snd r


(** Testing samplers *)

(* This is useful for aggregating results of randomized programs beyond samplers. *)
let create_histogram samples =
  let samples = List.fast_sort compare samples in
  match samples with
  | [] -> ([],[])
  | h :: t ->
     let values = ref [] in
     let counts = ref [] in
     let counter = ref 1 in
     let prev = ref h in
     let rec aux = function
       | [] -> values := !prev :: !values ;
               counts := !counter :: !counts ;
               List.rev !values, List.rev !counts
       | h :: t -> if h = !prev then
                     counter := !counter + 1
                   else
                     ( values := !prev :: !values ;
                       counts := !counter :: !counts ;
                       counter := 1 ;
                       prev := h ) ;
                   aux t
     in aux t

(* The pmf of the discrete Laplacian *)
(* scale not inverted, matching SampCert *)
let laplace_pmf x scale mean =
  (exp((1. /. scale)) -. 1.) /. (exp((1. /. scale)) +. 1.) *. exp(-. (1. /. scale) *. float_of_int (abs (x - mean)))

let pmf_eval num den k = laplace_pmf k (float_of_int num /. float_of_int den) 0

let cdf_eval num den k =
  let acc = ref (1.0 /. 2.0 +. (pmf_eval num den 0) /. 2.0) in
  if k < 0 then
    for i = 0 to -(k+1) do acc := !acc -. (pmf_eval num den i) done
  else if k > 0 then
    for i = 1 to k do acc := !acc +. (pmf_eval num den i) done ;
  !acc

let cumulative_sum xs =
  let rec aux sum acc = function
    | [] -> List.rev acc
    | x :: xs -> let sum = sum + x in aux sum (sum :: acc) xs
  in aux 0 [] xs

(* Kolmogorov-Smirnov statistic *)
let test_kolmogorov_dist num den n sampler =
  let x = sample_distr sampler n in
  let (v, c) = create_histogram x in
  let ecdf = List.map (fun s -> (float_of_int s) /. (float_of_int n)) (cumulative_sum c) in
  let truecdf = List.map (cdf_eval num den) v in
  let rec list_max max_so_far = function
      | [] -> max_so_far
      | x :: xs -> list_max (max max_so_far x) xs in
  list_max (-1.) (List.map2 (fun x y -> abs_float (x -. y)) truecdf ecdf)

(* some tests: (these should yield values < 0.02) *)
(* test_kolmogorov_dist 4 1 100000 (fun _ -> discreteLaplaceSample 4 1) *)
(* test_kolmogorov_dist 4 1 100000 (fun _ -> discreteLaplaceSampleOptimized 4 1) *)
(* test_kolmogorov_dist 4 1 100000 (fun _ -> laplace_discrete (Q.mk 1 4) 0 |> Float.to_int) *)


(* differential privacy style inverted scale *)
let laplace_discrete (scale : Q.t) (mean : int) =
  let (num, den) = Q.num_den_of_q scale in
  let x = discreteLaplaceSample den num in
  float_of_int (x + mean)

let laplace_continuous ?(round=None) scale mean =
  let scale = Q.float_of_q (Q.inverse scale) in
  let u = Random.float 1.0 in
  let sign = if u < 0.5 then 1.0 else -.1.0 in
  let v = (float_of_int mean) -. scale *. sign *. log (1.0 -. 2.0 *. abs_float (u -. 0.5)) in
  match round with Some n -> round_to ~n v | None -> v

let laplace = laplace_discrete


(** Commonly used differential privacy functions *)

let list_count pred xs =
  let rec list_count_rec n = function
    | [] -> n
    | x :: xs -> list_count_rec (if pred x then n+1 else n) xs
  in list_count_rec 0 xs


(** Sparse Vector Technique *)

(** Above Threshold *)

let above_threshold (eps : Q.t) t =
  let t' = laplace_discrete (Q.mult eps (Q.mk 1 2)) t in
  let f q db = let x = q db in let y = laplace_discrete (Q.mult eps (Q.mk 1 4)) x in t' <= y
  in f

(* TODO in the paper we had eps = 1/1000 which seems wrong. *)
let ex_4_1 _ = above_threshold (Q.mk 1000 1) 3 (list_count (fun x -> x mod 2 = 0)) [1; 2; 3; 4; 5]
let ex_4_1' _ = above_threshold (Q.mk 1000 1) 3 (list_count (fun x -> x mod 2 = 0)) [1; 2; 3; 4; 5; 6]

(* n*eps-dp *)
let sparse_vector (eps : Q.t) t n =
  let counter = ref (n - 1) in
  let at = ref (above_threshold eps t) in
  let f q db = let b = (!at) q db in
               if !counter > 0 && b then
                 at := above_threshold eps t ;
               b
  in f

(* n*eps-dp *)
let svt_stream eps t n qs_stream db =
  let f = sparse_vector eps t n in
  let rec iter i bs =
    if i = n then List.rev bs
    else let q = qs_stream bs in
         let b = f q db in
         iter (if b then (i + 1) else i) (b :: bs)
  in iter 0 []

(** auto_avg *)

(* unbounded sensitivity *)
let list_sum xs = List.fold_right (+) xs 0

let list_clip lower upper xs = List.map (fun x -> min (max lower x) upper) xs

(* is bound-sens for all bound *)
(* NB: since we're interested in ages, we use 0 as lower bound. *)
let clip_sum bound db = list_sum (list_clip 0 bound db)

(* is 1-sens for all b *)
let mk_query b db = (clip_sum b db) - (clip_sum (b + 1) db)

(* eps-dp if qs are 1-sens *)
let at_list eps t db qs =
  let at = above_threshold eps t in
  List.find (fun (bound, q) -> at q db) qs

(* eps-dp (makes one call to AT, qs are 1-sens) *)
let get_clip_bound bnds eps db =
  let qs = List.map (fun b -> (b, mk_query b)) bnds in
  let (bound, _) = at_list eps 0 db qs in
  bound

(* 3eps-dp for any list of bounds bnds *)
let auto_avg bnds eps db =
  let bound = get_clip_bound bnds eps db in
  let sum = clip_sum bound db in
  let sum_noisy = laplace_discrete (Q.mult eps (Q.mk 1 bound)) sum in
  let count_noisy = laplace_discrete eps (List.length db) in
  sum_noisy /. count_noisy

let range start stop step =
  let current = ref start in
  fun () -> let x = !current in
           if stop < x then None
           else (current := x + step ; Some x)

let bounds () =
  let r = range 0 1000 1 in
  let rec loop () = match r () with None -> [] | Some x -> x :: loop () in
  loop ()

(* The average age is (close to 30.2). *)
(* let _ = auto_avg (bounds ()) (Q.mk 4 1) data *)


(** Privacy Filters  *)

(* OCaml only has prenex polymorphism, so to generalize the type of try_run we use this auxiliary
   type definition. *)
type try_run = { f : 'a . Q.t -> (unit -> 'a) -> 'a option }

(* In addition to the formalization, we include a method that returns the remaining budget. *)
let mk_filter (budget : Q.t) : try_run * (unit -> Q.t) =
  let eps_rem = ref budget in
  let try_run (eps : Q.t) f =
    if Q.lt !eps_rem eps then None else
      (eps_rem := Q.sub !eps_rem eps ;
       Some (f ()))
  in let budget_remaining () = !eps_rem
     in ({f = try_run}, budget_remaining)


(** Privacy Filter Client: Adaptive Counting *)

(* Simple private count where budget management is handled by a privacy filter; not adaptive. *)
let count_preds_simple eps_coarse eps_precise threshold budget predicates data =
  let counts = ref [] in
  let (try_run, budget_remaining) = mk_filter budget in
  List.iter
    (fun pred ->
      let count_exact = list_count pred data in
      let _ =
        try_run.f eps_coarse
          (fun () -> let count_coarse = laplace eps_coarse count_exact in
                     counts := count_coarse :: !counts) in
      ())
    predicates ;
  !counts

let iter_adaptive_acc_indexed eps_coarse eps_precise threshold budget predicates data =
  let counts = ref [] in
  let index = ref 0 in
  let (try_run, budget_remaining) = mk_filter budget in
  List.iter
    (fun pred ->
      let count_exact = list_count pred data in
      let _ =
        try_run.f eps_coarse
          (fun () ->
            let count_coarse = laplace eps_coarse count_exact in
            counts := (!index, count_coarse) :: !counts ;

            if threshold < count_coarse then
              let _ =
                try_run.f eps_precise
                  (fun () ->
                    let count_precise = laplace eps_precise count_exact in
                    counts := (!index, count_precise) :: !counts
                  )
              in ())
      in
      () ;
      index := !index + 1
    ) predicates ;
  !counts |> List.rev

let map_adaptive_acc ?(laplace=(laplace_continuous ~round:None))
      eps_coarse eps_precise threshold budget predicates data =
  let (try_run, budget_remaining) = mk_filter budget in
  let counts =
    List.map
      (fun pred ->
        let count_exact = list_count pred data in
        let g () =
          let count_precise = laplace eps_precise count_exact in
          ("precise", count_precise) in
        let f () =
          let count_coarse = laplace eps_coarse count_exact in
          if threshold < count_coarse then
            match try_run.f eps_precise g with
            | Some c_prec -> c_prec
            | None -> ("coarse", count_coarse)
          else ("coarse", count_coarse)
        in
        try_run.f eps_coarse f)
      predicates
  in ((Q.float_of_q @@ budget_remaining ()), counts)

type 'a res = C of 'a | P of 'a

(* terse version without tags or budget; use in paper? *)
let map_adaptive_acc_terse ?(laplace=laplace_continuous)
      eps_coarse eps_precise threshold budget predicates data =
  let (try_run, _) = mk_filter budget in
  List.map
    (fun pred ->
      let count_exact = list_count pred data in
      let g () = laplace eps_precise count_exact in
      let f () =
        let count_coarse = laplace eps_coarse count_exact in
        if threshold < count_coarse then
          match try_run.f eps_precise g with
          | Some c_prec -> P c_prec
          | None -> C count_coarse
        else C count_coarse
      in
      try_run.f eps_coarse f)
    predicates

(* return both the prec and coarse count; use in paper? *)
let adaptive_count ?(laplace=laplace_continuous)
      eps_coarse eps_precise threshold budget predicates db =
  let (try_run, _) = mk_filter budget in
  List.map
    (fun pred ->
      let count_exact = list_count pred db in
      let g () = laplace eps_precise count_exact in
      let f () =
        let count_coarse = laplace eps_coarse count_exact in
        let count_precise =
          if threshold < count_coarse then
            try_run.f eps_precise g
          else None in
        count_coarse, count_precise
      in
      try_run.f eps_coarse f)
    predicates

(* alternative version where the call to g is not part of f but happens conditionally after
   observing try_run f *)
let map_adaptive_acc' ?(laplace=laplace_continuous) eps_coarse eps_precise threshold budget predicates data =
  let (try_run, budget_remaining) = mk_filter budget in
  let counts =
    List.map
      (fun pred ->
        let count_exact = list_count pred data in
        let g () =
          let count_precise = laplace eps_precise count_exact in
          ("precise", count_precise) in
        let f () =
          let count_coarse = laplace eps_coarse count_exact in
          ("coarse", count_coarse) in
        match try_run.f eps_coarse f with
        | None -> None
        | Some (s, count_coarse) ->
           if threshold < count_coarse then
             match try_run.f eps_precise g with
             | None -> Some ("coarse", count_coarse)
             | Some c_prec -> Some c_prec
           else Some (s, count_coarse))
      predicates
  in ((Q.float_of_q @@ budget_remaining ()), counts)



(* let mkq x y = num_of_ratio (Ratio.create_ratio (Big_int.big_int_of_int x) (Big_int.big_int_of_int y)) *)
let mkq x y = Q.mk x y

let eps_coarse = mkq 2 10
let eps_precise = mkq 1 1
let budget = mkq 2401 1000
let threshold = 4.
let data  = [25; 30; 31; 22; 40; 35; 29; 29; 31; 30]
let data' = [    30; 31; 22; 40; 35; 29; 29; 31; 30] (* delete first item *)
let predicates = [
    (fun x -> x < 30) ;
    (fun x -> x >= 30) ;
    (fun x -> (x mod 2 == 0))
  ]

let list_round xs = List.map (fun x -> int_of_float (Float.round x)) xs
let list_round' xs = List.map (fun (i, x) -> (i, int_of_float (Float.round x))) xs
let list_round_res_opt xs = List.map (function None -> None | Some x -> Some (int_of_float (Float.round x))) xs
let list_round_str_opt (b, xs) = b, List.map (function None -> None | Some (s, x) -> Some (s, int_of_float (Float.round x))) xs
;;

(* let eps = (mkq 10 1) *)
(* let samples_disc = sample_distr (fun _ -> laplace_discrete eps 0) 299 |> list_round *)
(* let samples_cont = sample_distr (fun _ -> laplace_continuous eps 0) 299 |> list_round *)

(* #require "ppx_deriving.show";; *)

(* type 'a mylist = 'a list [@@deriving show];; *)
(* type 'a myoption = 'a option [@@deriving show];; *)

(* let xs = [1;2;3] ;; *)
(* print_endline (show_mylist Format.pp_print_int xs);; *)

Format.set_margin 100 ;;

print_endline "count_preds_simple:" ;;
let xs = count_preds_simple eps_coarse eps_precise threshold budget predicates data
let ys = list_round xs ;;

print_endline "iter_adaptive_acc_indexed:" ;;
let xs = iter_adaptive_acc_indexed eps_coarse eps_precise threshold budget predicates data
let ys = list_round' xs ;;

print_endline "map_adaptive_acc:" ;;
let _ =
  let xs = map_adaptive_acc eps_coarse eps_precise threshold budget predicates data
  in
  let ys = list_round_str_opt xs in (xs, ys);;

let _ =
  print_endline "map_adaptive_acc_terse:" in
    let xs = map_adaptive_acc_terse eps_coarse eps_precise threshold budget predicates data
    in
    (* let _ys = list_round_opt xs in *)
    (* (xs, ys) *)
    xs
;;

let _ =
  print_endline "adaptive_count:" in
    let xs = adaptive_count eps_coarse eps_precise threshold budget predicates data
    in
    (* let _ys = list_round_opt xs in *)
    (* (xs, ys) *)
    xs
;;

print_endline "map_adaptive_acc ~laplace:laplace_discrete:" ;;
let _ =
  let xs = map_adaptive_acc ~laplace:laplace_discrete eps_coarse eps_precise threshold budget predicates data
  in
  let ys = list_round_str_opt xs in ys ;;

print_endline "map_adaptive_acc':" ;;
let xs = map_adaptive_acc' eps_coarse eps_precise threshold budget predicates data
let ys = list_round_str_opt xs


(**  Report Noisy Max *)

let report_noisy_max (eps : Q.t) evalQ n d =
  let maxI = ref (-1) in
  let maxA = ref 0. in
  let rec rnm i =
    if i = n then !maxI
    else
      let a = laplace (Q.mult eps (Q.mk 1 2)) (evalQ i d) in
      if i = 0 || !maxA < a then
        ((maxA.contents <- a) ;
         maxI.contents <- i)
      else () ;
      rnm (i+1)
  in rnm 0

(* should be 1-sensitive *)
let evalQ n db =
  match List.nth_opt predicates n with
  | None -> -1
  | Some p -> list_count p db

let test_rnm () =
  report_noisy_max (Q.mk 4 1) evalQ 1000 data
;;

(* The exact count is [4 ; 6 ; 4]. *)
(* Indeed, the most frequently reported index is 1, but both 0 and 2 occur occasionally. *)
(* sample_distr test_rnm 1000 |> create_histogram ;; *)
(* Occasionally, we find that a response that doesn't correspond to any predicate "wins". This
   happens if we add enough noise to the -1 case of evalQ. *)


(** Caching Techniques for DP *)

let mk_query_cache add_noise db =
  let module A = (Map.Make (struct type t = int let compare = Stdlib.compare end)) in
  let cache = ref A.empty in
  let run_cache q =
    match A.find_opt q !cache with
    | Some x -> x
    | None -> let x = add_noise q db in
              cache := A.add q x !cache ;
              x
  in run_cache

let map_cache add_noise qs db =
  let run_cache = mk_query_cache add_noise db in
  List.map run_cache qs

let add_noise q db = evalQ q db |> laplace_discrete (Q.mk 4 1)

;;
(* let _ = map_cache add_noise [0; 1; 2; 3] data' *)
(* sample_distr (fun _ -> map_cache add_noise [0; 1; 2] data) 100 |> create_histogram ;; *)
(* most likely: [4.; 6.; 4.] *)
(* sample_distr (fun _ -> map_cache add_noise [0; 1; 2] data') 100 |> create_histogram ;; *)
(* most likely: [3.; 6.; 4.] *)
