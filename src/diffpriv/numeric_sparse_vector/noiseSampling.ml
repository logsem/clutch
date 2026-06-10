(** Sampling Noise from the ClutchProcjet https://github.com/logsem/clutch *)
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

(* differential privacy style inverted scale *)
let laplace_discrete (scale : Q.t) (mean : int) =
  let (num, den) = Q.num_den_of_q scale in
  let x = discreteLaplaceSample den num in
  x + mean

(** End of noize sampling from clutch *)
