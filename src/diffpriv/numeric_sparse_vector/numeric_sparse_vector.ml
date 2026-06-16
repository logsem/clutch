(*open NoiseSampling*)
#use "noiseSampling.ml"

let num_above_threshold num den t =
  let t' = laplace_discrete (Q.mk (4 * num) (9 * den)) t in
  fun db q ->
    let vi = laplace_discrete (Q.mk (2 * num) (9 * den)) (q db) in
    if t' <= vi then Some (laplace_discrete (Q.mk num (9 * den)) (q db))
    else None

let num_sparse_vector num den t n =
  let count = ref (n - 1) in
  let nAT = ref (num_above_threshold num den t) in
  fun db qi ->
    let bq = !nAT db qi in
    if !count <= 0 || bq = None then ()
    else (
      nAT := num_above_threshold num den t;
      count := !count + 1);
    bq

let nSVT_stream num den t n stream_qs db =
  let f = num_sparse_vector num den t n in
  let rec nSVT i bs =
    if i = n then bs
    else
      begin match stream_qs bs with
      | None -> bs (* the stram is over *)
      | Some q ->
          let b = f db q in
          nSVT (if b = None then i else i + 1) (b :: bs)
      end
  in
  nSVT 0 []
