#use "numeric_sparse_vector.ml"
#use "db_query.ml"

let mw x f v eta =
  let r = Hashtbl.copy f in
  if v >= c_query f x then Hashtbl.iter (fun a b -> Hashtbl.replace r a (1. -. b)) r;
  Hashtbl.iter (fun a b -> Hashtbl.replace r a ((exp ((-.eta) *. b)) *. (Hashtbl.find x a))) r;
  norm r;
  r

let abs_f x =
  if x<0. then -.x else x

let oPMW size domaine db unif stream_q nb_q num den alpha beta =
  let c = 4. *. (log (float_of_int (List.length domaine))) /.  (alpha *. alpha) in
  let t = 0.01 *. (float_of_int size) *. ((float_of_int den) *. 18. *. c *. (log (2. *. nb_q) +. log (4. *. c) -. log beta)) /. ((float_of_int num) *. (float_of_int size)) in
  let f = num_sparse_vector num den (int_of_float t) (int_of_float c) db in
  let rec aux i bs distrib =
    match stream_q bs with
    | None -> (bs, distrib, i, c, t) (* no more queries we stop *)
    | Some q -> (
        if i >= int_of_float c then
          (* we retrun only from the distribution *)
          aux i ((abs_f (c_query q db -. c_query q distrib)) :: bs) distrib
        else (
          let a = ref None in
          (match f (fun x' -> int_of_float ((float_of_int size) *. (c_query q x' -. c_query q distrib))) with
          | None -> (
              match f (fun x' -> int_of_float ((float_of_int size) *. (c_query q distrib -. c_query q x'))) with
              | None -> ()
              | Some v -> a := Some (c_query q distrib -. float_of_int v /. (float_of_int size)))
          | Some v -> a := Some (c_query q distrib +. float_of_int v /. (float_of_int size)));
          match !a with
          | None -> aux i ((abs_f (c_query q db -. c_query q distrib)) :: bs) distrib
          | Some v ->
              aux (i + 1) ((abs_f (c_query q db -. v)) :: bs) (mw distrib q v  (alpha /. 2.))))
  in
  aux 0 [] unif

let oPMW_gif size domaine db unif stream_q nb_q num den alpha beta file =
  let c = 4. *. (log (float_of_int (List.length domaine))) /.  (alpha *. alpha) in
  let t = 0.01 *. (float_of_int size) *. ((float_of_int den) *. 18. *. c *. (log (2. *. nb_q) +. log (4. *. c) -. log beta)) /. ((float_of_int num) *. (float_of_int size)) in
  let f = num_sparse_vector num den (int_of_float t) (int_of_float c) db in
  let rec aux i bs distrib =
    match stream_q bs with
    | None -> (bs, distrib, i, c, t) (* no more queries we stop *)
    | Some q -> (
        if i >= int_of_float c then
          (* we retrun only from the distribution *)
          aux i ((abs_f (c_query q db -. c_query q distrib)) :: bs) distrib
        else (
          let a = ref None in
          (match f (fun x' -> int_of_float ((float_of_int size) *. (c_query q x' -. c_query q distrib))) with
          | None -> (
              match f (fun x' -> int_of_float ((float_of_int size) *. (c_query q distrib -. c_query q x'))) with
              | None -> ()
              | Some v -> a := Some (c_query q distrib -. float_of_int v /. (float_of_int size)))
          | Some v -> a := Some (c_query q distrib +. float_of_int v /. (float_of_int size)));
          match !a with
          | None -> aux i ((abs_f (c_query q db -. c_query q distrib)) :: bs) distrib
          | Some v ->
              write_db distrib file i;
              aux (i + 1) ((abs_f (c_query q db -. v)) :: bs) (mw distrib q v  (alpha /. 2.))))
  in
  aux 0 [] unif
