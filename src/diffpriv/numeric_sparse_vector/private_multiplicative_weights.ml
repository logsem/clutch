#use "numeric_sparse_vector.ml"
#use "db_query.ml"

let norm htbl =
  let sum = Hashtbl.fold (fun _ b acc -> acc +. b) htbl 0. in
  Hashtbl.iter (fun a b -> Hashtbl.replace htbl a (b /. sum)) htbl

let mw x f v eta =
  let r = Hashtbl.copy f in
  if v >= c_query f x then Hashtbl.iter (fun a b -> Hashtbl.replace r a (1. -. b)) r;
  Hashtbl.iter (fun a b -> Hashtbl.replace r a ((exp ((-.eta) *. b)) *. (Hashtbl.find x a))) r;
  norm r;
  (* Printf.printf "v: %f | eat : %f\n" v eta; *)
  (* aff_bq f; *)
  (* Printf.printf "--Pre:\n"; *)
  (* aff_db x; *)
  (* Printf.printf "--Post:\n"; *)
  (* aff_db r; *)
  (* Printf.printf "-------\n\n-------\n"; *)
  r

let oPMW size domaine db unif stream_q nb_q num den alpha beta =
  let precision = 1_000. in
  let c = 4. *. (log (float_of_int (List.length domaine))) /.  (alpha *. alpha) in
  let t = 0.05 *. precision *. ((float_of_int den) *. 18. *. c *. (log (2. *. nb_q) +. log (4. *. c) -. log beta)) /. ((float_of_int num) *. (float_of_int size)) in
  let f = num_sparse_vector num den (int_of_float t) (int_of_float c) db in
  let nb_upd = ref 0 in
  let rec aux i bs distrib =
    match stream_q bs with
    | None -> (bs, distrib, !nb_upd) (* No more queries we stop *)
    | Some q -> (
        if i >= int_of_float c then
          (* we retrun only from the distribution *)
          aux i ((c_query q distrib) :: bs) distrib
        else (
          let a = ref None in
          (* Printf.printf "q:%f\n" (c_query q db -. c_query q distrib); *)
          (match f (fun x' -> int_of_float (precision *. (c_query q x' -. c_query q distrib))) with
          | None -> (
              match f (fun x' -> int_of_float (precision *. (c_query q distrib -. c_query q x'))) with
              | None -> ()
              | Some v -> a := Some (c_query q distrib -. float_of_int v /. precision))
          | Some v -> a := Some (c_query q distrib +. float_of_int v /. precision));
          match !a with
          | None -> aux i ((c_query q distrib) :: bs) distrib
          | Some v ->
              (* Printf.printf "v: %f\n" v; *)
              nb_upd := !nb_upd + 1;
              (*distrib := mw distrib q v (alpha /. 2.) get_db_i;*)
              aux (i + 1) (v :: bs) (mw distrib q v  (alpha /. 2.))))
  in
  Printf.printf "c: %f\nt: %f\n" c t;
  aux 0 [] unif
