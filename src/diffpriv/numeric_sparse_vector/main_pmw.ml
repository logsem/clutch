(*open SparseV*)

#use "private_multiplicative_weights.ml"

#use "db_sampling.ml"

let rec pow m n =
  if n = 0 then 1 else (
    if n mod 2 = 0 then pow (m*m) (n/2)
    else m * pow (m*m) ((n-1)/2) )


let aff_lst l =
  List.iter (fun x -> Printf.printf "%d|" x) l;
  Printf.printf "\n"

let aff_l_op l =
  List.fold_left
    (fun _ y -> match y with
       | None -> Printf.printf "⊥\n"
       | Some n -> Printf.printf "%d\n" n) () l

let count_above t l =
  Array.fold_left (fun x y -> x + (if y>t then 1 else 0)) 0 l

let () =
  let k = 10 in
  let i = 511 in
  let stream_query =
    let a = ref 1000 in
    fun bs -> (
      if !a <= 0
        then None
      else (
        a := !a -1;
        let b = ref (Random.int k) in
        let e = ref (!b + Random.int (k- !b)) in
        Some (fun distr ->  let a = int_of_float (count_between !b !e (get_db (pow 2 k) (sample_i distr))) in
                            b := Random.int k; e := !b + Random.int (k- !b);
                            (*Printf.printf "a: %d\n" a;*)
                            a)))
  in
  let (res, distrib, nb_upd) = oPMW (distrib_dirac i (pow 2 k)) (get_db k) (float_of_int k) (pow 2 k) (distrib_unif (pow 2 k)) stream_query 100 1 100 10. 0.01 in
  Printf.printf "- NB UPDATE : %d\n- DISTRIB DB :\n--- " nb_upd;
  List.iteri (fun i x -> if x > 0.00001 then (Printf.printf "%d : %f" i x)) (distrib_dirac i (pow 2 k));
  Printf.printf "\n";
  List.iter (fun x -> Printf.printf "%d" (int_of_float x)) (get_db k i);
  Printf.printf "\n\n- DISTRIB :\n";
  List.iteri (fun i x -> if x > 0.001 then (
                           Printf.printf "--- %d : %f \n" i x;
                           List.iter (fun x -> Printf.printf "%d" (int_of_float x)) (get_db k i);
                           Printf.printf "\n")) distrib;
  Printf.printf "\n\n- LIST RESULT :\n";
  aff_lst res
