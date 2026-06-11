(*open SparseV*)

#use "private_multiplicative_weights.ml"

#use "db_sampling.ml"

let rec pow m n =
  if n = 0 then 1 else (
    if n mod 2 = 0 then pow (m*m) (n/2)
    else m * pow (m*m) ((n-1)/2) )


let aff_lst l =
  List.fold_left (fun acc x -> Printf.printf "%d|" x) () l;
  Printf.printf "\n"

let aff_l_op l =
  List.fold_left
    (fun _ y -> match y with
       | None -> Printf.printf "⊥\n"
       | Some n -> Printf.printf "%d\n" n) () l

let count_above t l =
  Array.fold_left (fun x y -> x + (if y>t then 1 else 0)) 0 l

let () =
  let k = 5 in
  let i = 5 in
  let db = get_db i k in
  let stream_query =
    let a = ref 1000 in
    fun bs -> (
      if !a <= 0
        then None
        else (a := !a -3; let b = Random.int k in Some (fun distr -> int_of_float (count_between b (b + Random.int k-b) (get_db (sample_i distr) k)))) )
  in
  Printf.printf "\nSmall epsilon -->\n";
  let res = oPMW (distrib_dirac i k) (fun j -> get_db j k) (float_of_int k) (pow 2 20) (distrib_unif k) stream_query 100 100 1 1. 1. in

  aff_lst res
