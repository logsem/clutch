(*open SparseV*)
#use "private_multiplicative_weights.ml"

#use "db_sampling.ml"

let path = "data/"
let file = "adult_with_pii_sanitized.csv"
let () = Random.self_init ()

let rec pow m n =
  if n = 0 then 1
  else if n mod 2 = 0 then pow (m * m) (n / 2)
  else m * pow (m * m) ((n - 1) / 2)

let string_to_int s =
  let l = String.length s in
  let res = ref 0 in
  for i = 0 to l - 1 do
    res := !res + (Char.(code s.[l - 1 - i] - code '0') * pow 10 i)
  done;
  !res

let mk_histo file =
  (* turn a column file of numbers into an histogram of the form of an int Array *)
  let reader = open_in (path ^ file) in
  let rec aux reader acc =
    try
      let line = input_line reader in
      aux reader (string_to_int line :: acc)
    with e ->
      close_in_noerr reader;
      acc
  in
  let raw = Array.of_list (aux reader []) in
  let max_elem = Array.fold_left (fun acc v -> if (v>acc) then v else acc) raw.(0) raw and
      min_elem = Array.fold_left (fun acc v -> if (v<acc) then v else acc) raw.(0) raw and
      size = Array.length raw
  in
  (size, max_elem, min_elem, Array.init (max_elem - min_elem) (fun i -> count raw i))



let aff_lst l =
  List.iter (fun x -> Printf.printf "%d|" x) l;
  Printf.printf "\n"

let aff_l_op l =
  List.fold_left
    (fun _ y ->
      match y with
      | None -> Printf.printf "⊥\n"
      | Some n -> Printf.printf "%d\n" n)
    () l

let count_above t l =
  Array.fold_left (fun x y -> x + if y > t then 1 else 0) 0 l

let count db l =
  db.(l)

let () =
  let nb_q = 1000 in

  let (length, max, min, db) = mk_histo file in

  let stream_query =
    let a = ref nb_q in
    fun bs ->
      if !a <= 0 then None
      else (
        a := !a - 1;
        let b = ref (Random.int max) in
        Some
          (fun db' -> int_of_float db'.(!b)))
  in
  let res, distrib, nb_upd =
    oPMW
      db
      length (pow length (max - min))
      (distrib_unif (max - min))
      stream_query (max - min)
      1 1 10. 0.01
  in
  Printf.printf "- NB UPDATE : %d\n- DISTRIB DB :" nb_upd;
  List.iteri
    (fun i x -> Printf.printf "\n---%d : %f" i x) db;
  Printf.printf "\n\n- SANITIZED :";
  List.iteri
    (fun i x -> Printf.printf "\n---%d : %f" i x) res;
  Printf.printf "\n\n- LIST RESULT :\n";
  aff_lst res
