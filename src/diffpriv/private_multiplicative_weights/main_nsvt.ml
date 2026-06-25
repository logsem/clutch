#use "numeric_sparse_vector.ml"

let path = "data/"
let file = "data0"
let () = Random.self_init ()

let mk_array file =
  (* turn a column file of numbers into a int Array *)
  let reader = open_in (path ^ file) in
  let rec aux reader acc =
    try
      let line = input_line reader in
      aux reader (string_to_int line :: acc)
    with e ->
      close_in_noerr reader;
      acc
  in
  Array.of_list (aux reader [])

let count_above t l =
  Array.fold_left (fun x y -> x + if y > t then 1 else 0) 0 l

let () =
  let db = mk_array file in
  let stream_query =
    let a = ref 1000 in
    fun bs ->
      if !a <= 0 then None
      else (
        a := !a - 1;
        Some (count_above !a))
  in
  Printf.printf "\nSmall epsilon -->\n";
  let res = nSVT_stream 1 30 200 20 stream_query db in
  aff_l_op res;

  let stream_query =
    let a = ref 1000 in
    fun bs ->
      if !a <= 0 then None
      else (
        a := !a - 1;
        Some (count_above !a))
  in
  Printf.printf "\nMedium (=1) epsilon -->\n";
  let res = nSVT_stream 1 1 200 20 stream_query db in
  aff_l_op res;

  let stream_query =
    let a = ref 1000 in
    fun bs ->
      if !a <= 0 then None
      else (
        a := !a - 1;
        Some (count_above !a))
  in
  Printf.printf "\nLarge epsilon -->\n";
  let res = nSVT_stream 30 1 200 20 stream_query db in
  aff_l_op res
