(*open SparseV*)
#use "numeric_sparse_vector.ml"

let path = "data/"
let file = "data0"

let rec pow m n =
  if n = 0 then 1 else (
    if n mod 2 = 0 then pow (m*m) (n/2)
    else m * pow (m*m) ((n-1)/2) )

let string_to_int s =
  let l = String.length s in
  let res = ref 0 in
  for i = 0 to (l-1) do
    res := !res + Char.(code(s.[l-1-i]) - code('0')) * pow 10 i
  done;
  !res


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

let aff_tab t n =
  for i = 0 to n do
    Printf.printf "%d\n" t.(i)
  done

let aff_l_op l =
  List.fold_left
    (fun _ y -> match y with
       | None -> Printf.printf "⊥\n"
       | Some n -> Printf.printf "%d\n" n) () l

let count_above t l =
  Array.fold_left (fun x y -> x + (if y>t then 1 else 0)) 0 l

let () =
  let db = mk_array file in
  let stream_query =
    let a = ref 1000 in
    fun bs -> (
      if !a <= 0
        then None
        else (a := !a -1; Some (count_above !a)) )
  in
  Printf.printf "\nSmall epsilon -->\n";
  let res = nSVT_stream 1 30 200 20 stream_query db in
  aff_l_op res;
  
  let stream_query =
    let a = ref 1000 in
    fun bs -> (
      if !a <= 0
        then None
        else (a := !a -1; Some (count_above !a)) )
  in
  Printf.printf "\nMedium (=1) epsilon -->\n";
  let res = nSVT_stream 1 1 200 20 stream_query db in
  aff_l_op res;

  let stream_query =
    let a = ref 1000 in
    fun bs -> (
      if !a <= 0
        then None
        else (a := !a -1; Some (count_above !a)) )
  in
  Printf.printf "\nLarge epsilon -->\n";
  let res = nSVT_stream 30 1 200 20 stream_query db in
  aff_l_op res
