let rec pow m n =
  (* computes m^n *)
  if n = 0 then 1
  else if n mod 2 = 0 then pow (m * m) (n / 2)
  else m * pow (m * m) ((n - 1) / 2)

let string_to_int s =
  (* given a string of a number "102" -> 102 *)
  let l = String.length s in
  let res = ref 0 in
  for i = 0 to l - 1 do
    res := !res + (Char.(code s.[l - 1 - i] - code '0') * pow 10 i)
  done;
  !res

let mk_histo file =
  (* Given a file containing a column of number returns *)
  (* - the size of the db *)
  (* - the domain *)
  (* - the normalized histogram. *)
  let reader = open_in file in
  let rec aux reader acc =
    try
      let line = input_line reader in
      aux reader (string_to_int line :: acc)
    with e ->
      close_in_noerr reader;
      acc
  in
  let ht = Hashtbl.create 150 in
  let rec mk_domaine lst acc =
    match lst with
    | [] -> acc
    | h::t ->
      if Hashtbl.mem ht h then (
        Hashtbl.replace ht h (1+ Hashtbl.find ht h);
        mk_domaine t acc)
      else (
        Hashtbl.add ht h 1;
        mk_domaine t (h::acc))
  in
  let raw = aux reader [] in
  let size = List.length raw in
  let domain = mk_domaine raw [] in
  let ht_normal = Hashtbl.create 150 in
  Hashtbl.iter (fun a b -> Hashtbl.add ht_normal a ((float_of_int b) /. (float_of_int (List.length raw)))) ht;
  (size, domain, ht_normal)


let get_rd_query domaine =
  (* Given a domaine returns a random query (random map of domain -> bool) *)
  let res = Hashtbl.create 150 in
  List.iter (fun x -> Hashtbl.add res x (float_of_int (Random.int 2))) domaine;
  res

let c_query q db =
  (* Given a query and a db compute the result *)
  Hashtbl.fold
    (fun a b acc -> acc +. (b *. (Hashtbl.find db a))) q 0.

let get_unif domaine =
  (* Given a domain returns the uniform db on it *)
  let res = Hashtbl.create 150
  and s = List.length domaine in
  List.iter (fun x -> Hashtbl.add res x (1. /. float_of_int s)) domaine;
  res

let aff_db db =
  (* Given a db, displays the db *)
  Printf.printf "Aff_db ---\n---";
  Hashtbl.iter (fun a b -> Printf.printf "%d: %f\n---" a b) db;
  Printf.printf "> OK\n"
