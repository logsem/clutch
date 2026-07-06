(** Various functions *)

let rec pow m n =
  if n = 0 then 1
  else if n mod 2 = 0 then pow (m * m) (n / 2)
  else m * pow (m * m) ((n - 1) / 2)

let abs_f x =
  if x<0. then -.x else x

let string_to_int s =
  let l = String.length s in
  let res = ref 0 in
  for i = 0 to l - 1 do
    res := !res + (Char.(code s.[l - 1 - i] - code '0') * pow 10 i)
  done;
  !res

let int_to_string i =
  if i = 0 then "0"
  else (
  let rec aux i s =
    if i = 0 then s
    else aux (i/10) (String.make 1 Char.(chr (i mod 10 + code '0')) ^ s)
  in aux i ""
 )

let aff_flst l =
  List.iter (fun x -> Printf.printf "%f|" x) l;
  Printf.printf "\n"

let max_l l =
  List.fold_left max 0. l

let count_above l n =
  List.fold_left (fun acc x -> if x > n then acc + 1 else acc) 0 l

let aff_l_op l =
  List.fold_left
    (fun _ y ->
      match y with
      | None -> Printf.printf "⊥\n"
      | Some n -> Printf.printf "%d\n" n)
    () l


(** Utils function for the Hashtbl. implementation *)

let norm htbl =
  (* normalizes a hashtabl *)
  let sum = Hashtbl.fold (fun _ b acc -> acc +. b) htbl 0. in
  Hashtbl.iter (fun a b -> Hashtbl.replace htbl a (b /. sum)) htbl

let mk_histo file =
  (* compute the histogram of the db contained in file *)
  let reader = open_in file in
  let rec aux reader acc =
    try
      let line = input_line reader in
      aux reader ((*string_to_int*) line :: acc)
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
        Hashtbl.replace ht h (1. +. Hashtbl.find ht h);
        mk_domaine t acc)
      else (
        Hashtbl.add ht h 1.;
        mk_domaine t (h::acc))
  in
  let raw = aux reader [] in
  let size = List.length raw in
  let domain = mk_domaine raw [] in
  norm ht;
  (size, domain, ht)

let write_db db gif i =
  (* when gif = Some file, write the database in file_i.csv *)
  match gif with
  | Some file ->
    let writer = open_out (file ^ (int_to_string i) ^ ".csv") in
    Hashtbl.iter (fun a b -> Printf.fprintf writer "%s,%f\n" a b) db;
    close_out writer
  | _ -> ()

let get_rd_query domaine =
  (* given a domaine returns a random query (random map of domain -> {0, 1}) *)
  let res = Hashtbl.create 150 in
  List.iter (fun x -> Hashtbl.add res x (float_of_int (Random.int 2))) domaine;
  res

let c_query q db =
  (* given a query and a db compute the result (scalar product) *)
  Hashtbl.fold
    (fun a b acc -> acc +. (b *. (Hashtbl.find db a))) q 0.

let get_unif domaine =
  (* returns the uniform db on domaine *)
  let res = Hashtbl.create 150
  and s = List.length domaine in
  List.iter (fun x -> Hashtbl.add res x (1. /. float_of_int s)) domaine;
  res

let aff_db db =
  (* displays db *)
  Printf.printf "Aff_db ---\n---";
  Hashtbl.iter (fun a b -> Printf.printf " %s: %f\n---" a b) db;
  Printf.printf "> OK\n"

let aff_bq bq  =
  (* displays the boolean query *)
  Printf.printf "Aff_bq ---\n---";
  Hashtbl.iter (fun a b -> Printf.printf "%s:%d|" a (int_of_float b)) bq;
  Printf.printf "\n"


(** Utils functions for the list implementation *)

let sum_l l =
  List.fold_left (fun acc x -> acc + x) 0 l

let normalize_l l size =
  let s = sum_l l in
  let ln = List.map (fun x -> (size * x)/s) l in
  let s' = sum_l ln and
      lln = List.length ln in
  List.mapi (fun i x -> (if i <= size - s' -1 mod lln then 1 else 0) + (((size - s'))/lln) + x) ln

let mk_histo_l file =
  let (size, index, ht) = mk_histo file in
  (size, index, normalize_l (List.map (fun x -> int_of_float (Hashtbl.find ht x *. (float_of_int size))) index) size)

let write_db_l domain db gif i =
  (* when gif = Some file, write the database in file_i.csv *)
  match gif with
  | Some file ->
    let writer = open_out (file ^ (int_to_string i) ^ ".csv") in
    List.iteri (fun i x -> Printf.fprintf writer "%s,%d\n" x (List.nth db i)) domain;
    close_out writer
  | _ -> ()

let get_rd_query_l domaine =
  (* given a domaine returns a random query (random map of domain -> {0, 1}) *)
  List.map (fun x -> (0 = Random.int 2)) domaine

let get_unif_l domaine size =
  (* returns the uniform db on domaine *)
  let s = List.length domaine in
  List.init s (fun i -> (if i < size mod s then 1 else 0) + size / s)

let c_query_l q db =
  (* given a query and a db compute the result (scalar product) *)
  let res = ref 0 in
  List.iteri (fun i x -> if (List.nth q i) then (res := x + !res) else ()) db;
  !res

let aff_db_l db index =
  (* displays db *)
  Printf.printf "Aff_db ---\n---";
  List.iteri (fun i a -> Printf.printf " %s: %d\n---" a (List.nth db i)) index;
  Printf.printf "> OK\n"

let max_l2 l =
  List.fold_left max 0 l
