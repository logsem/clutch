#use "numeric_sparse_vector.ml"

let norm l =
  let sum = List.fold_left (fun s x -> s +. x) 0. l in
  List.map (fun x -> x /. sum) l

let upd x r eta get_db_i =
  List.mapi (fun i pdb -> pdb *. exp (-. eta *. (float_of_int (r (get_db_i i))))) x



let mw x f v eta get_db_i =
  (*Printf.printf "######\n######\n";*)
  let r = ref f in
  if v >= f x then begin
      r := (fun y -> 1 - f y)
  end;
  norm (upd x (!r) eta get_db_i)



let oPMW db get_db_i normeDB card_Sdb unif stream_q card_Sq num den alpha beta =
  (*
    let c = 1. +. 4. *. (log (float_of_int card_Sdb)) /.  (alpha *. alpha) in
    let t = ((float_of_int den) *. 18. *. c *. (log (2. *. float_of_int card_Sq) +. log (4. *. c) -. log beta)) /. ((float_of_int num) *. normeDB) in
   *)
  let c = 200. in
  let t = 5. in
  let f = num_sparse_vector num den (int_of_float t) (int_of_float c) in
  let distrib = ref unif in
  let nb_upd = ref 0 in
  let rec nSVT i bs =
    (*Printf.printf "\n----\n";
    List.iter (Printf.printf "%f | ") (!distrib);
    Printf.printf "\n\n";*)
    match stream_q bs with
    | None -> (bs, !distrib, !nb_upd)   (* No more queries *)
    | Some q ->
       if i > 1 + int_of_float c
       then     (* we retrun only from the distribution *)
         nSVT i ((q !distrib) :: bs)
       else (
       let e1 = f db (fun x' -> q x' - q !distrib) in
       let e2 = f db (fun x' -> q !distrib - q x') in
       let a = ref None in
       (match e1 with
       | None -> (
          match e2 with
          | None -> ()
          | Some v -> a := Some (q !distrib + v))
       | Some v -> a := Some (q !distrib - v));
       (match !a with
       | None -> nSVT i ((q !distrib) :: bs)
       | Some v -> nb_upd := !nb_upd + 1; distrib := mw (!distrib) q v (alpha /. 2.) get_db_i; nSVT (i+1) (v :: bs))
       )
  in
  nSVT 0 []
