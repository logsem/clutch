(*open SparseV*)
#use "private_multiplicative_weights.ml"

#use "db_sampling.ml"

let path = "data/"
let file = "rd_data.csv"
let () = Random.self_init ()

let aff_lst l =
  List.iter (fun x -> Printf.printf "%f|" x) l;
  Printf.printf "\n"

let aff_l_op l =
  List.fold_left
    (fun _ y ->
      match y with
      | None -> Printf.printf "⊥\n"
      | Some n -> Printf.printf "%d\n" n)
    () l

let () =
  let size, domaine, db = mk_histo (path ^ file) in
  let card_q = pow 2 (List.length domaine) in
  let nb_q = 3 * card_q in
  aff_db (get_unif domaine);
  let stream_query =
    let a = ref nb_q in
    fun bs ->
      if !a <= 0 then None
      else (
        a := !a - 1;
        Some
          (get_rd_query domaine))
  in
  let res, db', nb_upd =
    oPMW
      size
      domaine
      db
      (get_unif domaine)
      stream_query
      (float_of_int card_q)
      1 1 0.1 0.01
  in
  Printf.printf "- NB UPDATE : %d\n- DISTRIB DB :" nb_upd;
  aff_db db;
  Printf.printf "\n\n- SANITIZED :";
  aff_db db';
  Printf.printf "\n\n- LIST RESULT :\n";
  (* aff_lst res; *)
  ()
