#use "private_multiplicative_weights.ml"
let () = Random.self_init ()

let path = "data/"
let file = "rd_data.csv"

let path_gif = "gif/"
let file_gif = "0gif"

let () =
  let size, domaine, db = mk_histo (path ^ file) in
  let card_q = pow 2 (List.length domaine) in
  let nb_q = 3 * card_q in
  let stream_query =
    let a = ref nb_q in
    fun bs ->
      if !a <= 0 then None
      else (
        a := !a - 1;
        Some
          (get_rd_query domaine))
  in
  let res, db', nb_upd, c, t =
    oPMW_gif
      size
      domaine
      db
      (get_unif domaine)
      stream_query
      (float_of_int card_q)
      1 1 0.1 0.1
      (path_gif ^ file_gif)
  in
  Printf.printf "c: %f\nt: %f\n" c t;
  Printf.printf "- NB UPDATE : %d\n- DISTRIB DB :" nb_upd;
  aff_db db;
  Printf.printf "\n\n- SANITIZED :";
  aff_db db';
  Printf.printf "\n\n- LIST RESULT :\n";
  (* aff_flst res; *)
  ()
