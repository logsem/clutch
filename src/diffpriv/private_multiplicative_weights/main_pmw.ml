#use "private_multiplicative_weights.ml"
let () = Random.self_init ()

let path = "data/"
let file = "educ_lvl.csv"
(* let file = "adult_with_pii_sanitized_short.csv" *)

let path_gif = "gif/data/"
let file_gif = "gif"

let () =
  let size, domaine, db = mk_histo (path ^ file) in
  Printf.printf "tl: %d\n" (pow 2 (List.length domaine));
  let card_q = pow 2 (List.length domaine) in
  let nb_q = 2 * card_q in
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
    oPMW
      size
      domaine
      db
      (get_unif domaine)
      stream_query
      (float_of_int card_q)
      10 1 0.1 0.1
      ~gif:(if (Array.length Sys.argv = 2) && (Sys.argv.(1) = "--gif") then Some (path_gif ^ file_gif) else None)
  in
  if (Array.length Sys.argv = 2) && (Sys.argv.(1) = "--gif") then (
    let writer = open_out (path_gif ^ "len.csv") in
    Printf.fprintf writer "%d\n" nb_upd;
    close_out writer
  );
  Printf.printf "c: %f\nt: %f\n" c t;
  Printf.printf "- NB UPDATE : %d\n- ORIGINAL DB :\n" nb_upd;
  aff_db db;
  Printf.printf "\n\n- SANITIZED DB :\n";
  aff_db db';
  Printf.printf "\n\n- LIST RESULT :\n";
  (* aff_flst res; *)
  ()
