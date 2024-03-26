(** This module implements a key-value store as hash table where collisions are
    handled by chaining.

    The code hereafter is a simplified version of hashtbl.ml from OCaml's
    standard library. **)

(** We keep track of the number of elements that have been inserted. The data
    is stored in a reference to an array. The reference is updated when a new
    array is allocated during resizing. Each cell in the array represents a
    bucket, which is implemented as a list. **)
type ('a, 'b) t =
  int ref * ('a * 'b) list array ref

(* Accessor functions for the hash. *)
let data (_size, data) = data
let size (size, _data) = size

let number_of_buckets (h : ('a, 'b) t) =
  Array.length (! (data h))

(* fix the seed to get reproducible results *)
let hash (h : ('a, 'b) t) key = Hashtbl.seeded_hash 42 key

(** Compute the index associated to a key (by hashing it).  *)
let key_index (h : ('a, 'b) t) key =
  (hash h key) mod (number_of_buckets h)

(** Rehash old data (odata) and insert into new data (ndata). **)
let insert_all_buckets indexfun odata ndata =
  let rec insert_bucket = function
    | [] -> ()
    | ((key, data) :: next) ->
       let newidx = indexfun key in
       let oldbucket = Array.get ndata newidx in
       let newbucket = ((key, data) :: oldbucket) in
       Array.set ndata newidx newbucket ;
       insert_bucket next
  in
  for i = 0 to Array.length odata - 1 do
    insert_bucket (Array.get odata i)
  done

(** Update the size by doubling and rehash the data. **)
let resize (h : ('a, 'b) t) =
  let olddata = ! (data h) in
  let newsize = Array.length olddata * 2 in
  if newsize < Sys.max_array_length then begin
      let newdata = Array.make newsize [] in
      (data h) := newdata;
      insert_all_buckets (key_index h) olddata newdata
    end

(** Add a new key and value, possibly resizing. *)
let add (h : ('a, 'b) t) key value =
  let i = key_index h key in
  let oldbucket = Array.get (! (data h)) i in
  let newbucket = (key, value) :: oldbucket in
  Array.set (! (data h)) i newbucket ;
  (size h) := (! (size h)) + 1 ;
  if ! (size h) > ((Array.length (! (data h))) * 2) then
    resize h

(** Look up some key-value pair with [key] in [h]. **)
let find_opt (h : ('a, 'b) t) key =
  let bucket = Array.get (!(data h)) (key_index h key) in
  List.find_opt (fun (key', _v) -> key = key') bucket

(** Remove all key-value pairs associated to [key]. **)
let remove (h : ('a, 'b) t) key =
  let idx = key_index h key in
  let oldbucket = Array.get (! (data h)) idx in
  let newbucket =
    List.filter
      (fun (k', _v) ->
        let b = (key = k') in
        if b then (size h) := ! (size h) - 1 ;
        not b)
      oldbucket in
  Array.set (! (data h)) idx newbucket

(** Create a hash table with data array of size [init_size]. *)
let create init_size : ('a, 'b) t =
  let a = ref (Array.make init_size [])
  and current_size = ref 0 in
  (current_size, a)


(** Helper functions *)

let add_n t n =
  for i = 0 to n do
    add t (string_of_int i) i
  done

type statistics = {
    num_bindings: int;
    num_buckets: int;
    max_bucket_length: int;
    bucket_histogram: int array;
    average_bucket_length: float;
  }

let stats h =
  let mbl =
    Array.fold_left (fun m b -> Int.max m (List.length b)) 0 (! (data h)) in
  let histo = Array.make (mbl + 1) 0 in
  Array.iter
    (fun b ->
      let l = List.length b in
      histo.(l) <- histo.(l) + 1)
    (! (data h));
  let num_buckets = Array.length (! (data h)) in
  let num_bindings = ! (size h) in
  let avg = (float_of_int num_bindings) /. (float_of_int num_buckets) in
  { num_bindings ;
    num_buckets ;
    max_bucket_length = mbl;
    bucket_histogram = histo;
    average_bucket_length = avg ; }

(** Examples *)

let t = create 4 ;;
let _ = add t "2" 2 ; t ;;
let _ = add t "5" 5 ; t ;;
let _ = find_opt t "2" ;;
let _ = find_opt t "5" ;;
let _ = remove t "2" ; t ;;

let _ = add_n t 20 ; t ;;
let _ = stats t ;;

let t = create 4 ;;
for i = 0 to 200 do
  add t (string_of_int i) i ;
  let s = stats t in
  print_endline (string_of_int i ^ ": " ^ (string_of_float s.average_bucket_length))
done
