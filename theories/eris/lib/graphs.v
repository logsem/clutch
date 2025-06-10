From Coq Require Import List.
From clutch Require Import eris.
From clutch.eris.lib Require Import list array.
From GraphTheory Require mgraph.
From mathcomp Require Import fintype.
About Finite.type.

Definition Graph := mgraph.graph () ().
Notation "g '.vertices'" := (mgraph.vertex g) (at level 0).
Notation "g '.edges'" := (mgraph.edge g) (at level 0).


Notation source := (mgraph.endpoint false).
Notation target := (mgraph.endpoint true).

Definition is_graph (vertex_count : nat) (v : val) (g : Graph) : Prop :=
  ∃ (l : list (nat * nat)) 
    (eq_vertices : Finite.sort g.vertices = 'I_vertex_count) 
    (eq_edges : Finite.sort g.edges = 'I_(length l)),
    is_list l v ∧
    ∀ i : g.edges,
      let vertex_to_nat v := 
        nat_of_ord (ssrAC.change_type v eq_vertices) 
      in
      let edge_to_nat e := 
        nat_of_ord (ssrAC.change_type e eq_edges) 
      in
      let src_res : nat := vertex_to_nat (source i) in
      let trgt_res : nat := vertex_to_nat (target i) in
      let nat_i : nat := edge_to_nat i in
      nth_error l nat_i = Some (src_res, trgt_res).

(* 
For Karger's algorithm (https://en.wikipedia.org/wiki/Karger's_algorithm): 2 solutions

Either do specific things, or use an union find structure

*)

(* 
Need:
- multigraph structure, possibilities:
  - list of edges
  - associative list of vertex -> list of vertices
  - matrices (might be complicated due to rescaling)
- linking with Rocq's multigraphs
- Function to pick a random edge. HTS:
  - Always returns a result if graph is non-empty, the result is an edge of the graph
- Function to merge along an edge (and eventually remove reflexive edges: bounded number of steps).
  - Do we keep the same label or reconstruct a graph  with vertices from 0 to |G| - 1 every time ? (might be easier, but with more overhead, the merge function exists for multigraphs but does not remove reflexive edges, might be just as easy to recreate one)

Algorithm:
  def f(G : Graph):
    if |G| = 2:
      return G
    else:
      e := random edge
      G' := fuse the endpoints of e in G
      f G'
*)




Section graph_code.
  #[local] Open Scope expr_scope.
  Definition empty_graph : expr := list_nil.

  Definition add_edge : val :=
    λ: "src" "dst" "g", list_cons ("src", "dst") "g".
  
  Definition remove_edge : val :=
    rec: "remove_edge" "src" "dst" "g" :=
      if: "g" = empty_graph 
      then empty_graph
      else
        let: "h" := list_head "g" in
        let: "curr_src" := Fst "h" in
        let: "curr_dst" := Snd "h" in
        let: "new_g" := list_tail "g" in
        if: ("curr_src" = "src") || ("curr_dst" = "dst")
        then "new_g"
        else 
          let: "new_g" := "remove_edge" "src" "dst" "new_g" in
          add_edge "curr_src" "curr_dst" "new_g"
  .

  Definition get_output_nodes : val :=
    λ: "src" "g",
      list_map 
        (λ: "p", Snd "p") 
        (list_filter (λ: "p", Fst "p" = "src") "g")
  .

  Definition get_input_nodes : val :=
    λ: "dst" "g",
      list_map 
        (λ: "p", Fst "p") 
        (list_filter (λ: "p", Snd "p" = "dst") "g")
  .

  Definition get_edges : val := λ: "g", "g".

  Definition get_nodes : val :=
    rec: "get_nodes" "g" :=
      let: "nodes" := "get_nodes" (list_tail "g") in
      let, ("n1", "n2") := list_head "g" in
      let: "new_nodes" := 
        if: list_mem "n1" "nodes" 
        then "g" 
        else list_cons "n1" "nodes"
      in
      if: list_mem "n2" "new_nodes" 
      then "g" 
      else list_cons "n2" "new_nodes"
  .

End graph_code.


Section karger.

  Definition pick_random_edge : val :=
    λ: "g", 
      let: "len" := list_length "g" in
      let: "n" := rand ("len" - #1) in
      match: list_nth "g" "n" with 
      | SOME "v" => "v"
      | NONE => #() (* Not possible *)
      end
  .

  
  Definition fuse : val :=
    λ: "p" "g",
      let, ("repr", "to_replace") := "p" in
      let: "f" := λ: "e", 
        let, ("src", "dst") := "e" in 
        let: "new_src" := 
          if: "src" = "to_replace" 
          then "repr" else "src"
        in
        let: "new_dst" := 
          if: "dst" = "to_replace" 
          then "repr" else "dst"
        in
        ("new_src", "new_dst") 
      in
      list_map "f" "g"
  . 

  Definition cut : val :=
    λ: "g",
    let: "g" := ref "g" in
    while #2 < list_length (get_nodes !"g") do
      let: "e" := pick_random_edge !"g" in
      "g" <- fuse "e" !"g"
    end;;
    !"g"
  .

  Definition cut_size : val :=
    λ: "g",
    let: "f" := λ: "e",
      let, ("src", "dst") := "e" in
      "src" ≠ "dst"
    in
    list_length (list_filter "f" "g")
  .
  
End karger.
