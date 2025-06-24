Import EqNotations.

From Coq Require Import List.
From clutch Require Import eris.
From clutch.eris.lib Require Import list.
From clutch.eris.lib.graphs Require Import lemmas.
From clutch.common Require Import inject.
From GraphTheory Require mgraph.
From mathcomp Require Import fintype ssreflect.ssrAC.

Ltac intro_subst := let temp := fresh in intro temp; subst temp; try clear temp.
Ltac intro_subst_all := repeat intro_subst.
#[local] Ltac done ::= 
  solve[
    lia |
    lra |
    nra |
    tactics.done |
    auto
  ].

#[local] Definition Graph := mgraph.graph () ().
#[local] Notation "g '.vertices'" := (mgraph.vertex g) (at level 0).
#[local] Notation "g '.edges'" := (mgraph.edge g) (at level 0).


#[local] Notation source := (mgraph.endpoint false).
#[local] Notation target := (mgraph.endpoint true).

Record is_graph (v : val) (g : Graph) (vertex_count : nat) : Set := IsGraph {
  edges : list (nat * nat);

  eq_val : v = (#vertex_count, inject edges)%V;
  eq_vertices : Finite.sort g.vertices = 'I_vertex_count;
  eq_edges : Finite.sort g.edges = 'I_(length edges);
  
  corres : 
    ∀ i : g.edges,
      let nat_of_vertex (v : g.vertices) := nat_of_ord (eq_vertices ▸ v) in
      let nat_of_edge (e : g.edges) := nat_of_ord (eq_edges ▸ e) in
      let src_res := nat_of_vertex (source i) in
      let trgt_res := nat_of_vertex (target i) in
      let nat_i := nat_of_edge i in
      nth_error edges nat_i = Some (src_res, trgt_res)
}.

#[local] Notation "gv '≃{' n '}' g" := (is_graph gv g n) (at level 50, no associativity).

Section graph_code.
  Context `{!erisGS Σ}.
  Definition empty_graph : val := λ: "n", ("n", list_nil). 
  Definition empty_graph_rocq (n : nat) : Graph :=
    {|
      mgraph.vertex := 'I_n;
      mgraph.edge := 'I_0;
      mgraph.endpoint := 
        λ _ '(Ordinal _ pf), False_rect _ $ not_0_gt (leb_to_leq pf) ;
      mgraph.vlabel := λ _, ();
      mgraph.elabel := λ _, ()
    |}.


  Lemma empty_graph_spec (n : nat) :
    [[{True}]]
      empty_graph #n
    [[{g, RET g; ⌜inhabited (g ≃{n} (empty_graph_rocq n))⌝}]].
  Proof.
    iIntros "%Φ _ HΦ".
    unfold empty_graph.
    wp_pures.
    iApply "HΦ".
    iPureIntro.
    unshelve eapply inhabits, IsGraph.
    - exact [].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - case=> m pf.
      exfalso.
      exact: not_0_gt (leb_to_leq pf).
  Qed.
  Search (¬ is_true (ssrnat.leq (S _) 0)).

  Definition add_edge : val :=
    λ: "src" "dst" "g",
    let, ("n", "l") := "g" in ("n", list_cons ("src", "dst") "l").

  Definition add_edge_rocq 
    {edge_count : nat}
    (g : Graph) 
    (eq_edges : 'I_edge_count = Finite.sort g.edges)
    (src dest : g.vertices) : Graph :=
      {|
        mgraph.vertex := g.vertices;
        mgraph.edge := 'I_(S edge_count);
        mgraph.endpoint :=
          λ b '(Ordinal n pf), 
          match n as n0 return (n = n0) -> g.vertices with
          | 0 => λ _, if b then dest else src
          | S n' => 
            λ heq,
              mgraph.endpoint b $ 
                eq_edges ▸ (
                  Ordinal (
                    ssrnat.ltnSE (
                        rew f_equal (λ a, ssrnat.leq (S a) (S edge_count)) heq in pf
                    )
                  )
                )
          end eq_refl
         ;
        mgraph.vlabel := λ _, ();
        mgraph.elabel := λ _, ()
      |}.

  
  Lemma add_edge_spec (vertex_count : nat) (src dst : 'I_vertex_count) (gv : val) (g : Graph) (Hg : gv ≃{vertex_count} g) :
      [[{True}]]
        add_edge #src #dst gv
      [[{
        gv', RET gv'; 
        ⌜
          let (_, _, eq_vertices, eq_edges, _) := Hg in inhabited $
          gv' ≃{vertex_count} (
            add_edge_rocq 
              g 
              (eq_sym eq_edges) 
              (eq_vertices ▸ₛ src)
              (eq_vertices ▸ₛ dst)
            )
        ⌝
      }]].
  Proof.
    iIntros "%Φ _ HΦ".
    move: src dst Hg => [src srcprf] [dst dstprf] [edges -> eq_vertices eq_edges corres] /=.
    rewrite /add_edge.
    wp_pures.
    assert (is_list edges (inject_list edges)) 
      as Hlist
      by rewrite is_list_inject //.
    assert ((inject (src, dst)%core = (#src, #dst)%V)) as <- by reflexivity.
    wp_apply twp_list_cons as "%new_edges %Hlist_new"; first done.
    wp_pures.
    iApply "HΦ".
    iPureIntro.
    unshelve eapply inhabits, IsGraph.
    - exact ((src, dst) :: edges).
    - exact eq_vertices.
    - reflexivity.
    - by apply is_list_inject in Hlist_new as ->.
    - intros [[|i] iprf]; intro_subst_all;
        rewrite /= -?corres !transport_sym_right //.
  Qed.

  Definition add_node : val :=
    λ: "g",
    let, ("n", "l") := "g" in (("n" + #1, "l"), "n").
  
  Definition add_node_rocq 
    {vertex_count : nat}
    (g : Graph) 
    (eq_vertices : Finite.sort g.vertices = 'I_vertex_count )
    : Graph := 
      {|
        mgraph.vertex := 'I_(S vertex_count);
        mgraph.edge := g.edges;
        mgraph.endpoint b e := 
          let 'Ordinal v pf := eq_vertices ▸ (mgraph.endpoint b e) in
          Ordinal (ssrnat.leqW pf);
        mgraph.vlabel := λ _, ();
        mgraph.elabel := λ _, ()
      |}.
      
  Lemma add_node_spec (vertex_count : nat) (gv : val) (g : Graph) (Hg : gv ≃{vertex_count} g) :
  [[{True}]]
    add_node gv
  [[{
    gv', RET (gv', #vertex_count); 
    ⌜
      let (_, _, eq_vertices, eq_edges, _) := Hg in inhabited $
      gv' ≃{S vertex_count} (add_node_rocq g (eq_vertices))
    ⌝
  }]].
  Proof.
    iIntros "%Φ _ HΦ".
    destruct Hg as [edges -> eq_vertices eq_edges corres].
    rewrite /add_node.
    wp_pures.
    iApply "HΦ".
    iPureIntro.
    unshelve eapply inhabits, IsGraph.
    - exact edges.
    - reflexivity.
    - exact eq_edges.
    - by rewrite Z.add_1_r -Nat2Z.inj_succ.
    - intros i; intro_subst_all;
      rewrite corres /=.
      by destruct (eq_vertices ▸ (mgraph.endpoint (g:=g) true i)), (eq_vertices ▸ (mgraph.endpoint (g:=g) false i)).
  Qed.

  Search ssrnat.leq "trans".

  Definition convert_rocq {vertex_count} (val : 'I_(S vertex_count)) (repr to_replace : 'I_(S vertex_count)) (Hlt : repr < to_replace) : 'I_vertex_count :=
    let to_replace_le_vertex_count : to_replace ≤ vertex_count :=
      le_S_n $ leb_to_leq $ ltn_ord to_replace
    in
    match nat_tricho val to_replace with
    | inleft (left val_lt_to_replace) =>
        let val_lt_vertex_count : val < vertex_count := 
          Nat.le_trans val_lt_to_replace to_replace_le_vertex_count
        in 
        mkOrdinal val_lt_vertex_count
    | inleft (right val_eq_to_replace) => 
        let repr_lt_vertex_count : repr < vertex_count := 
          Nat.le_trans Hlt to_replace_le_vertex_count
        in
        mkOrdinal repr_lt_vertex_count
    | inright val_gt_to_replace =>
        match nat_of_ord val as val0 return nat_of_ord val = val0 -> 'I_vertex_count with
        | 0 => λ val_eq_0, False_rect _ $ not_0_gt_eq val_eq_0 val_gt_to_replace
        | S val' => λ val_eq_Sval',
            let val_le_vertex_count : val <= vertex_count := le_S_n $ leb_to_leq $ ltn_ord val in 
            let val'_lt_vertex_count : val' < vertex_count := 
              eq_ind _ (λ a, a <= vertex_count) val_le_vertex_count _ val_eq_Sval' 
            in
            mkOrdinal val'_lt_vertex_count
        end eq_refl
    end.

  Definition fuse_rocq {vertex_count} (g : Graph) (Heq: Finite.sort g.vertices = 'I_(S vertex_count)) {repr to_replace : 'I_(S vertex_count)} (Hlt : (repr < to_replace)%nat) : Graph :=
    {|
      mgraph.vertex := 'I_vertex_count;
      mgraph.edge := g.edges;
      mgraph.endpoint b e := convert_rocq (Heq ▸ mgraph.endpoint (g := g) b e) _ _ Hlt
      ;
      mgraph.vlabel := λ _, ();
      mgraph.elabel := λ _, ();
    |}.

  Definition convert : val :=
    λ: "v" "repr" "to_replace",
    if: "v" = "to_replace"
    then "repr"
    else 
      if: "to_replace" < "v"
      then "v" - #1
      else "v".
  Definition fuse : val :=
    λ: "repr" "to_replace" "g",
      let, ("vertices", "edges") := "g" in
      let: "f" := λ: "e",
        let, ("src", "dst") := "e" in
        (convert "src" "repr" "to_replace", convert "dst" "repr" "to_replace")
      in
      let: "new_edges" := list_map "f" "edges" in
      ("vertices" - #1, "new_edges")
  .
  
  Theorem fuse_spec (vertex_count : nat) (repr to_replace : 'I_(S vertex_count)) (gv : val) (g : Graph) (Hg : gv ≃{S vertex_count} g) (repr_lt_to_replace : repr < to_replace):
  [[{True}]]
    fuse #repr #to_replace gv
  [[{
    gv', RET gv';
    ⌜
      let (_, _, eq_vertices, eq_edges, _) := Hg in inhabited $
      gv' ≃{vertex_count} (
        fuse_rocq 
          g 
          eq_vertices 
          repr_lt_to_replace
      )
    ⌝
  }]].
  Proof.
    iIntros "%Φ _ HΦ".
    destruct Hg as [edges -> eq_vertices eq_edges corres].
    unfold fuse.
    wp_pures.
    pose convert_rocq v :=
      match nat_tricho v to_replace with
      | inleft (left v_lt_to_replace) => v
      | inleft (right v_eq_to_replace) => repr
      | inright v_gt_to_replace => 
          match v as v0 return v = v0 -> nat with 
          | 0 => λ v_eq_0, False_rect _ $ not_0_gt_eq v_eq_0 v_gt_to_replace
          | S v' => λ _, v'
          end eq_refl
      end.
      
    assert (∀ v, v < to_replace -> convert_rocq v = v) as convert_lt
      by (move=>> ?;rewrite /= /convert_rocq nat_tricho_lt //).
    assert (convert_rocq to_replace = repr) as convert_eq 
      by rewrite /convert_rocq /= nat_tricho_eq //.
    assert (∀ v, S v > to_replace -> convert_rocq (S v) = v) as convert_gt
      by (move=>> ?;rewrite /= /convert_rocq /ord_succ nat_tricho_gt //).

    pose f := λ '(src, dst), (convert_rocq src, convert_rocq dst).
    wp_apply (twp_list_map edges f _ _ (λ _, True)%I (λ _ _, True)%I) as "%v [%Hlist forall_Q]".
    {
      iSplit.
      - iIntros ([src dst]) "%Φ' !> HP HΦ'"; unfold convert; wp_pures.
        destruct (nat_tricho dst to_replace) as [[dst_lt_to_replace | ->] | dst_gt_to_replace] eqn:Heq_tricho_dst_to_replace;
        destruct (nat_tricho src to_replace) as [[src_lt_to_replace | ->] | src_gt_to_replace] eqn:Heq_tricho_src_to_replace;
          repeat (
            match goal with 
            | |- context[bool_decide (?a = ?a)] => rewrite bool_decide_eq_true_2 //
            | |- context[bool_decide (?a = ?b)] => rewrite bool_decide_eq_false_2 //; last (intros [=->%Nat2Z.inj]; done)
            | H : ?a < ?b |- context[bool_decide (Z.of_nat ?a < Z.of_nat ?b)%Z] => rewrite bool_decide_eq_true_2 //
            | H : ?b > ?a |- context[bool_decide (Z.of_nat ?a < Z.of_nat ?b)%Z] => rewrite bool_decide_eq_true_2 //
            | H : ?b < ?a |- context[bool_decide (Z.of_nat ?a < Z.of_nat ?b)%Z] => rewrite bool_decide_eq_false_2 //
            | H : ?a > ?b |- context[bool_decide (Z.of_nat ?a < Z.of_nat ?b)%Z] => rewrite bool_decide_eq_false_2 //
            end;
            try wp_pures
          ); 
          iApply "HΦ'";
          rewrite /= /convert_rocq ?Heq_tricho_src_to_replace ?Heq_tricho_dst_to_replace;
          by repeat match goal with 
          | |- context[(Z.of_nat ?v - 1)%Z] => 
              destruct v; [lia | rewrite Z.sub_1_r Nat2Z.inj_succ Z.pred_succ]
          end.
      - by iSplitR; first rewrite is_list_inject.
    }
    wp_pures.
    rewrite Z.sub_1_r Nat2Z.inj_succ Z.pred_succ.
    iApply "HΦ".  
    iPureIntro.
    unshelve eapply inhabits, IsGraph.
    - exact (map f edges).
    - reflexivity.
    - rewrite map_length eq_edges //.
    - f_equal; apply is_list_inject, Hlist.
    - intros i; intro_subst_all.
      rewrite nth_error_map /= /graph_code.convert_rocq /mkOrdinal.
      destruct repr as [repr' repr'_lt_Svertex_count] eqn:Heq_repr'.
      destruct (eq_vertices ▸ (mgraph.endpoint (g:=g) false i)) as [src src_lt_Svertex_count] eqn:Heq_src.
      destruct (eq_vertices ▸ (mgraph.endpoint (g:=g) true i)) as [dst dst_lt_Svertex_count] eqn:Heq_dst; simpl.
      destruct (nat_tricho src to_replace) as [[src_lt_to_replace | src_eq_to_replace] | src_gt_to_replace];
      destruct (nat_tricho dst to_replace) as [[dst_lt_to_replace | dst_eq_to_replace] | dst_gt_to_replace];
       repeat match goal with 
        | |- context[match ?v with | _ => _ end] => 
            let v' := fresh v in 
            let Heqv := fresh "Heq" v in 
            destruct v as [|v'] eqn:Heqv; first lia
        | |- _ = Some (?new_src, ?new_dst) =>
            assert ((new_src, new_dst) = f (src, dst)) as ->;
            [ simpl; f_equal; subst;
              solve[rewrite !convert_lt // | rewrite convert_eq // | rewrite convert_gt //]
            | subst; rewrite option_map_some nat_of_ord_transport_map corres Heq_src Heq_dst // ]
        end.
  Qed.


  (* TODO: Look at proof on paper and give an estimation of possiblity *)


  (* TODO: rewrite this *)
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
  - Do we keep the same label or reconstruct a graph  with vertices from 0 to |G| - 1 every time ? (might be easier, but with more overhead, the merge λction exists for multigraphs but does not remove reflexive edges, might be just as easy to recreate one)

Algorithm:
  def f(G : Graph):
    if |G| = 2:
      return G
    else:
      e := random edge
      G' := fuse the endpoints of e in G
      f G'
*)
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

  
  (* Definition fuse : val :=
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
  . *)

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
