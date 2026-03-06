(lang dune 3.17)
; version in current ci image

; update to rocq 0.11 with dune 3.21
(using coq 0.10)

; (name foxtrot)

(generate_opam_files true)

(authors "anon")

(maintainers "anon")

(package
 (name rocq-foxtrot)
 (synopsis "Contextual Refinement of Higher-Order Concurrent Probabilistic Programs")
 (depends ocaml
  (rocq-core (and (>= 9.0.0) (< "9.1~")))
  (rocq-stdlib (and (>= 9.0.0) (< "9.1~")))  
  (coq-iris (= "4.4.0"))
  (coq-stdpp (= "1.12.0"))
  (coq-coquelicot (= "3.4.4"))
  (coq-autosubst (= "1.9"))
  (coq-hierarchy-builder (= "1.10.1"))
  (coq-mathcomp-ssreflect (= "2.5.0"))
  (coq-mathcomp-solvable (= "2.5.0"))
  (coq-mathcomp-analysis (= "1.14.0"))  
  (rocq-elpi (= 3.2.0))
  (elpi (= 3.4.2)))
 )

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html