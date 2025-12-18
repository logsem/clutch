(lang dune 3.20)

; update to rocq 0.11 with dune 3.21
(using coq 0.10)

; (name clutch)

(generate_opam_files true)

(source (github logsem/clutch))

(authors "Simon Oddershede Gregersen"
         "Alejandro Aguirre"
         "Philipp G. Haselwarter"
         "Kwing Hei Li"
         "Markus de Medeiros"
         "Joseph Tassarotti"
         "Lars Birkedal")

(maintainers "Simon Oddershede Gregersen <s.gregersen@nyu.edu>")

(homepage "https://github.com/logsem/clutch")

(license MIT)

; (documentation https://url/to/documentation)

(package
 (name rocq-clutch)
 (synopsis "Higher-order probabilistic separation logics")
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
  (coq-elpi (= 3.2.0))
  (elpi (= 3.4.2)))
 (tags
  ("awesome" "separation logic" probabilities)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html