(lang dune 3.20)

(using coq 0.10)

; (name clutch)

(generate_opam_files true)

(source
 (github logsem/clutch))

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
 (name coq-clutch)
 (synopsis "Higher-order probabilistic separation logics")
 (depends ocaml
  (coq (and (>= 8.19) (< "8.20~")))
  (coq-iris (= "4.2.0"))
  (coq-stdpp (= "1.10.0"))
  (coq-coquelicot (= "3.4.1"))
  (coq-autosubst (= "1.9"))
  (coq-hierarchy-builder (= "1.8.1"))
  (coq-mathcomp-ssreflect (= "2.2.0"))
  (coq-mathcomp-solvable (= "2.2.0"))
  (coq-mathcomp-analysis (= "1.4.0")))
 (tags
  ("awesome" "separation logic" probabilities)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
