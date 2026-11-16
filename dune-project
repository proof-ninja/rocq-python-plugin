(lang dune 3.21)
(using rocq 0.11)

(generate_opam_files true)

(license MIT)

(package
 (name rocq-python-plugin)
 (synopsis "Python extraction plugin for Rocq")
 (depends
  ocaml
  ; Common.register_language を持つ Rocq (9.4 で入る見込み。PR #22541) が必要。
  (rocq-runtime (>= 9.4~))
  (rocq-core (>= 9.4~))
  (rocq-stdlib (>= 9.4~))
  rocq-pycert
  zarith))
