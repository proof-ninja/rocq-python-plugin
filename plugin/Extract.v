(** Translate.v の翻訳 [tr_prog] を OCaml に Extraction する。
    生成物 pycert_translate.ml(i) は、このディレクトリのライブラリ python_plugin が使う。 *)
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatInt.
From RocqPython Require Import Translate.

Extraction Language OCaml.
Extraction "pycert_translate.ml" tr_prog.
