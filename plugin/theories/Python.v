(** Rocq → Python 抽出を使うための 1 行インポート:
      From PythonPlugin Require Import Python.
*)
Declare ML Module "rocq-runtime.plugins.extraction".   (* Extraction コマンドの文法 *)
Declare ML Module "rocq-python-plugin".                            (* Python 言語の登録 *)
