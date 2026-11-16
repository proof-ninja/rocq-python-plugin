(** MiniML の構文。rocq-prover の plugins/extraction/miniml.mli の [ml_ast] の
    部分集合。

    - 変数は de Bruijn index で、[MLrel] と同じく 1 始まり
      (index 1 = 環境の先頭)。
    - [MLlam] は 1 引数、[MLapp] は n 引数 (意味はカリー化された逐次適用)。
    - 束縛名 ([ml_ident]) と [ml_type] は意味に関与しないので持たない。
    - 対象外 (第1版): MLtuple, MLfloat, MLstring, MLparray, MLaxiom,
      深いパターン (Pcons/Ptuple/Prel)。 *)
From Stdlib Require Import String ZArith List.
From PyCert Require Import Common.
Import ListNotations.

(** パターン。[Pusual g] は [Pcons (g, [Prel n; ...; Prel 1])] の略。
    [MPWild] の分岐は束縛変数を持たない (nvars = 0) ものとする。 *)
Inductive mpat : Type :=
| MPUsual (g : global)
| MPWild.

Inductive mexpr : Type :=
| MRel   (n : nat)                         (* n >= 1 *)
| MLam   (body : mexpr)
| MApp   (f : mexpr) (args : list mexpr)   (* args <> [] *)
| MLet   (e1 e2 : mexpr)
| MGlob  (g : global)
| MCons  (g : global) (args : list mexpr)  (* 飽和した適用 *)
| MCase  (scrut : mexpr) (brs : list mbranch)
| MFix   (i : nat) (defs : list mexpr)
    (* 相互再帰。各 def は全 fix 名を束縛した下で評価される。
       push_vars (List.rev ids) より、最後の def が index 1。 *)
| MExn   (msg : string)
| MDummy
| MMagic (e : mexpr)                       (* 実行時は恒等 *)
| MUint  (n : Z)                           (* 0 <= n < 2^63 (Uint63) *)
with mbranch : Type :=
(** [MBr p nvars body]: [body] は nvars 個の変数を束縛した下で評価される。
    最後の引数が index 1 (json_one_pat の push_vars (List.rev_map ids) より)。 *)
| MBr (p : mpat) (nvars : nat) (body : mexpr).

Inductive mdecl : Type :=
| MDTerm (g : global) (e : mexpr)
| MDFix  (gs : list global) (es : list mexpr).

Definition mprogram := list mdecl.
