(** MiniML の構文。rocq-prover の plugins/extraction/miniml.mli の [ml_ast] の
    部分集合。型名とコンストラクタ名は、[miniml.mli] と同じにしてある
    ([ml_ast], [ml_branch], [ml_pattern], [ml_decl], [MLrel], [MLlam], ...)。

    - 変数は de Bruijn index で、[MLrel] と同じく 1 始まり
      (index 1 = 環境の先頭)。
    - [MLlam] は 1 引数、[MLapp] は n 引数 (意味はカリー化された逐次適用)。

    [miniml.mli] との差 (すべて、意味に関与しないものを持たない、または、対象外にしたもの):

    - [MLlam], [MLletin] の束縛名 ([ml_ident]) を持たない。
    - [MLcons], [MLcase] の型 ([ml_type]) を持たない。[MLdummy] の [kill_reason] を持たない。
    - [MLfix] の関数名 ([Id.t array]) を持たない。配列は、[list] で表す。
    - [ml_ident] の [Id] / [Tmp] の引数は、[Id.t] ではなく [string]。
      ([ml_branch] は、[miniml.mli] と同じ組 [(ml_ident list * ml_pattern * ml_ast)]。
      意味は、[ml_ident list] の長さ (束縛する変数の個数) だけに依存する。)
    - [MLuint] の値は、[Uint63.t] ではなく [Z] で、[0 <= n < 2^63]。理由: [Uint63.t] は、
      OCaml への抽出で、native int にするための型で、他の言語への抽出には関係しない。
      Python の整数は任意精度なので、[Z] で足りる (他の言語への抽出に影響しない)。
    - [Dterm], [Dfix] の型 ([ml_type]) を持たない。[Dind], [Dtype] は持たない
      (型宣言は、Python では不要)。
    - モジュール構造 ([ml_structure] の入れ子) を持たず、宣言の列 ([list ml_decl]) だけを扱う。
    - 対象外 (第1版): MLtuple, MLfloat, MLstring, MLparray, MLaxiom,
      深いパターン (Pcons/Ptuple/Prel)。 *)
From Stdlib Require Import String ZArith List.
From PyCert Require Import Common.
Import ListNotations.

(** 束縛名。[miniml.mli] の [ml_ident] と同じ。 *)
Inductive ml_ident : Type :=
| Dummy
| Id  (s : string)
| Tmp (s : string).

(** パターン。[Pusual g] は [Pcons (g, [Prel n; ...; Prel 1])] の略。
    [Pwild] の分岐は束縛変数を持たない ([ml_ident] の列が空) ものとする。 *)
Inductive ml_pattern : Type :=
| Pusual (g : global)
| Pwild.

Inductive ml_ast : Type :=
| MLrel   (n : nat)                         (* n >= 1 *)
| MLlam   (body : ml_ast)
| MLapp   (f : ml_ast) (args : list ml_ast)   (* args <> [] *)
| MLletin  (e1 e2 : ml_ast)
| MLglob  (g : global)
| MLcons  (g : global) (args : list ml_ast)  (* 飽和した適用 *)
| MLcase  (scrut : ml_ast) (brs : list (list ml_ident * ml_pattern * ml_ast))
    (* 分岐は [ml_branch] (下で定義)。[body] は、[ml_ident] の個数の変数を束縛した下で
       評価される。最後の変数が index 1 (json_one_pat の push_vars (List.rev_map ids) より)。 *)
| MLfix   (i : nat) (defs : list ml_ast)
    (* 相互再帰。各 def は全 fix 名を束縛した下で評価される。
       push_vars (List.rev ids) より、最後の def が index 1。 *)
| MLexn   (msg : string)
| MLdummy
| MLmagic (e : ml_ast)                       (* 実行時は恒等 *)
| MLuint  (n : Z)                           (* 0 <= n < 2^63 (Uint63) *).

(** 分岐。[miniml.mli] の [ml_branch] と同じ組。
    Rocq では、[ml_ast] と相互に定義する別名にできない (組は帰納型ではない) ので、
    [MLcase] の中に組を直接書き、ここで別名を付ける。 *)
Definition ml_branch : Type := (list ml_ident * ml_pattern * ml_ast)%type.

Inductive ml_decl : Type :=
| Dterm (g : global) (e : ml_ast)
| Dfix  (gs : list global) (es : list ml_ast).

