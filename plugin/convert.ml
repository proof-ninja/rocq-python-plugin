(** Rocq の MiniML ([Extraction_plugin.Miniml.ml_ast]) を、検証済みの翻訳
    ([Pycert_translate], theories/Translate.v から Extraction したもの) の入力
    [Pycert_translate.ml_ast] に変換する。ここも信頼の基盤 (TCB) に含まれる。

    MiniML.v の仮定を満たさないものは、黙って落とさずエラーにする。 *)
open Extraction_plugin
open Miniml
module T = Pycert_translate

let unsupported (what : string) =
  CErrors.user_err Pp.(str "rocq-python-plugin: unsupported construct: " ++ str what ++ str ".")

let char_list_of_string (s : string) : char list = List.init (String.length s) (String.get s)

let rec positive_of_zarith (n : Z.t) : T.positive =
  if Z.equal n Z.one then T.XH
  else if Z.is_even n then T.XO (positive_of_zarith (Z.shift_right n 1))
  else T.XI (positive_of_zarith (Z.shift_right n 1))

let z_of_zarith (n : Z.t) : T.z =
  match Z.sign n with
  | 0 -> T.Z0
  | 1 -> T.Zpos (positive_of_zarith n)
  | _ -> T.Zneg (positive_of_zarith (Z.neg n))

(** [Extract Constant] で与えられた定数: (Rocq 側の識別子, Python の式)。
    出力の冒頭に [g_<識別子> = <式>] の束縛として出力される (python_plugin.ml)。
    式はカリー化された 1 引数関数でなければならない (Python subset の呼び出し規約)。
    これらは検証されない (信頼の基盤)。[pp_struct] ごとに空にして集め直す。 *)
let customs : (string * string) list ref = ref []

(** 名前は Common.pp_global (Rocq 本体の名前解決・衝突回避) に従う。
    [pp_struct] はドライランと本番の 2 回呼ばれるので、どちらでも同じ呼び出しをする。 *)
let name (table : Common.State.t) (kind : Common.kind) (g : global) : char list =
  let id = Common.pp_global table kind g in
  if Table.is_custom g then begin
    match kind with
    | Common.Term ->
        if not (List.mem_assoc id !customs) then
          customs := (id, Table.find_custom g) :: !customs;
        char_list_of_string id
    | _ -> unsupported "Extract Inductive / Extract Inlined Constant on constructors"
  end else char_list_of_string id

let rec conv (table : Common.State.t) (a : ml_ast) : T.ml_ast =
  match a with
  | MLrel n -> T.MLrel n
  | MLapp (f, []) -> conv table f
  | MLapp (f, args) -> T.MLapp (conv table f, List.map (conv table) args)
  | MLlam (_, b) -> T.MLlam (conv table b)
  | MLletin (_, a1, a2) -> T.MLletin (conv table a1, conv table a2)
  | MLglob g -> T.MLglob (name table Common.Term g)
  | MLcons (_, g, args) -> T.MLcons (name table Common.Cons g, List.map (conv table) args)
  | MLcase (_, e, brs) -> T.MLcase (conv table e, List.map (conv_branch table) (Array.to_list brs))
  | MLfix (i, _, defs) -> T.MLfix (i, List.map (conv table) (Array.to_list defs))
  | MLexn s -> T.MLexn (char_list_of_string s)
  | MLdummy _ -> T.MLdummy
  | MLmagic a1 -> T.MLmagic (conv table a1)
  | MLuint i -> T.MLuint (z_of_zarith (Z.of_string (Uint63.to_string i)))
  | MLtuple _ -> unsupported "tuple"
  | MLaxiom _ -> unsupported "axiom"
  | MLfloat _ -> unsupported "float"
  | MLstring _ -> unsupported "primitive string"
  | MLparray _ -> unsupported "primitive array"

and conv_ident (i : ml_ident) : T.ml_ident =
  match i with
  | Dummy -> T.Dummy
  | Id s -> T.Id (char_list_of_string (Names.Id.to_string s))
  | Tmp s -> T.Tmp (char_list_of_string (Names.Id.to_string s))

(* [T.ml_branch] は抽出されない (別名の定義で、[translate_program] の型に現れない) ので、
   組の型を直接書く。Rocq の [A * B * C] は [(A * B) * C] なので、抽出された OCaml の型は
   [(ml_ident list * ml_pattern) * ml_ast] (miniml.mli の平らな 3 つ組 [A * B * C] とは違う)。 *)
and conv_branch table ((ids, pat, body) : ml_branch)
    : (T.ml_ident list * T.ml_pattern) * T.ml_ast =
  match pat with
  | Pusual g ->
      ((List.map conv_ident ids, T.Pusual (name table Common.Cons g)), conv table body)
  | Pwild ->
      if ids <> [] then unsupported "wildcard branch with bound variables"
      else (([], T.Pwild), conv table body)
  | Pcons _ | Ptuple _ | Prel _ -> unsupported "nested pattern"

(** 型宣言 ([Dind], [Dtype]) は Python では不要 (コンストラクタはタグ文字列) *)
let conv_decl (table : Common.State.t) (d : ml_decl) : T.ml_decl option =
  match d with
  | Dind _ | Dtype _ -> None
  | Dterm (r, _, _) when Table.is_custom r ->
      (* Extract Constant された定数の宣言。本体 (公理) は捨て、束縛を [customs] に登録する
         (宣言は参照より前に来るが、束縛は出力の冒頭にまとめて出す)。 *)
      ignore (name table Common.Term r); None
  | Dterm (r, a, _) -> Some (T.Dterm (name table Common.Term r, conv table a))
  | Dfix (rv, defs, _) ->
      Some (T.Dfix (List.map (name table Common.Term) (Array.to_list rv),
                     List.map (conv table) (Array.to_list defs)))
