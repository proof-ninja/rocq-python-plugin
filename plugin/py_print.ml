(** Python subset (Pycert_translate.pyexpr / pystmt) の印字。
    ここは信頼の基盤 (TCB) に含まれる。ノードは Python の ast ノード (Name, Tuple,
    Subscript, Compare, IfExp, Call, Lambda) に 1 対 1 で対応する (例外: PyLetRec)。
    例外は、出力の冒頭の補助関数 raise_ ([runtime_prelude]) の呼び出しで表す。

    式は、すべて括弧で囲んで印字する (優先順位の誤りを避ける)。括弧の中の改行は、
    Python では自由なので、読みやすさのために、lambda の本体や if 式の枝で改行する。 *)
(* zarith の Z。[open Pycert_translate] は、Rocq の Z モジュール (Z.of_nat などを含む、
   抽出されたもの) を持ち込み、zarith の [Z] を隠すので、先に別名を付けておく。 *)
module BigInt = Z

open Pycert_translate

let string_of_char_list l = String.of_seq (List.to_seq l)

(* 識別子の単射なエスケープ: '_' -> "__", '\'' -> "_q", '.' -> "_d",
   英数字以外 -> "_xHH" (バイト単位)。結果は常に ASCII の識別子片になる。 *)
let mangle (s : string) : string =
  let b = Buffer.create (String.length s) in
  String.iter (fun c ->
    match c with
    | 'a'..'z' | 'A'..'Z' | '0'..'9' -> Buffer.add_char b c
    | '_' -> Buffer.add_string b "__"
    | '\'' -> Buffer.add_string b "_q"
    | '.' -> Buffer.add_string b "_d"
    | c -> Buffer.add_string b (Printf.sprintf "_x%02x" (Char.code c))) s;
  Buffer.contents b

(* グローバルの Python 識別子 (PyGlobal g の印字と、Extract Constant の束縛で共通) *)
let global_ident (s : string) : string = "g_" ^ mangle s

let pident = function
  | PyLocal n -> "v" ^ string_of_int n
  | PyGlobal g -> global_ident (string_of_char_list g)
  | PyRuntimeRaise -> "raise_"

(* Python の文字列リテラル (ダブルクォート)。OCaml の %S は使わない
   (10 進エスケープが Python と意味が違うため)。 *)
let py_string (s : string) : string =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter (fun c ->
    match c with
    | '\\' -> Buffer.add_string b "\\\\"
    | '"' -> Buffer.add_string b "\\\""
    | '\n' -> Buffer.add_string b "\\n"
    | '\r' -> Buffer.add_string b "\\r"
    | '\t' -> Buffer.add_string b "\\t"
    | c when Char.code c < 32 || Char.code c = 127 ->
        Buffer.add_string b (Printf.sprintf "\\x%02x" (Char.code c))
    | c -> Buffer.add_char b c) s;
  Buffer.add_char b '"';
  Buffer.contents b

let rec zarith_of_positive = function
  | XH -> BigInt.one
  | XO p -> BigInt.shift_left (zarith_of_positive p) 1
  | XI p -> BigInt.succ (BigInt.shift_left (zarith_of_positive p) 1)

let string_of_z = function
  | Z0 -> "0"
  | Zpos p -> BigInt.to_string (zarith_of_positive p)
  | Zneg p -> BigInt.to_string (BigInt.neg (zarith_of_positive p))

let newline (ind : int) : string = "\n" ^ String.make ind ' '

(* [ind]: 現在の行のインデント (半角空白の数)。改行するとき、[ind + 4] に揃える。
   後置 ([..] や (..)) の対象になる式は、括弧で囲まれた式・名前・呼び出し・添字。 *)
let rec pyexpr (ind : int) (e : pyexpr) : string =
  match e with
  | PyName x -> pident x
  | PyNone -> "None"
  | PyInt n ->
      let s = string_of_z n in
      if String.length s > 0 && s.[0] = '-' then "(" ^ s ^ ")" else s
  | PyStr s -> py_string (string_of_char_list s)
  | PyTuple [] -> "()"
  | PyTuple [e] -> "(" ^ pyexpr ind e ^ ",)"
  | PyTuple es -> "(" ^ String.concat ", " (List.map (pyexpr ind) es) ^ ")"
  | PySubscript (e, idx) -> head ind e ^ "[" ^ pyexpr ind idx ^ "]"
  | PyCompare (l, PyEq, r) -> "(" ^ pyexpr ind l ^ " == " ^ pyexpr ind r ^ ")"
  | PyCall (f, a) -> head ind f ^ "(" ^ pyexpr ind a ^ ")"
  | PyLambda (x, body) ->
      "(lambda " ^ pident x ^ ":" ^ newline (ind + 4) ^ pyexpr (ind + 4) body ^ ")"
  | PyIfExp (test, body, orelse) ->
      "(" ^ pyexpr (ind + 4) body
      ^ newline (ind + 4) ^ "if " ^ pyexpr (ind + 4) test
      ^ newline (ind + 4) ^ "else " ^ pyexpr (ind + 4) orelse ^ ")"
  | PyLetRec (fs, i) ->
      (* 関数名は walrus (:=) で束縛する。名前が兄弟の式と衝突しないよう、すぐ呼ぶ lambda の
         中に閉じ込める:
           (lambda: ((f0 := lambda x0: ...), (f1 := lambda x1: ...))[i])()
         (関数が 1 つのときは、タプルも添字も要らない) *)
      let inner = ind + 8 in
      let body =
        match fs, i with
        | [d], 0 -> def_walrus inner d
        | _ ->
            "(" ^ String.concat ("," ^ newline inner) (List.map (def_walrus inner) fs)
            ^ ")[" ^ string_of_int i ^ "]"
      in
      "(lambda: " ^ body ^ ")()"

and def_walrus ind (PyDef (f, x, body)) =
  "(" ^ pident f ^ " := lambda " ^ pident x ^ ":" ^ newline (ind + 4)
  ^ pyexpr (ind + 4) body ^ ")"

and head ind e =
  match e with
  | PyNone | PyInt _ -> "(" ^ pyexpr ind e ^ ")"
  | _ -> pyexpr ind e

(* 出力の冒頭に置く補助関数。[PyRuntimeRaise] ([raise_]) の定義 (Python の [raise] は文で、
   式にならないため、関数にして呼び出す)。 *)
let runtime_prelude : string list =
  ["def raise_(m):"; "    raise Exception(m)"]

(* トップレベルの文を、行のリストに印字する。右辺は、全体を括弧で囲む (lambda の本体で
   改行できるように)。 *)
let stmt (s : pystmt) : string list =
  match s with
  | PyAssign (x, e) -> [pident x ^ " = (" ^ pyexpr 4 e ^ ")"]
  | PyDefs fs ->
      List.map (fun (PyDef (f, x, body)) ->
        pident f ^ " = (lambda " ^ pident x ^ ":" ^ newline 4 ^ pyexpr 4 body ^ ")") fs

let lines_of_module (m : pystmt list) : string list = List.concat_map stmt m
