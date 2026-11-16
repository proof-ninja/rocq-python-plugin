(** Python subset (Pycert_translate.pystmt) の印字。
    ここは信頼の基盤 (TCB) に含まれる。各ノードは Python 構文 1 つに 1 対 1 で対応する。 *)
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
  | XH -> Z.one
  | XO p -> Z.shift_left (zarith_of_positive p) 1
  | XI p -> Z.succ (Z.shift_left (zarith_of_positive p) 1)

let string_of_z = function
  | Z0 -> "0"
  | Zpos p -> Z.to_string (zarith_of_positive p)
  | Zneg p -> Z.to_string (Z.neg (zarith_of_positive p))

(* 後置 ([..] や (..)) の対象になる式は、名前・呼び出し・添字・タプルのみ。
   それ以外は括弧で囲む。 *)
let rec pyexpr (e : pyexpr) : string =
  match e with
  | PyName x -> pident x
  | PyNone -> "None"
  | PyInt n -> string_of_z n
  | PyCon (tag, []) -> "(" ^ py_string (string_of_char_list tag) ^ ",)"
  | PyCon (tag, args) ->
      "(" ^ String.concat ", " (py_string (string_of_char_list tag) :: List.map pyexpr args) ^ ")"
  | PyField (e, i) -> head e ^ "[" ^ string_of_int i ^ "]"
  | PyCall (f, a) -> head f ^ "(" ^ pyexpr a ^ ")"

and head e =
  match e with
  | PyName _ | PyCon _ | PyField _ | PyCall _ -> pyexpr e
  | PyNone | PyInt _ -> "(" ^ pyexpr e ^ ")"

(* 文を行のリストに印字する (indent は半角空白の数) *)
let rec stmts (ind : int) (ss : pystmt list) : string list =
  match ss with
  | [] -> [String.make ind ' ' ^ "pass"]
  | _ -> List.concat_map (stmt ind) ss

and stmt (ind : int) (s : pystmt) : string list =
  let pad = String.make ind ' ' in
  match s with
  | PyAssign (x, e) -> [pad ^ pident x ^ " = " ^ pyexpr e]
  | PyReturn e -> [pad ^ "return " ^ pyexpr e]
  | PyRaise m -> [pad ^ "raise Exception(" ^ py_string (string_of_char_list m) ^ ")"]
  | PyDefs fs ->
      List.concat_map (fun (PyDef (f, x, body)) ->
        (pad ^ "def " ^ pident f ^ "(" ^ pident x ^ "):") :: stmts (ind + 4) body) fs
  | PyIfCon (e, tag, t, f) -> if_chain ind "if" e tag t f

and if_chain ind kw e tag t f =
  let pad = String.make ind ' ' in
  let cond = head e ^ "[0] == " ^ py_string (string_of_char_list tag) in
  let head_line = pad ^ kw ^ " " ^ cond ^ ":" in
  let then_lines = stmts (ind + 4) t in
  match f with
  | [PyIfCon (e2, tag2, t2, f2)] ->
      (head_line :: then_lines) @ if_chain ind "elif" e2 tag2 t2 f2
  | _ -> (head_line :: then_lines) @ ((pad ^ "else:") :: stmts (ind + 4) f)

let lines_of_module (m : pystmt list) : string list = List.concat_map (stmt 0) m
