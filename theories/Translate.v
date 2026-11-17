(** MiniML → Python subset の翻訳。MiniML の式を、Python の **式** に翻訳する。

    - [let x = e1 in e2] は [(lambda x: e2')(e1')]、関数は [lambda]、分岐は [if] 式、
      例外は式として投げる、再帰関数の群は [PyLetRec]。
    - 関数適用 [f a b] は [f'(a')(b')] (Python と同じ評価順は、MiniMLSem.v で合わせてある)。
    - **Python の変数名は、束縛の入れ子の深さ [depth] で決まる**: [depth] 個の束縛が
      スコープにあるとき、MiniML の [MLrel n] (1 始まり。1 が直前の束縛) は、
      Python の変数 [v(depth - n)] になる。新しく束縛する変数は [v(depth)]。
      そのため、変数名の表も、新しい名前を作るカウンタも要らない。

    注: [list ml_ast] / [list ml_branch] を走査する部分は、Rocq の構造再帰の
    制約 (入れ子型の要素が部分項と認められるのは局所 [fix] 内のみ) により、
    [translate_aux] の中の局所 [fix] として書いている。 *)
From Stdlib Require Import String ZArith List.
From PyCert Require Import Common Python.
From RocqPython Require Import MiniML.
Import ListNotations.

(** 例外を投げる式: 補助関数の呼び出し [raise_("msg")] *)
Definition py_raise (msg : string) : py_expr :=
  PyCall (PyName PyRuntimeRaise) (PyStr msg).

(** [lams [x1; x2] body] は [lambda x1: lambda x2: body] *)
Fixpoint lams (xs : list pident) (body : py_expr) : py_expr :=
  match xs with
  | [] => body
  | x :: rest => PyLambda x (lams rest body)
  end.

(** コンストラクタの引数 (フィールド) を、[PySubscript] で取り出して、順に変数に束縛する:
    [bind_fields t [x1; x2] body] は [(lambda x1: lambda x2: body)(t[1])(t[2])]。
    フィールドの取り出し [t[i]] は、すべて lambda の外で評価されるので、[x1] が [t] と
    同じ名前でも、問題ない。 *)
Definition bind_fields (t : pident) (xs : list pident) (body : py_expr) : py_expr :=
  fold_left PyCall
    (map (fun i => PySubscript (PyName t) (PyInt (Z.of_nat (S i)))) (seq 0 (length xs)))
    (lams xs body).

(** 再帰の本体。[depth] は、いまスコープにある局所変数 (束縛) の個数。 *)
Fixpoint translate_aux (depth : nat) (ml_expr : ml_ast) {struct ml_expr} : py_expr :=
  match ml_expr with
  | MLrel n => PyName (PyLocal (depth - n))
  | MLlam body => PyLambda (PyLocal depth) (translate_aux (S depth) body)
  | MLapp f args =>
      fold_left PyCall
        ((fix go (es : list ml_ast) : list py_expr :=
            match es with
            | [] => []
            | e1 :: rest => translate_aux depth e1 :: go rest
            end) args)
        (translate_aux depth f)
  | MLletin e1 e2 =>
      PyCall (PyLambda (PyLocal depth) (translate_aux (S depth) e2)) (translate_aux depth e1)
  | MLglob g => PyName (PyGlobal g)
  | MLcons g args =>
      PyTuple
        (PyStr g ::
         (fix go (es : list ml_ast) : list py_expr :=
            match es with
            | [] => []
            | e1 :: rest => translate_aux depth e1 :: go rest
            end) args)
  | MLcase scrutinee branches =>
      (* 値を 1 度だけ評価して t に束縛し、t のタグで if 式の連鎖にする。t は、MiniML の
         変数ではないが、次に束縛される変数と同じ名前 v(depth) を使う (t の使用は、
         その変数が束縛される lambda の外だけなので、衝突しない)。
         最後は match failure の例外 (MiniML では stuck なので定理には影響しない) *)
      let t := PyLocal depth in
      let chain :=
        (fix go (bs : list ml_branch) {struct bs} : py_expr :=
           match bs with
           | [] => py_raise "match failure"%string
           | (ids, p, body) :: rest =>
               match p with
               | Pusual g =>
                   (* フィールドは v(depth) .. v(depth + n - 1)。最後の引数が index 1 *)
                   let n := length ids in
                   let xs := map PyLocal (seq depth n) in
                   PyIfExp
                     (PyCompare (PySubscript (PyName t) (PyInt 0)) PyEq (PyStr g))
                     (bind_fields t xs (translate_aux (depth + n) body)) (go rest)
               | Pwild => translate_aux depth body
               end
           end) branches in
      PyCall (PyLambda t chain) (translate_aux depth scrutinee)
  | MLfix i defs =>
      (* 関数 j は v(depth + j)、引数は v(depth + n)。最後の関数が index 2、引数が index 1。
         本体が [MLlam] でないものは MiniML では適用時に stuck なので、
         Python では例外を投げる本体にしておく。 *)
      let n := length defs in
      PyLetRec
        ((fix go (j : nat) (es : list ml_ast) {struct es} : list pydef :=
            match es with
            | [] => []
            | e1 :: rest =>
                PyDef (PyLocal (depth + j)) (PyLocal (depth + n))
                  (match e1 with
                   | MLlam b => translate_aux (S (depth + n)) b
                   | _ => py_raise "unsupported fix body"%string
                   end)
                :: go (S j) rest
            end) 0 defs)
        i
  | MLexn m => py_raise m
  | MLdummy => PyNone
  | MLmagic e1 => translate_aux depth e1
  | MLuint n => PyInt n
  end.

(** 局所変数のない (閉じた) 式の翻訳。深さ 0 から始める。 *)
Definition translate (ml_expr : ml_ast) : py_expr := translate_aux 0 ml_expr.

(** トップレベルの Dfix: 関数名はグローバル、引数は v0 *)
Fixpoint translate_global_defs (gs : list global) (es : list ml_ast) : list pydef :=
  match gs, es with
  | g :: gs', e :: es' =>
      PyDef (PyGlobal g) (PyLocal 0)
        (match e with
         | MLlam b => translate_aux 1 b
         | _ => py_raise "unsupported fix body"%string
         end)
      :: translate_global_defs gs' es'
  | _, _ => []
  end.

Definition translate_decl (d : ml_decl) : list pystmt :=
  match d with
  | Dterm g e => [PyAssign (PyGlobal g) (translate e)]
  | Dfix gs es => [PyDefs (translate_global_defs gs es)]
  end.

Definition translate_program (ds : list ml_decl) : pymodule :=
  flat_map translate_decl ds.
