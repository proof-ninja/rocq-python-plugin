(** MiniML → Python subset の翻訳。

    ANF 風: 関数適用・コンストラクタ・let・case の部分式は、すべて新しい
    局所変数に左から右へ順に代入してから使う。これにより MiniML の評価順
    (左から右) を保つ。MiniML の [MRel] (1 始まり) は、文脈 [ctx] (先頭が
    index 1) から Python の変数名に写す。

    [k] は fresh な [PyLocal] 用のカウンタで、使うたびに増やして返す。

    注: [list mexpr] / [list mbranch] を走査する部分は、Rocq の構造再帰の
    制約 (入れ子型の要素が部分項と認められるのは局所 [fix] 内のみ) により、
    [tr] の中の局所 [fix] として書いている。 *)
From Stdlib Require Import String ZArith List.
From PyCert Require Import Common Python.
From RocqPython Require Import MiniML.
Import ListNotations.

(** 結果の置き先 *)
Inductive dest : Type :=
| TRet                    (* return する (関数末尾) *)
| TAssign (x : pident).   (* x に代入する *)

Definition finish (d : dest) (a : pyexpr) : list pystmt :=
  match d with
  | TRet => [PyReturn a]
  | TAssign x => [PyAssign x a]
  end.

Fixpoint tr (d : dest) (ctx : list pident) (k : nat) (e : mexpr) {struct e}
  : nat * list pystmt :=
  match e with
  | MRel n => (k, finish d (PyName (nth (pred n) ctx (PyLocal 0))))
  | MLam b =>
      (* クロージャは直前の def に巻き上げる *)
      let f := PyLocal k in
      let x := PyLocal (S k) in
      let '(k1, body) := tr TRet (x :: ctx) (S (S k)) b in
      (k1, PyDefs [PyDef f x body] :: finish d (PyName f))
  | MApp f args =>
      let tf := PyLocal k in
      let '(k1, s1) := tr (TAssign tf) ctx (S k) f in
      (* 各引数を fresh 変数に左から右へ代入し、その変数の列を得る *)
      let '(k2, s2, as_) :=
        (fix go (k : nat) (es : list mexpr) {struct es}
           : nat * list pystmt * list pyexpr :=
           match es with
           | [] => (k, [], [])
           | e1 :: rest =>
               let t := PyLocal k in
               let '(k1, s1) := tr (TAssign t) ctx (S k) e1 in
               let '(k2, s2, ts) := go k1 rest in
               (k2, s1 ++ s2, PyName t :: ts)
           end) k1 args in
      (k2, s1 ++ s2 ++ finish d (fold_left PyCall as_ (PyName tf)))
  | MLet e1 e2 =>
      let x := PyLocal k in
      let '(k1, s1) := tr (TAssign x) ctx (S k) e1 in
      let '(k2, s2) := tr d (x :: ctx) k1 e2 in
      (k2, s1 ++ s2)
  | MGlob g => (k, finish d (PyName (PyGlobal g)))
  | MCons g args =>
      let '(k1, s1, as_) :=
        (fix go (k : nat) (es : list mexpr) {struct es}
           : nat * list pystmt * list pyexpr :=
           match es with
           | [] => (k, [], [])
           | e1 :: rest =>
               let t := PyLocal k in
               let '(k1, s1) := tr (TAssign t) ctx (S k) e1 in
               let '(k2, s2, ts) := go k1 rest in
               (k2, s1 ++ s2, PyName t :: ts)
           end) k args in
      (k1, s1 ++ finish d (PyCon g as_))
  | MCase s brs =>
      let ts := PyLocal k in
      let '(k1, ss) := tr (TAssign ts) ctx (S k) s in
      (* 分岐列: ts のタグで if/else の連鎖にする。
         最後は match failure の raise (MiniML では stuck なので定理には影響しない) *)
      let '(k2, ib) :=
        (fix go (k : nat) (bs : list mbranch) {struct bs}
           : nat * list pystmt :=
           match bs with
           | [] => (k, [PyRaise "match failure"%string])
           | MBr p n body :: rest =>
               match p with
               | MPUsual g =>
                   let xs := map PyLocal (seq k n) in
                   let binds :=
                     map (fun ix => PyAssign (snd ix) (PyField (PyName ts) (S (fst ix))))
                         (combine (seq 0 n) xs) in
                   (* 最後の引数が index 1 *)
                   let '(k1, sb) := tr d (rev xs ++ ctx) (k + n) body in
                   let '(k2, sr) := go k1 rest in
                   (k2, [PyIfCon (PyName ts) g (binds ++ sb) sr])
               | MPWild => tr d ctx k body
               end
           end) k1 brs in
      (k2, ss ++ ib)
  | MFix i defs =>
      let n := length defs in
      let names := map PyLocal (seq k n) in
      (* 最後の def が index 1 *)
      let fixctx := rev names ++ ctx in
      (* 各 def を関数名 (names の先頭から順) に対応させて def にする。
         本体が [MLam] でないものは MiniML では適用時に stuck なので、
         Python では raise する本体にしておく。 *)
      let '(k1, pds) :=
        (fix go (k : nat) (ns : list pident) (es : list mexpr) {struct es}
           : nat * list pdef :=
           match es with
           | [] => (k, [])
           | e1 :: rest =>
               let f := hd (PyLocal 0) ns in
               let x := PyLocal k in
               let '(k1, body) :=
                 match e1 with
                 | MLam b => tr TRet (x :: fixctx) (S k) b
                 | _ => (S k, [PyRaise "unsupported fix body"%string])
                 end in
               let '(k2, ds) := go k1 (tl ns) rest in
               (k2, PyDef f x body :: ds)
           end) (k + n) names defs in
      (k1, PyDefs pds :: finish d (PyName (nth i names (PyLocal 0))))
  | MExn m => (k, [PyRaise m])
  | MDummy => (k, finish d PyNone)
  | MMagic e1 => tr d ctx k e1
  | MUint n => (k, finish d (PyInt n))
  end.

(** トップレベルの MDFix: 関数名はグローバル、本体の文脈は引数のみ *)
Fixpoint tr_gdefs (k : nat) (gs : list global) (es : list mexpr)
  : nat * list pdef :=
  match gs, es with
  | g :: gs', e :: es' =>
      let x := PyLocal k in
      let '(k1, body) :=
        match e with
        | MLam b => tr TRet [x] (S k) b
        | _ => (S k, [PyRaise "unsupported fix body"%string])
        end in
      let '(k2, ds) := tr_gdefs k1 gs' es' in
      (k2, PyDef (PyGlobal g) x body :: ds)
  | _, _ => (k, [])
  end.

Definition tr_decl (k : nat) (d : mdecl) : nat * list pystmt :=
  match d with
  | MDTerm g e => tr (TAssign (PyGlobal g)) [] k e
  | MDFix gs es => let '(k1, ds) := tr_gdefs k gs es in (k1, [PyDefs ds])
  end.

Fixpoint tr_prog (k : nat) (ds : mprogram) : pymodule :=
  match ds with
  | [] => []
  | d :: rest =>
      let '(k1, s) := tr_decl k d in
      s ++ tr_prog k1 rest
  end.
