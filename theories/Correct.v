(** 翻訳の正しさ (前向きシミュレーション) の主張。

    *** 注意: このファイルの定理はすべて [Admitted] (未証明) である。***
    主張が実際に成り立つか (追加の仮定が要らないか) も未確認。 *)
From Stdlib Require Import String ZArith List.
From PyCert Require Import Common Python PythonSem.
From RocqPython Require Import MiniML MiniMLSem Translate.
Import ListNotations.

(** * 値・環境の対応関係

    関数 (クロージャ) は、「関数として同じ振る舞いをする」という論理関係ではなく、
    翻訳関係 (本体が翻訳の結果であり、環境が対応している) で定義する。
    論理関係は、帰納型の負の位置に現れて定義できないため。

    Python の変数名は、束縛の入れ子の深さで決まる ([Translate.v])。 *)

Inductive value_relation : ml_val -> py_val -> Prop :=
| VR_cons g vs pvs :
    values_relation vs pvs -> value_relation (VCons g vs) (PyVTuple (PyVStr g :: pvs))
| VR_uint n :
    value_relation (VUint n) (PyVInt n)
| VR_dummy :
    value_relation VDummy PyVNone
| VR_clos env body py_env :
    environment_relation env py_env ->
    value_relation (VClos env body)
      (PyVClos py_env (PyLocal (nesting_depth env))
         (translate_aux (S (nesting_depth env)) body))
| VR_fix env defs i py_env fs :
    environment_relation env py_env ->
    translate_aux (nesting_depth env) (MLfix i defs) = PyLetRec fs i ->
    value_relation (VFix env defs i) (PyVRec py_env fs i)

with values_relation : list ml_val -> list py_val -> Prop :=
| VsR_nil : values_relation [] []
| VsR_cons v pv vs pvs :
    value_relation v pv -> values_relation vs pvs ->
    values_relation (v :: vs) (pv :: pvs)

(** [environment_relation ml_env py_env]: MiniML の環境 [ml_env] (局所とグローバル) が、
    Python の環境 [py_env] に対応する。局所環境の、古い方から [k] 番目 ([k = 0, 1, ...]) の値は、
    Python の変数 [v(k)] の値に、各グローバル [g] は、変数 [PyGlobal g] の値に対応する。 *)
with environment_relation : environment -> penv -> Prop :=
| ER ml_env py_env :
    locals_relation (locals_of ml_env) py_env ->
    globals_relation (globals_of ml_env) py_env ->
    environment_relation ml_env py_env

(** 局所環境: 先頭の値は、それより古い値の数 ([length vs]) を番号とする変数 *)
with locals_relation : list ml_val -> penv -> Prop :=
| LR_nil py_env : locals_relation [] py_env
| LR_cons v vs py_env pv :
    plookup (PyLocal (length vs)) py_env = Some pv -> value_relation v pv ->
    locals_relation vs py_env ->
    locals_relation (v :: vs) py_env

with globals_relation : genv -> penv -> Prop :=
| GR G py_env :
    (forall g v, glookup G g = Some v ->
       exists pv, plookup (PyGlobal g) py_env = Some pv /\ value_relation v pv) ->
    globals_relation G py_env.

(** 評価結果の対応 (成功なら値が対応し、例外なら同じメッセージ) *)
Definition result_relation (ml_result : result ml_val) (py_result : result py_val) : Prop :=
  match ml_result, py_result with
  | Ok v, Ok pv => value_relation v pv
  | Error m, Error m' => m = m'
  | _, _ => False
  end.

(** * 式の翻訳の正しさ *)

(** 補題 (帰納法の本体)。深さが一般の値 ([nesting_depth ml_env]) でも成り立つ形でないと、
    部分式についての帰納法の仮定が使えない。 *)
Lemma translate_aux_correct py_env ml_env ml_expr v :
  evaluate ml_env ml_expr (Ok v) ->
  environment_relation ml_env py_env ->
  exists pv,
    pyevaluate py_env (translate_aux (nesting_depth ml_env) ml_expr) (Ok pv) /\
    value_relation v pv.
Proof.
Admitted.

(** MiniML の式 [ml_expr] が、グローバル環境 [ml_globals] だけの環境 ([init_env ml_globals])
    のもとで値 [v] に評価される ([Ok v]) なら、[ml_expr] を翻訳した Python の式を、
    対応する Python の環境 [py_env] で評価すると、[v] に対応する値になる。
    局所変数がないので、環境の対応は、グローバル環境の対応 ([globals_relation]) だけでよい。

    前提を [Ok] の場合に限るのは、Rocq の型検査を通った項から作った MiniML は、
    停止し、例外にも行き詰まりにもならないため (Rocq 処理系が正しいという仮定の一部)。
    [evaluate] 自体の定義は変えない。 *)
Theorem translate_correct py_env ml_globals ml_expr v :
  evaluate (init_env ml_globals) ml_expr (Ok v) ->
  globals_relation ml_globals py_env ->
  exists pv, pyevaluate py_env (translate ml_expr) (Ok pv) /\ value_relation v pv.
Proof.
  intros Hevaluate Hglobals.
  exact (translate_aux_correct py_env (init_env ml_globals) ml_expr v Hevaluate
           (ER (init_env ml_globals) py_env (LR_nil py_env) Hglobals)).
Qed.

(** * プログラムの翻訳の正しさ *)

(** 未定義 (TODO): 次を含む整形条件。
    - グローバルの参照は、より前の宣言か同じ fix 群のものに限る
      (Python 側の簡易モデルは作られた時点の環境を捕捉するため、前方参照を扱えない)
    - [Pusual] の分岐の [ml_ident] の個数が、コンストラクタの引数個数と一致する
    - [Pwild] の分岐の [ml_ident] の列が空
    - [MLfix] の各 def が [MLlam] *)
Parameter well_formed_program : list ml_decl -> Prop.

(** ** 初期のグローバル環境 ([Extraction Constant] で指定した項)

    [Extraction Constant] の項は、Python のソースの文字列として、出力の冒頭に
    [g_<名前> = <式>] で出力される。翻訳器は、その式も、Rocq の公理の本体も見ない
    ([py_expr] で表現しない。検証の対象外)。そこで、定理は、初期のグローバル環境を引数にとる:

    - [ml_globals0] (MiniML 側) と [py_env0] (Python 側) が、[globals_relation] で対応する
      ([Extraction Constant] した項の Python の値が、MiniML 側の値に対応するという、
      **信頼の基盤の仮定**。定理は、この仮定が成り立つ範囲でだけ成り立つ)
    - [py_env0] は、出力の冒頭の補助関数 [raise_] を束縛している ([prelude_env] の内容)

    これらは、下の Section [Externals] の [Parameter] / [Axiom] として宣言する。
    外部の項を何も使わないときは、[ml_globals0 = []] と [py_env0 = prelude_env] で、
    どちらの公理も成り立つ。

    制限 (未対応): 外部の項が、関数の値 (呼び出される Python の関数) のときの対応は、まだない。
    [value_relation] の関数の値は、翻訳された本体のクロージャだけで、外部の Python の関数を
    呼ぶ規則が、[pycall] にも MiniML の [apply_closure] にもない。いまは、外部の項が
    関数でない値 (データ) のときだけ、[globals_relation] を満たせる。 *)
Section Externals.

  (** 初期のグローバル環境 (MiniML 側と Python 側)。信頼の基盤の公理として宣言するので、
      定理の statement には現れない ([Print Assumptions] には現れる)。 *)
  Parameter ml_globals0 : genv.
  Parameter py_env0 : penv.

  (** 外部の項の対応 (信頼の基盤) *)
  Axiom externals_related : globals_relation ml_globals0 py_env0.

  (** 補助関数 [raise_] が束縛されている *)
  Axiom prelude_included : plookup PyRuntimeRaise py_env0 = Some PyVRaise.

  Theorem translate_program_correct :
    forall ml_program final_globals,
      well_formed_program ml_program ->
      run ml_globals0 ml_program (Ok final_globals) ->
      exists py_env,
        pyrun py_env0 (translate_program ml_program) (Ok py_env) /\
        globals_relation final_globals py_env.
  Proof.
  Admitted.

  Theorem translate_program_correct_error :
    forall ml_program msg,
      well_formed_program ml_program ->
      run ml_globals0 ml_program (Error msg) ->
      pyrun py_env0 (translate_program ml_program) (Error msg).
  Proof.
  Admitted.

End Externals.
