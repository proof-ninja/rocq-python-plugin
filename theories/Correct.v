(** 翻訳の正しさ (前向きシミュレーション) の主張。

    *** 注意: このファイルの定理はすべて [Admitted] (未証明) である。***
    主張が実際に成り立つか (追加の仮定が要らないか) も未確認。 *)
From Stdlib Require Import String ZArith List.
From PyCert Require Import Common Python PythonSem.
From RocqPython Require Import MiniML MiniMLSem Translate.
Import ListNotations.

(** * 値・環境の対応関係

    クロージャは「関数として同じ振る舞いをする」という論理関係ではなく、
    翻訳関係 (本体が翻訳の結果であり、環境が対応している) で定義する。
    論理関係は帰納型の負の位置に現れて定義できないため。 *)

Inductive val_rel : mval -> pval -> Prop :=
| VR_cons g vs pvs :
    vals_rel vs pvs -> val_rel (VCons g vs) (PyVTuple g pvs)
| VR_uint n :
    val_rel (VUint n) (PyVInt n)
| VR_dummy :
    val_rel VDummy PyVNone
| VR_clos env b ctx penv fs j f x body k k' :
    (* [MLam] の巻き上げ (fs = [def]) と、トップレベル [MDFix] の
       関数 (env = ctx = []) の両方を表す *)
    env_rel ctx env penv ->
    nth_error fs j = Some (PyDef f x body) ->
    tr TRet (x :: ctx) k b = (k', body) ->
    val_rel (VClos env b) (PyVRec penv fs j)
| VR_fix env defs i ctx penv fs rest k k' :
    env_rel ctx env penv ->
    tr TRet ctx k (MFix i defs) = (k', PyDefs fs :: rest) ->
    val_rel (VFix env defs i) (PyVRec penv fs i)

with vals_rel : list mval -> list pval -> Prop :=
| VsR_nil : vals_rel [] []
| VsR_cons v pv vs pvs :
    val_rel v pv -> vals_rel vs pvs -> vals_rel (v :: vs) (pv :: pvs)

(** [env_rel ctx env penv]: MiniML 環境 [env] の i 番目の値が、
    Python 環境 [penv] の変数 [ctx[i]] の値に対応する。 *)
with env_rel : list pident -> list mval -> penv -> Prop :=
| ER_nil penv : env_rel [] [] penv
| ER_cons x ctx v env penv pv :
    plookup x penv = Some pv -> val_rel v pv ->
    env_rel ctx env penv -> env_rel (x :: ctx) (v :: env) penv.

(** グローバル環境の対応 *)
Definition genv_rel (G : genv) (penv : penv) : Prop :=
  forall g v, glookup G g = Some v ->
    exists pv, plookup (PyGlobal g) penv = Some pv /\ val_rel v pv.

(** k 未満の番号しか [PyLocal] が使われていない (fresh 性) *)
Definition fresh_from (k : nat) (penv : penv) : Prop :=
  forall j pv, plookup (PyLocal j) penv = Some pv -> j < k.

(** 評価結果と、実行結果 (置き先 d) の対応 *)
Definition out_rel (d : dest) (r : result mval) (o : pout) : Prop :=
  match r with
  | Error m => o = ORaise m
  | Ok v =>
      exists pv, val_rel v pv /\
        match d with
        | TRet => o = ORet pv
        | TAssign x => exists penv', o = OFall penv' /\ plookup x penv' = Some pv
        end
  end.

(** * 式の翻訳の正しさ *)
Theorem tr_correct :
  forall G env e r,
    ev G env e r ->
    forall d ctx k k' ss penv,
      tr d ctx k e = (k', ss) ->
      env_rel ctx env penv ->
      genv_rel G penv ->
      fresh_from k penv ->
      exists o, pexec_block penv ss o /\ out_rel d r o.
Proof.
Admitted.

(** * プログラムの翻訳の正しさ *)

(** 未定義 (TODO): 次を含む整形条件。
    - グローバルの参照は、より前の宣言か同じ fix 群のものに限る
      (Python 側の簡易モデルは def 時点の環境を捕捉するため、前方参照を扱えない)
    - [MBr] の変数個数がコンストラクタの引数個数と一致する
    - [MPWild] の分岐の nvars = 0
    - [MFix] の各 def が [MLam] *)
Parameter wf_prog : mprogram -> Prop.

Theorem tr_prog_correct_ok :
  forall ds G',
    wf_prog ds ->
    run [] ds (Ok G') ->
    exists penv', pexec_block [] (tr_prog 0 ds) (OFall penv') /\ genv_rel G' penv'.
Proof.
Admitted.

Theorem tr_prog_correct_err :
  forall ds m,
    wf_prog ds ->
    run [] ds (Error m) ->
    pexec_block [] (tr_prog 0 ds) (ORaise m).
Proof.
Admitted.
