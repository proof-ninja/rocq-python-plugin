(** MiniML の big-step 意味論 (環境 + クロージャ、正格、左から右)。

    環境 [environment] は、局所環境 (de Bruijn index で参照する値の列) と、
    グローバル環境 (名前から値への対応) を、1 つにまとめたもの。
    クロージャは、作られた時点の環境 (グローバルを含む) を捕捉する。

    関数適用 [MLapp f [a1; a2]] は、Python の [f(a1)(a2)] と同じ順序で評価する:
    [f] を評価し、[a1] を評価して適用し、その結果に対して [a2] を評価して適用する。
    (抽出される式は副作用のない純粋なものなので、すべての引数を先に評価する場合と、
    結果は変わらない。) *)
From Stdlib Require Import String ZArith List Bool.
From PyCert Require Import Common.
From RocqPython Require Import MiniML.
Import ListNotations.

Inductive mval : Type :=
| VCons (g : global) (vs : list mval)
| VUint (n : Z)
| VDummy
| VClos (env : environment) (body : ml_ast)
| VFix  (env : environment) (defs : list ml_ast) (i : nat)
  (* [VFix env defs i]: fix 群の i 番目の関数。適用時に展開する。 *)
| VGFix (env : environment) (gs : list global) (bodies : list ml_ast) (j : nat)
  (* [VGFix env gs bodies j]: トップレベルの fix 群 (名前 gs) の j 番目の関数。 *)

with environment : Type :=
| Environment (locals : list mval) (globals : list (global * mval)).

Definition locals_of (env : environment) : list mval :=
  match env with Environment l _ => l end.

(** グローバル環境: 後から追加したものが先頭で、先頭から検索する。 *)
Definition globals_of (env : environment) : list (global * mval) :=
  match env with Environment _ g => g end.

(** 束縛の入れ子の深さ: スコープにある局所変数の数。翻訳は、これで Python の変数名を決める。 *)
Definition nesting_depth (env : environment) : nat := length (locals_of env).

Definition genv := list (global * mval).

(** 局所変数のない環境 (トップレベルの式を評価するときの環境) *)
Definition init_env (globals : genv) : environment := Environment [] globals.

Fixpoint glookup (G : genv) (g : global) : option mval :=
  match G with
  | [] => None
  | (h, v) :: r => if String.eqb h g then Some v else glookup r g
  end.

Definition lookup_global (env : environment) (g : global) : option mval :=
  glookup (globals_of env) g.

(** 局所環境の先頭に値を 1 つ / 複数 加える。 *)
Definition push (v : mval) (env : environment) : environment :=
  Environment (v :: locals_of env) (globals_of env).

Definition push_all (vs : list mval) (env : environment) : environment :=
  Environment (vs ++ locals_of env) (globals_of env).

(** fix 群の関数を表す値の列。最後の関数が先頭 (= index 1)。 *)
Definition fix_values (env : environment) (defs : list ml_ast) : list mval :=
  rev (map (fun j => VFix env defs j) (seq 0 (length defs))).

(** トップレベルの fix 群を加えたグローバル環境 *)
Definition gfix_globals (env : environment) (gs : list global) (bodies : list ml_ast)
  : genv :=
  combine gs (map (fun j => VGFix env gs bodies j) (seq 0 (length gs))) ++ globals_of env.

(** 最初にマッチする分岐を探す。返り値は (分岐で追加する環境, 本体)。
    最後の引数が先頭 (= index 1) になるので [rev vs]。
    タグが同じで変数の個数が違う分岐は、評価できない (stuck)。 *)
Fixpoint find_branch (g : global) (vs : list mval) (brs : list ml_branch)
  : option (list mval * ml_ast) :=
  match brs with
  | [] => None
  | (ids, p, b) :: rest =>
      match p with
      | Pusual g' =>
          if String.eqb g g'
          then (if Nat.eqb (length ids) (length vs) then Some (rev vs, b) else None)
          else find_branch g vs rest
      | Pwild => Some ([], b)
      end
  end.

(** 式の評価 *)
Inductive evaluate : environment -> ml_ast -> result mval -> Prop :=
| eval_rel env n v :
    0 < n -> nth_error (locals_of env) (pred n) = Some v ->
    evaluate env (MLrel n) (Ok v)
| eval_lam env b :
    evaluate env (MLlam b) (Ok (VClos env b))
| eval_app env f args vf r :
    evaluate env f (Ok vf) -> evaluate_application env vf args r ->
    evaluate env (MLapp f args) r
| eval_app_function_error env f args m :
    evaluate env f (Error m) -> evaluate env (MLapp f args) (Error m)
| eval_let env e1 e2 v r :
    evaluate env e1 (Ok v) -> evaluate (push v env) e2 r ->
    evaluate env (MLletin e1 e2) r
| eval_let_error env e1 e2 m :
    evaluate env e1 (Error m) -> evaluate env (MLletin e1 e2) (Error m)
| eval_glob env g v :
    lookup_global env g = Some v -> evaluate env (MLglob g) (Ok v)
| eval_cons env g args r :
    evaluate_list env args r ->
    evaluate env (MLcons g args) (map_result (VCons g) r)
| eval_case env s brs g vs benv b r :
    evaluate env s (Ok (VCons g vs)) -> find_branch g vs brs = Some (benv, b) ->
    evaluate (push_all benv env) b r -> evaluate env (MLcase s brs) r
| eval_case_error env s brs m :
    evaluate env s (Error m) -> evaluate env (MLcase s brs) (Error m)
| eval_fix env i defs :
    i < length defs -> evaluate env (MLfix i defs) (Ok (VFix env defs i))
| eval_exn env m :
    evaluate env (MLexn m) (Error m)
| eval_dummy env :
    evaluate env MLdummy (Ok VDummy)
| eval_magic env e r :
    evaluate env e r -> evaluate env (MLmagic e) r
| eval_uint env n :
    evaluate env (MLuint n) (Ok (VUint n))

(** 式の列を左から右へ評価する (コンストラクタの引数) *)
with evaluate_list : environment -> list ml_ast -> result (list mval) -> Prop :=
| eval_list_nil env :
    evaluate_list env [] (Ok [])
| eval_list_cons env e es v vs :
    evaluate env e (Ok v) -> evaluate_list env es (Ok vs) ->
    evaluate_list env (e :: es) (Ok (v :: vs))
| eval_list_head_error env e es m :
    evaluate env e (Error m) -> evaluate_list env (e :: es) (Error m)
| eval_list_tail_error env e es v m :
    evaluate env e (Ok v) -> evaluate_list env es (Error m) ->
    evaluate_list env (e :: es) (Error m)

(** 関数値 [vf] に、引数の式を 1 つずつ評価しては適用していく (カリー化された適用) *)
with evaluate_application : environment -> mval -> list ml_ast -> result mval -> Prop :=
| app_nil env vf :
    evaluate_application env vf [] (Ok vf)
| app_cons env vf a rest va vf' r :
    evaluate env a (Ok va) -> apply_closure vf va (Ok vf') ->
    evaluate_application env vf' rest r ->
    evaluate_application env vf (a :: rest) r
| app_argument_error env vf a rest m :
    evaluate env a (Error m) -> evaluate_application env vf (a :: rest) (Error m)
| app_call_error env vf a rest va m :
    evaluate env a (Ok va) -> apply_closure vf va (Error m) ->
    evaluate_application env vf (a :: rest) (Error m)

(** 関数値に、値を 1 つ適用する *)
with apply_closure : mval -> mval -> result mval -> Prop :=
| apply_clos env b v r :
    evaluate (push v env) b r -> apply_closure (VClos env b) v r
| apply_fix env defs i b v r :
    nth_error defs i = Some (MLlam b) ->
    evaluate (push v (push_all (fix_values env defs) env)) b r ->
    apply_closure (VFix env defs i) v r
| apply_gfix env gs bodies j b v r :
    nth_error bodies j = Some b ->
    evaluate (Environment [v] (gfix_globals env gs bodies)) b r ->
    apply_closure (VGFix env gs bodies j) v r.

(** プログラム (宣言列) の実行。結果は、最後のグローバル環境か、例外。 *)
Inductive run : genv -> list ml_decl -> result genv -> Prop :=
| run_nil G :
    run G [] (Ok G)
| run_term G g e v ds r :
    evaluate (Environment [] G) e (Ok v) -> run ((g, v) :: G) ds r ->
    run G (Dterm g e :: ds) r
| run_term_error G g e m ds :
    evaluate (Environment [] G) e (Error m) -> run G (Dterm g e :: ds) (Error m)
| run_fix G gs es bs ds r :
    Forall2 (fun e b => e = MLlam b) es bs ->
    run (gfix_globals (Environment [] G) gs bs) ds r ->
    run G (Dfix gs es :: ds) r.
