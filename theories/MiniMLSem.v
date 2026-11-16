(** MiniML の big-step 意味論 (環境 + クロージャ、正格、左から右)。 *)
From Stdlib Require Import String ZArith List Bool.
From PyCert Require Import Common.
From RocqPython Require Import MiniML.
Import ListNotations.

Inductive mval : Type :=
| VCons (g : global) (vs : list mval)
| VUint (n : Z)
| VDummy
| VClos (env : list mval) (body : mexpr)
| VFix  (env : list mval) (defs : list mexpr) (i : nat).
  (* [VFix env defs i]: fix 群の i 番目の関数。適用時に展開する。 *)

(** グローバル環境。後から追加したものが先頭で、先頭から検索する。 *)
Definition genv := list (global * mval).

Fixpoint glookup (G : genv) (g : global) : option mval :=
  match G with
  | [] => None
  | (h, v) :: r => if String.eqb h g then Some v else glookup r g
  end.

(** fix 群を束縛した環境。最後の def が先頭 (= index 1)。 *)
Definition fix_env (env : list mval) (defs : list mexpr) : list mval :=
  rev (map (fun j => VFix env defs j) (seq 0 (length defs))).

(** 最初にマッチする分岐を探す。返り値は (分岐で追加する環境, 本体)。
    最後の引数が先頭 (= index 1) になるので [rev vs]。 *)
Fixpoint find_branch (g : global) (vs : list mval) (brs : list mbranch)
  : option (list mval * mexpr) :=
  match brs with
  | [] => None
  | MBr p n b :: rest =>
      match p with
      | MPUsual g' =>
          if String.eqb g g' && Nat.eqb n (length vs)
          then Some (rev vs, b) else find_branch g vs rest
      | MPWild => Some ([], b)
      end
  end.

Section Sem.
  Variable G : genv.

  Inductive ev : list mval -> mexpr -> result mval -> Prop :=
  | ev_rel env n v :
      0 < n -> nth_error env (pred n) = Some v ->
      ev env (MRel n) (Ok v)
  | ev_lam env b :
      ev env (MLam b) (Ok (VClos env b))
  | ev_app_ok env f args vf vs r :
      ev env f (Ok vf) -> evl env args (Ok vs) -> ap vf vs r ->
      ev env (MApp f args) r
  | ev_app_ferr env f args m :
      ev env f (Error m) -> ev env (MApp f args) (Error m)
  | ev_app_aerr env f args vf m :
      ev env f (Ok vf) -> evl env args (Error m) ->
      ev env (MApp f args) (Error m)
  | ev_let_ok env e1 e2 v r :
      ev env e1 (Ok v) -> ev (v :: env) e2 r -> ev env (MLet e1 e2) r
  | ev_let_err env e1 e2 m :
      ev env e1 (Error m) -> ev env (MLet e1 e2) (Error m)
  | ev_glob env g v :
      glookup G g = Some v -> ev env (MGlob g) (Ok v)
  | ev_cons env g args r :
      evl env args r -> ev env (MCons g args) (map_result (VCons g) r)
  | ev_case_ok env s brs g vs benv b r :
      ev env s (Ok (VCons g vs)) -> find_branch g vs brs = Some (benv, b) ->
      ev (benv ++ env) b r -> ev env (MCase s brs) r
  | ev_case_err env s brs m :
      ev env s (Error m) -> ev env (MCase s brs) (Error m)
  | ev_fix env i defs :
      ev env (MFix i defs) (Ok (VFix env defs i))
  | ev_exn env m :
      ev env (MExn m) (Error m)
  | ev_dummy env :
      ev env MDummy (Ok VDummy)
  | ev_magic env e r :
      ev env e r -> ev env (MMagic e) r
  | ev_uint env n :
      ev env (MUint n) (Ok (VUint n))

  (** 引数列を左から右へ評価する *)
  with evl : list mval -> list mexpr -> result (list mval) -> Prop :=
  | evl_nil env :
      evl env [] (Ok [])
  | evl_cons_ok env e es v vs :
      ev env e (Ok v) -> evl env es (Ok vs) -> evl env (e :: es) (Ok (v :: vs))
  | evl_cons_err1 env e es m :
      ev env e (Error m) -> evl env (e :: es) (Error m)
  | evl_cons_err2 env e es v m :
      ev env e (Ok v) -> evl env es (Error m) -> evl env (e :: es) (Error m)

  (** 1 引数の適用 *)
  with ap1 : mval -> mval -> result mval -> Prop :=
  | ap1_clos env b v r :
      ev (v :: env) b r -> ap1 (VClos env b) v r
  | ap1_fix env defs i b v r :
      nth_error defs i = Some (MLam b) ->
      ev (v :: fix_env env defs ++ env) b r ->
      ap1 (VFix env defs i) v r

  (** カリー化された逐次適用 *)
  with ap : mval -> list mval -> result mval -> Prop :=
  | ap_nil f :
      ap f [] (Ok f)
  | ap_cons_ok f v vs f' r :
      ap1 f v (Ok f') -> ap f' vs r -> ap f (v :: vs) r
  | ap_cons_err f v vs m :
      ap1 f v (Error m) -> ap f (v :: vs) (Error m).
End Sem.

(** プログラム (宣言列) の実行。トップレベルの [MDFix] の関数は
    [VClos [] b] とし、グローバルは呼び出し時の [G] で解決する。 *)
Inductive run : genv -> mprogram -> result genv -> Prop :=
| run_nil G :
    run G [] (Ok G)
| run_term_ok G g e v ds r :
    ev G [] e (Ok v) -> run ((g, v) :: G) ds r ->
    run G (MDTerm g e :: ds) r
| run_term_err G g e m ds :
    ev G [] e (Error m) -> run G (MDTerm g e :: ds) (Error m)
| run_fix G gs es bs ds r :
    Forall2 (fun e b => e = MLam b) es bs ->
    run (combine gs (map (VClos []) bs) ++ G) ds r ->
    run G (MDFix gs es :: ds) r.
