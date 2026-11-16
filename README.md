# rocq-python-plugin

Rocq から Python への Extraction をできるようにする。

## How to use

### インストール

```console
opam pin add rocq-pycert git+https://github.com/proof-ninja/PyCert.git
opam pin add rocq-python-plugin git+https://github.com/proof-ninja/rocq-python-plugin.git
```

(rocq-core.9.4以上が必要です)

### Rocq から Python を生成する

```rocq
From PythonPlugin Require Import Python.
From Stdlib Require Import List.
Extraction Language Python.

Extraction "sample.py" List.map.
```

`rocq c Sample.v` で `sample.py` ができる。


### 生成した Python を使う

```python
import sample

zero = ("O",)
succ = lambda n: ("S", n)
xs = ("Cons", zero, ("Cons", succ(zero), ("Nil",)))   # [0; 1]

print(sample.g_map(succ)(xs))   # [1; 2] = ("Cons", ("S", ("O",)), ("Cons", ("S", ("S", ("O",))), ("Nil",)))
```

### TODO

- [ ] float、primitive string、primitive array
- [ ] `Extract Constant` / `Extract Inductive` による名前の置き換え
- [ ] `Extraction Library` (複数ファイルへの抽出)

## 証明事項

Rocq のプログラム (Extraction が出す MiniML) を Python に変換しても、意味が変わらない。

```rocq
Theorem tr_correct :
  forall G env e r,
    ev G env e r ->
    forall d ctx k k' ss penv,
      tr d ctx k e = (k', ss) ->
      env_rel ctx env penv ->
      genv_rel G penv ->
      fresh_from k penv ->
      exists o, pexec_block penv ss o /\ out_rel d r o.
```

### TODO

- [ ] `tr_correct` の証明
- [ ] `tr_prog_correct_ok` / `_err` の証明と、前提 `wf_prog` の定義 (現在は `Parameter`)
- [ ] 発散と Python の再帰上限の扱い (今は評価が成功する場合のみ)
