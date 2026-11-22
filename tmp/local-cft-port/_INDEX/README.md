# tmp/local-cft-port 索引（donor port）

这是 local class field theory / PadicField 的 port，部分模块可直接 import，不要重证。

## 关键 donor
- `PadicField/FieldNorm.lean`：
  - `PadicField.v_norm : v p (Algebra.norm K x) = f p K L * v p x`
  - `PadicField.nrm_norm`
  - 已用 `import PadicField.FieldNorm` 验证可加载。
- `PadicField/Ramification.lean`、`Tower.lean` 等：v/e/f/uniformizer donor。

## 注意
- 这些模块有自己的 `v`/`nrm` 定义，接本项目的 `Valued.v` 需要桥接；
- 不要重新从零证 norm-valuation 公式。

总索引：`../../coord/LEAN-INDEX.md`。编译只走 watchdog。
