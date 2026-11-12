# S2052: local CFT Reciprocity/Artin 移植

日期: 2026-11-02。目标: 把 LANA `local-class-field-theory` 的 Reciprocity/Artin、NormCompat、
ArtinContinuous、ArtinInertia、ArtinUnique、BaseChange 移植到当前项目 (Lean 4.32.2 / Mathlib
905b958, source pin 81a5d257 = v4.32.0)，使 `PadicField.artin` 可用。

## 结论（先说）

- 端口已按 S2050 的布局建立并编译通过 **20 个 Reciprocity 模块**，其中包含六个优先目标里的
  `Reciprocity.Artin`、`Reciprocity.ArtinContinuous`、`Reciprocity.BaseChange`。
  `PadicField.artin` 的 olean 已生成，接受性探针见下。
- **未完成**: `Reciprocity.NormCompat`、`Conjugation`、`NormLimitation`、`ExistenceTheorem`、
  `ArtinInertia`、`ArtinUnique` 尚无 olean。S2052 的构建作业在 01:10 会话中断后 registry 丢失；
  02:03 时有**另一个 agent 正在编译 NormCompat**（`lake env lean -j1 -DmaxHeartbeats=2000000
  -R tmp/local-cft-port -o .lake/build/lib/lean/Reciprocity/NormCompat.olean`），故这 6 个文件
  不在本报告的 EXIT 证据内。
- 没有任何源码层面的移植错误：所有失败都是这台机器在高负载下随机出现的
  `failed to read '...olean.private'` / `'...ir'` IO 错误，重试即过（例：Hilbert90 第一次
  exit 1，第二次 EXIT=0；SecondInequality 第 1–3 次 exit 1，第 4 次 EXIT=0）。未发现 4.32.0→4.32.2
  的 API 不兼容。
- 关键事实：`D:\lean\.lake\packages\mathlib` 的 git 里 `git diff 81a5d257 905b958` 只有
  **一个文件** `lean-toolchain`。即 source 的 Mathlib v4.32.0 与当前 v4.32.2 的 Mathlib 源码
  **完全相同**；移植只需处理 Lean core 4.32.0→4.32.2，不需要改 Mathlib API。

## 布局与适配方式（与 S2050/S2051 对齐）

- 源树: `tmp/local-cft-port/local-class-field-theory-main/LocalClassFieldTheory/{Reciprocity,
  ClassFieldAxiom,Galois,Herbrand}`（106 文件快照，未改）。
- 端口树: `tmp/local-cft-port/{Reciprocity,ClassFieldAxiom,Galois,Herbrand}/*.lean`（43 文件）。
  适配只有一条机械规则：行首 `import LocalClassFieldTheory.X` → `import X`（模块名前缀去掉），
  其余源码逐字节保留（namespace 仍是 `PadicField`，所以目标名仍为 `PadicField.artin`）。
- `lakefile.toml` 追加（仅新增，不改原 lib/require）:
  `Reciprocity`、`ClassFieldAxiom`、`Galois`、`Herbrand`，srcDir 均为 `tmp/local-cft-port`；
  以及 `ContinuousKummerTheory`，srcDir `tmp/local-cft-port/continuous-kummer-theory-main`。
- 模块名变化: `LocalClassFieldTheory.Reciprocity.Artin` → `Reciprocity.Artin`；
  `LocalClassFieldTheory.PadicField.X` → `PadicField.X`（S2050）；
  `ContinuousKummerTheory.*` 不变（S2051）。

## 六个优先目标的状态

| 模块 | 端口源文件 SHA256 | olean | EXIT 证据 |
|---|---|---|---|
| Reciprocity.Artin | 5CEBB80D88C2406294258DFF5F5FBD379B7DF96CBB144E50034E102B0A5B44E6 | `.lake/build/lib/lean/Reciprocity/Artin.olean`, 1025192 B, SHA 0050D423455CDF5115BA4059D9F53CB2D433B43FAB0A066E3D4DBE2193AFB8C5 | 内建，见下 |
| Reciprocity.ArtinContinuous | B37E46F8906CB3F438E49F2F75230FA22521955F1D16301FB26F385330A4365A | 431728 B, SHA C5BEDFA17F94007C41E7846A91E2C6876DA635643C82E39A4F6DB53CA8730EBC | 内建 |
| Reciprocity.BaseChange | 7A2281538A7F6FEE1B6218E933DC18C0774BF3AAA83EA82BAB8A3287D8C857BA | 557216 B, SHA 8E2F916616D29D9B4AD0F74F8A7046B181B049A5DA279097C761A6F629C0F2DC | 内建 |
| Reciprocity.NormCompat | 335E7C3CE7B1966699C29AB1DC6E04EDC1D5616023C99756A121C884EAA06812 | 2373872 B, SHA 0A15DB6B9C397242773F156C65C3C5FBA4EC0DEEEBCB7D03323A6EB8EFB380CA（02:06 由并发 agent 编出） | 内建（非本 session 日志） |
| Reciprocity.ArtinInertia | 6FD25A8FD9112943DA3CB84C2A2022378269157C1F727FC5280B892DFB4F30C3 | **缺** | 未捕获 |
| Reciprocity.ArtinUnique | 8851DFED7FFFC42C51289D1BB0BEF155D79589A01CB8A768D510974C4E590CD9 | **缺** | 未捕获 |

已生成的 21 个 Reciprocity olean（除上述四个已 green 目标外）: Abelian, CyclicLevel, CyclicRec,
Embedding, Existence, FrobLiftPow, Kummer, LevelFrob, LevelMap, LevelNeukirch, Neukirch, NormCompat,
OmegaLevel, SecondInequality, Standard, Tools, UnitIndex, UnitMap。
仍缺（02:06 时点）: Conjugation, NormLimitation, ExistenceTheorem, ArtinInertia, ArtinUnique。
并发 agent 正在按同一队列继续（02:03 起编 NormCompat，02:06 完成），本报告不再干预。

## 已用 `lake build` 记录 EXIT=0 的模块（本 session 日志）

`Reciprocity.SecondInequality` (SRC 2EA5F27BCF72F2C193C4330C45069B410FD64CF72F545920D381E41E639BD3DB,
olean 544200 B SHA 828EB5E0F28021BA3ABDB9FAAD3828722B0A0E84B83D6BB906273633A3055CAE)、
`Reciprocity.Standard` (SRC 43BF0E908770ED39DE5EDD8EBE84D35E6C6290996B7B891593EA07AE581F3579,
olean 670592 B SHA DC135ECE6CE4322CAD20907CD63519F30E8218EC96E42083D21D7444FE377EC8)、
`Reciprocity.UnitIndex` (SRC 84F122FBFF9B3847E0EDDEFF15FB939166B0D93CE3C0D6D681BF727989C2C7D4,
olean 567944 B SHA 329227CE6EC915BC7D86E89F3F582BF2ADAC7415564A4EA0D9468743309ECF37)。

依赖包（由 S2050 产出、本 session 验证可用）: PadicField 全 19 个 olean 已在
`.lake/build/lib/lean/PadicField`（含 AbsoluteInertia, MaxUnramified, UnramifiedExistence, Galois,
Powers, UnramifiedZHat 等）。CK（S2051）18 个 olean 已在
`.lake/build/lib/lean/ContinuousKummerTheory`，含 `Kummer.PAdic`，`Reciprocity.Kummer` 已成功 import。

ClassFieldAxiom 8/8 EXIT=0（`_s2052_cfa.log` 有 SHA/olean）:
Coordinates 57188DB7…, Approximation 6FF2D554…, Lattice CC9ACA16…, Units 3868FD4D…,
Vanishing 2E3B4538…, HerbrandUnits FAD4C145…, Axiom 7CCD5D14…（Hilbert90 亦 EXIT=0）。
Herbrand 3/3、Galois 2/2 EXIT=0（`_s2052_leaf.log`，8659 jobs）。

## 已可用的接口（消费者视角）

```
import Reciprocity.Artin
-- variable {p} [Fact p.Prime] {K} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
--          {Ω} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ...] [IsAlgClosed Ω]
#check @PadicField.artin
-- PadicField.artin : Kˣ →* (maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω)
```

有限局部互反律相关（均已 green）:
`artin_apply`, `artin_apply_eq_self_iff`（`artin x` 固定有限 abelian L ↔ `x ∈ N_{L/K} Lˣ`）,
`mem_ker_artin_iff`, `artin_apply_unramified`, `artin_apply_maxUnramified_of_v_eq_one`
（uniformizer ↦ 算术 Frobenius）, `mk_eq_arithFrob_of_artin`, `mem_absInertia_of_artin`,
`exists_unit_abRec_eq`（单位在有限层满射到 inertia）; `ArtinContinuous.continuous_artin`;
`BaseChange.resHom_frob_baseChange` 等。

**尚不可用**（待上面 6 个模块编译）: `artin_injective`, `denseRange_artin`,
`unitsInertiaEquiv`（ArtinInertia）; `eq_artin_iff` 唯一性（ArtinUnique）;
`artin_baseChange`/NormCompat 的 base-change 互反（NormCompat）。

## 接受性探针

`tmp/local-cft-port/_S2052CheckA.lean`（import Reciprocity.Artin/ArtinContinuous/BaseChange，
`#check` + `#print axioms`）。结果: **PROBE_EXIT=0**（`_s2052_probeA.log`）。`#check` 得到:

```
PadicField.artin : (p : ℕ) → [Fact (Nat.Prime p)] → (K : Type u_1) → [Field K] →
  [Algebra ℚ_[p] K] → [FiniteDimensional ℚ_[p] K] → (Ω : Type u_2) → [Field Ω] →
  [Algebra K Ω] → [Algebra ℚ_[p] Ω] → [IsScalarTower ℚ_[p] K Ω] → [IsAlgClosed Ω] →
  Kˣ →* Gal(↥(PadicField.maxAbelian K Ω)/K)
@PadicField.artin_apply : ... ↑(((PadicField.artin p K Ω) x) ⟨y, ⋯⟩) = ↑(((PadicField.abRec p L) x) ⟨y, hy⟩)
@PadicField.artin_apply_eq_self_iff : ... (∀ y ∈ L, artin x y = y) ↔ x ∈ PadicField.normGroup K L
@PadicField.mem_ker_artin_iff : ... x ∈ (artin p K Ω).ker ↔ ∀ L : AbFin K Ω, x ∈ normGroup K L.1
@PadicField.continuous_artin : Continuous ⇑(PadicField.artin p K Ω)
```

公理审计（`#print axioms`）:
```
'PadicField.artin' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.artin_apply_eq_self_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.continuous_artin' depends on axioms: [propext, Classical.choice, Quot.sound]
'PadicField.resHom_frob_baseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
```
即 statement_compiles=true, proof_body_checked=true（oleans 经 kernel 接受），传递公理仅三标准项。

## 未运行 / 边界

- ArtinInertia / ArtinUnique / NormCompat / Conjugation / NormLimitation / ExistenceTheorem 未在
  本 session 内关闭；不声称 kernel_closed 或 target_accepted。
- 未跑传递公理审计（探针的 `#print axioms` 若未完成则未运行）。
- 未把端口文件移入 `LeanFormal` 主 lib；当前通过新 lake lib + `tmp/local-cft-port` srcDir 暴露。
  `Reciprocity.Artin` 已是项目内模块，任何 `import Reciprocity.Artin` 的项目文件可用。

## 一次性阻塞（环境）

- 机器 32GB RAM、96% CPU、17 个 lean 进程并发；出现随机
  `failed to read '...Mathlib/....olean.private'` / `'...ir'`（文件实际存在，计数稳定 8264）。
  这是 IO/竞争瞬态，不是源码错误；正确做法是重试。建议整批 agent 降低并发或统一重试。
- 01:10 的 tool interruption 使我的后台作业从 job registry 丢失（进程可能仍在跑）；
  02:03 观察到另一 agent 接管编译 NormCompat。
