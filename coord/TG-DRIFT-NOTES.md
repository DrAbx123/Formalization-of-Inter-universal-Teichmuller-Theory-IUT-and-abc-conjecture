# TG drift minimal-patch notes (A919, mainline)

Status: planning only — NO forced compile. Both files are lana reference modules
(`TemperedFundamentalGroups/SemistableReduction/*`) ported from FLT271-era Mathlib
(v4.35) to our pin (lean v4.32.2, Mathlib 905b95818e). They are NOT on our own
framework chain; low priority. Local edits already present are marked.

## 1) TemperedFundamentalGroups/SemistableReduction/FormalPatchLevel.lean

Error chain (current, after local duplicate-`Algebra.smul_def` cleanup):
  line 171-174:
  ```
    | tmul s p =>
      simp only [β, betaMod, LinearMap.liftBaseChange_tmul, AlgHom.toLinearMap_apply]
      rw [← mkₐ_comp_lift f J hJ α₀, AlgHom.comp_apply, Algebra.smul_def, map_mul]
      rfl
  ```
  - Error A (already partially fixed): two consecutive `Algebra.smul_def` in rw list
    -> the second cannot match. Fix applied: keep only one. (Backup: `.bak-a894`.)
  - Error B (current): `rfl` fails at 174:6. Goal shape:
    `mk (algebraMap s) * mk (α p) = s • (mkₐ R (JNf f J N)) ((lift f J hJ α₀) p)`
    not definitionally equal under new `Ideal.Quotient.mkₐ` API.

Minimal patch candidates (try in order, 1 file compile each):
  1. replace `rfl` by:
     `rw [Ideal.Quotient.mkₐ_eq_mk, Algebra.smul_def]`  (then `rfl`/`map_mul` if needed)
  2. if lemma name differs in pin: find it via
     `#check @Ideal.Quotient.mkₐ_apply` / `#check @Ideal.Quotient.mkₐ_eq_mk`
     and use `simp only [Ideal.Quotient.mkₐ_eq_mk, Algebra.smul_def, map_mul]`.
  3. if `mkₐ` does not reduce, general fallback:
     `change mk (algebraMap s * α p) = mk (algebraMap s * lift f J hJ α₀ p)`
     then `rfl` (after `map_mul` normalization); requires `trace_state` first.
Diagnosis tip: `set_option pp.all true` + `trace_state` on the `tmul` branch.

## 2) TemperedFundamentalGroups/SemistableReduction/NilpotentFlatness.lean

Local edit present (A894): `set_option maxHeartbeats 4000000` inserted right after
`import Mathlib` (backup `.bak-a894`). This removes the first deterministic timeout but
makes the file very slow (10+ min); do not put it on the critical path.

Error chain after heartbeat fix:
  - line 183:4 `rTensor_exact M ?m hπ` has type `Exact (rTensor M ?m) (rTensor M π)`
    but expected `Exact (rTensor M K.subtype) (rTensor M π)`
    => Mathlib drift: explicit argument of `LinearMap.rTensor_exact` now needed.
    Patch: `exact rTensor_exact M K.subtype hπ` (or `LinearMap.rTensor_exact M K.subtype hπ`),
    confirm arg order via `#check @LinearMap.rTensor_exact`.
  - lines 487-500: `lean.synthInstanceFailed` for
    `SMul (A ⧸ I ^ n) (Q ⊗[A[X]] M)` and `Module (A ⧸ I ^ n) (Q ⊗[A[X]] M)`.
    Root: v4.35 provides quotient-ring action instances that v4.32 lacks. Options:
    (i) add a local instance via restriction of scalars along the canonical ring map used
        in the file (check the `Algebra` instance chain in the file header; likely
        `A[X] ⧸ J -> A ⧸ I^n` or `A ⧸ I^n ->+* A[X]` from a tower) with `Module.compHom`;
    (b) avoid the quotient-ring action in these proofs: replace the `SMul/Module` uses by
        `A[X]`-scalar operations plus explicit `algebraMap` rewrites (`change`/`rw`),
        possibly 5-20 lines per site;
    (c) document-only: leave file red, cite as lana-only reference (current choice).
  - line 196: kernel unknown constant `SemistableReduction.NilpotentFlatness.rTensor_subtype_injective_of_smul_le`
    is a CASCADE (lemma failed to elaborate), not independent; fix earlier errors first.

## Related (not TG): Pi1 Equalizer

`Pi1/Mathlib/RingTheory/Flat/Equalizer.lean` is a vendored backport; its `auxEquivRHS`
`.trans` chain is *type-ill-formed* under new instance transparency (`Algebra R` vs
`Algebra S` on equalizer subtypes). Needs instance transport (`letI`/`AlgEquiv.cast`/
`eqToHom`), >30 min. Deferred by A906/A919; file restored to `.bak-a807`.

## Decision

Both TG files stay red in our build; their only consumer is the lana reference chain.
If later needed: apply patch candidates above one at a time with single-file compile,
keep `.bak-*` backups, and do NOT add them to any watchdog plan.

## A931/A944 结论（2026-11-12，shehdd；限时到点）

**总判定：FormalPatchLevel GREEN；NilpotentFlatness RED；C0 的 lana `Gap.lean`/`LocalConstruct` 编译仍被 TG 阻塞。** 不再继续投入。

### 1) `TG/SemistableReduction/FormalPatchLevel.lean` — GREEN

* 单文件 `lake env lean -D maxHeartbeats=4000000 -D synthInstance.maxHeartbeats=400000 -o ...`：**EXIT=0，olean=True**。
* 成功补丁（`tmul` 分支，行 173-176）：
  ```lean
  rw [← mkₐ_comp_lift f J hJ α₀, AlgHom.comp_apply]
  rw [← Ideal.Quotient.mk_eq_mk]
  rw [Submodule.Quotient.mk_smul]
  congr 1
  ```
  关键：`Ideal.Quotient.mk_eq_mk` 把 `Ideal.Quotient.mk` 降为 `Submodule.Quotient.mk`，
  之后 `Submodule.Quotient.mk_smul` 可用；`congr 1` 关掉剩余 `α p = lift p`（`rfl` 不可见）。
* 备份：`FormalPatchLevel.lean.bak-a931`（修改前）。

### 2) `TG/SemistableReduction/NilpotentFlatness.lean` — RED（已恢复 `.bak-a931`）

当前首错（单文件，heartbeat override 后）：

```
line 183:4: Type mismatch
  rTensor_exact M ?m.514 hπ
has type Exact (rTensor M ?m.502) (rTensor M π)
but expected Exact (rTensor M K.subtype) (rTensor M π)
line 489: synthInstanceFailed: SMul (A ⧸ I ^ n) (Q ⊗[A[X]] M)
```

已试方案（全部失败，首错不变或更早）：
* `set_option maxHeartbeats 4000000`（消除 152 whnf 超时，但文件仍 red）；
* `rTensor_exact M (LinearMap.exact_subtype_ker_map π) hπ`；
* 显式命名参数 `(R := S) (Q := M) (f := K.subtype) (g := π)` / `(ker π).subtype`；
* `have hfg : Function.Exact (LinearMap.ker π).subtype π := ...` + `rTensor_exact M hfg hπ`；
* `@rTensor_exact ...` 显式全参数（参数序不匹配，报 expected `Module S M`）；
* `convert`（本文件未导入 `convert` tactic，unknown identifier）；
* 尚未处理的独立第二错：`SMul (A ⧸ I ^ n) (Q ⊗[A[X]] M)`（notes 建议 `Module.compHom`/改写 scalar 操作）。

### 3) TG 闭包的其他 RED（A931 任务外但阻塞 C0）

`NodeEtaleGlueReduced` 依赖闭包 87 文件，缺 43；首轮只编成 4 个（FormalPatch* 系列）。
下一层首错：
* `KummerNodePunctured.lean:131`（`tmul`）：tensor smul 重写失败，
  目标 `x ⊗ₜ (μ y) = ((algebraMap f)*x) ⊗ₜ y`；`TensorProduct.tmul_smul/smul_tmul` 组合未闭合；
* `FormalPatchProd.lean:135`：`IsScalarTower (Hat f) ((j:ι)→N j) ((j:ι)→Localization.Away ...)` synth failed；
* 其余为级联缺 olean。

### 4) 决策记录

* 停止 TG drift 投入（超过 1.5h 限时）；保留 `.bak-a931` 干净状态；
* **C0 的 Lean 化（lana `Gap.lean`/`LocalConstruct/*` olean）判定：BLOCKED-BY-TG**；
  C0 计算器若继续，只能用 Lean 外部模型/对 lana 源文件做非编译引用，不得声称 Lean green。

## A960（45 分钟限时）NilpotentFlatness 精确卡点（2026-11-12 20:xx）

`tmp/nilpotent_checks.log` 已保存 v4.32 `#check` 输出（`@rTensor_exact` 签名：
`Q` 显式在 `f/g` 之后、instances 7+2；不是 `LinearMap.rTensor_exact`）。

* 显式 `@rTensor_exact S (↥ker π) (B→₀S) B ... (ker π).subtype π M ...` 已让原 183 行
  类型错前进到下一阶段；随后文件在 `flat_of_isNilpotent` 的 `whnf` 超时（4M/20M heartbeat）；
* `SMul (A⧸I^n) (Q⊗[A[X]]M)` 用 `Module.compHom` + `IsScalarTower.of_compHom` 尝试，
  `IsScalarTower` 仍 synth/smul assoc 未闭合；
* 20M heartbeat 编译超过 16 分钟未结束，按限时停止；文件恢复 `.bak-a931`。
* 未产出新 olean；未继续 SemistableReduction 其余文件（前置仍 red）。

**判定：NilpotentFlatness 仍 RED；GLM（Gap/LocalConstruct）继续 BLOCKED-BY-TG。**
