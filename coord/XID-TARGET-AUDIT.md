# XID-TARGET-AUDIT — StepXiDData 与桥审计（A1116）

日期：2026-11-13。**Status: READ-ONLY AUDIT；不编译。**
对象：`tmp/sheaf/xif/paper/Mzk1XiDTargetActual.lean`（SHA16 待补；**ole=False**；imports `tmp.external.ported.lana_core...`，该端口未绿）。

## 0. 结论先行

1. **`StepXiDData` 可空泛满足**：取 `Ω=Unit`、`logVol` 常数、`qRegion=θRegion`、`qPilotLhs=rhs`、`detComparison=True` 即满足全部字段；因此“faithful data”只是抽象接口，不是 Step (xi-d) 对象的构造；
2. **`target_of_detComparison` 是假的/空桥**：证明完全没使用 `h : D.detComparison`，只调用 `target_of_stepXiD`；`detComparison : Prop` 是任意占位，不含 determinant/scaleElt/leastHull 内容；
3. **containment 方向在 negative-log 坐标下正确**：`logVol=-log μ`、`θRegion⊆qRegion` ⇒ `logVol q≤logVol θ` ⇒ `qPilotLhs≤rhs`；但若改用 Haar/signed `logμ`，正确方向是 `q⊆θ`；两坐标不可混；
4. **无 CIRCULAR 目标假设**：`target_of_stepXiD` 只用 containment/logVol_mono/normalization；不假设目标；但结构空泛、detComparison 空占位；
5. 文件不可编译（lana_core 端口未绿，ole=False）⇒ 只能 PENDING/BLOCKED。

## 1. StepXiDData 字段与可空性

```lean
structure StepXiDData where
  Ω : Type
  logVol : Set Ω → Real
  qRegion θRegion : Set Ω
  qPilotLhs rhs : Real
  containment : θRegion ⊆ qRegion
  logVol_mono : ∀ {S T}, S ⊆ T → logVol T ≤ logVol S
  q_vol : logVol qRegion = qPilotLhs
  θ_vol : logVol θRegion = rhs
  detComparison : Prop
```

**空泛 witness**：
* `Ω := Unit`；`qRegion := Set.univ`；`θRegion := Set.univ`；
* `logVol := fun _ => 0`；`qPilotLhs := 0`；`rhs := 0`；
* `containment` rfl；`logVol_mono` 由常数成立；`q_vol/θ_vol` rfl；`detComparison := True`；
⇒ 全部字段成立，目标 `qPilotLhs≤rhs` 为 `0≤0`。

因此：
* 结构**可平凡居住**；"faithful target data" 不是 faithfulness 证据；
* qRegion/θRegion 没有 actual q-pilot/Θ-hull 类型，`logVol` 没有 measure/负 log 定义，`qPilotLhs/rhs` 没有连到 `S2717`/`S2807`；
* `logVol_mono` 是**假设字段**，不是实际 measure_mono 证明；
* `detComparison : Prop` 是任意 Prop；没有 determinant line、scaleElt、leastHull、thetaComponent 类型。

## 2. 桥定理与循环性

### 2.1 `target_of_stepXiD`

```lean
theorem target_of_stepXiD (D) : D.qPilotLhs ≤ D.rhs := by
  rw [← D.q_vol, ← D.θ_vol]
  exact D.logVol_mono D.containment
```

* 证明只用 `θ⊆q`、`logVol_mono`、两个 normalization；没有假设目标；**不循环**；
* 条件定理本身正确；但它只是“包含 + 单调性”的抽象重编码，不是 Step (xi-d) 的几何构造；
* 由于结构可空泛满足，定理不能证明实际 `qPilotLhs≤rhs`。

### 2.2 `target_of_detComparison` — 空桥

```lean
theorem target_of_detComparison (D) (h : D.detComparison) : D.qPilotLhs ≤ D.rhs :=
  target_of_stepXiD D
```

* `h` **完全未使用**；`detComparison` 是任意 Prop，不能推出 containment；
* 所以这个“determinant-comparison variant”没有 determinant 内容，是**空占位桥**；
* 若把 `detComparison` 设为 `False`，定理无 inhabitant；设为 `True`，则它不提供任何 det 信息；
* 结论：**INVALID/EMPTY as a determinant bridge**；不能作为 Step (xi-d) det 比较的实现。

### 2.3 `target_of_containment`

```lean
theorem target_of_containment (D) (h : D.θRegion ⊆ D.qRegion) : ... :=
  ... D.logVol_mono h
```

与 `D.containment` 重复（结构已有 containment）；用显式 h 可，但只是同一单调性；不增加内容，也无循环。

## 3. containment 方向：θ⊆q vs q⊆θ

### 3.1 negative-log 坐标（本文件声明）

* `logVol = -log μ`；`θRegion⊆qRegion` ⇒ `μθ≤μq` ⇒ `-logμq ≤ -logμθ` ⇒ `logVol q≤logVol θ`；
* `q_vol`: `logVol q=qPilotLhs`；`θ_vol`: `logVol θ=rhs`；⇒ `qPilotLhs≤rhs`；
* 所以 **θ⊆q 在本文件坐标下正确**；
* 这与 A1050 QRegion 的 `logVol=-logμ, θ⊆q` 一致。

### 3.2 Haar/signed 坐标（不可混）

* 若 `logVol=logμ`（StructuralTarget/signed stack），monotonicity 方向反转；正确包含是 `qRegion⊆θRegion`；
* 本文件若被 `StructuralTarget` 或 signed `XiEContainment` 消费，必须换坐标/换包含；
* 文档应写“negative-log: θ⊆q；Haar: q⊆θ”的坐标表，避免把两种方向当同一。

### 3.3 判定

**方向 PASS（在声明的 negative-log 坐标下）**；但跨坐标混用会 INVALID。

## 4. 判定汇总

| 对象 | 判定 | 说明 |
|---|---|---|
| `StepXiDData` | **PARTIAL/EMPTY** | 字段可空泛满足（Unit/常值/q=θ/detComparison=True）；非 faithful 构造 |
| `target_of_stepXiD` | **VALID conditional（PARTIAL）** | 不循环；仅包含+单调性抽象重编码，不是 xi-d 构造 |
| `target_of_detComparison` | **INVALID/EMPTY** | h 未使用；detComparison 任意 Prop；无 det 内容 |
| containment 方向 | **PASS（negative-log）** | θ⊆q 正确；Haar/signed 下应为 q⊆θ；不可混 |
| 循环性 | **无 CIRCULAR** | 未假设目标；但空泛/占位严重 |
| gate | **BLOCKED/PENDING** | lana_core imports 未绿；ole=False |

**总判定：无 CIRCULAR；但 StepXiDData 是空接口，detComparison 桥是空占位；不能当 Step (xi-d) 对象已构造或 det 比较已证。**

## 5. 修正建议

1. 给 `StepXiDData` 绑定 actual 对象：
   * `Ω` 用 `C3LogShellTensorBlockL`/实际 block；`logVol` 用 `-haarLogVolume` 或 `signedLogVolume` 的 actual 定义；
   * `qRegion=actual qPilotHaarRegion`、`θRegion=actualC3LogShellTensorRegionL`；
   * `qPilotLhs/rhs` 连到 `S2717QPilotLogVolume`/`S2717ThetaHullLogVolume`；
   * 加 non-vacuity/strictness：`qRegion≠θRegion` 或 `logVol q<logVol θ`；
2. 把 `detComparison : Prop` 换成真实的 determinant line/单位数据（`S1422.detDataOfHull`、`hchar`、`G`/`scaleElt`），并让 `target_of_detComparison` **真正使用 h** 推出 containment；
3. 若暂不构造，header 应写“abstract interface; actual StepXiDData = GAP”，不要写“faithful target data”；
4. 明确坐标：negative-log θ⊆q；Haar q⊆θ；与 StructuralTarget/XiEContainment 互操作时先做坐标转换；
5. lana_core 端口绿前不编译；gate PENDING/BLOCKED，不写 PROVED。