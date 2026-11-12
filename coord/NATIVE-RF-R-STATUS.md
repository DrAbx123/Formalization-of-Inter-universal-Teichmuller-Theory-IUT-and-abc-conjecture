# NATIVE-RF-R-STATUS — R 字段（posRealAction/degree_of_q）可构造性判定

日期：2026-11-12；qpilot（A956/A958）。**只读 + 判定；未写 Lean 草稿（无 `_NATIVE-RF-R-DRAFT.lean`）。**

## 1. `ValueMonoidAt` 定义（精确）

- `I.ValueMonoidAt n m v`（`SourceImageHull.lean:82`）= `(I.primeStripAt n m).Mon v`；`SourceOriginalInput.lean:801` 同义 `I.valueMonoidAt`。
- `FPrimeStrip`（`PrimeStripCore.lean:117–121`）只含：
  - `Mon : V → Type v`，`[commMonoidMon : ∀ v, CommMonoid (Mon v)]`；
  - `action : ∀ v, Pi v →* MulAut (Mon v)`；
  - `degree : ∀ v, Mon v →* Multiplicative ℝ`。
- 因此 `ValueMonoidAt` 只是**任意交换幺半群** + 一个度数同态；**没有**：ℝ-模结构、可除性、`Mon v ≃ Multiplicative ℝ`、`degree` 的满射性/截面、实幂结构。
- `I.logDegreeAt n m v x := Multiplicative.toAdd ((I.primeStripAt n m).degree v x)`（`SourceImageHull.lean:100`）；`logDegreeAt_one = 0`、`logDegreeAt_mul` 可加。

## 2. 已找到的构造器/已有工作

| 对象 | 文件/行 | 内容 | 状态 |
|---|---|---|---|
| `NativeBindingRFActual.NativeImageRealizationSourceFields` | `tmp/sheaf/n8/closure/NativeBindingRFActual.lean:50` | 精确两个字段：`posRealAction : Multiplicative ℝ →* I.ValueMonoidAt 0 0 (nativeSelectedPlace X)`；`degree_of_q : logDegreeAt (posRealAction (ofAdd (log q))) = log q` | 定义/条件构造；无 inhabitant |
| `nativeImageRealizationOfFields` | 同上 :59 | 从两个字段构造 `I.SourceImageRealization` | 条件构造，green（依赖字段） |
| `trivialPositiveRealAction` | `NativeRFDeep2.lean:78` / `NativeRFProof.lean:96` | 常值 1 的 monoid hom：`Multiplicative ℝ →* ValueMonoidAt` | 已构造 |
| `logDegreeAt_trivialPositiveRealAction` | `NativeRFDeep2.lean:82` | 常值 action 的 degree 恒为 0 | 已证 |
| `realizationOfQOne` / `realizationOfImageFieldsAtQOne` | `NativeRFDeep2:89` / `NativeRFProof:110` | **q = 1** 时用常值 action 构造 `SourceImageRealization` | 已构造（q=1 trivial） |
| `q_eq_one_of_logDegree_zero` | `NativeRFDeep2:129` | 若该位 `logDegreeAt` 恒 0，则任何 realization 迫使 q=1 | 已证（精确障碍） |
| `no_realization_of_q_ne_one_and_logDegree_zero` | `NativeRFDeep2:146` | q≠1 且 degree 恒 0 ⇒ 无 realization | 已证 |
| `NativeNontrivialPosRealActionPrimitive` | `NativeRFDeep2:160` | 精确“非平凡 primitive”：`posRealAction` + `degree_of_q` + `q≠1` | **定义；无构造** |
| `sourceHaarActualImageRealization`（V=Unit, q=1） | `SourceUnitRegionHaarDataActual.lean`（文件 red） | 合成 V=Unit 的 realization | **不可用**（文件 red） |
| `NativeC1.NativeStripFiberComparison` | `NativeC1.lean:186` | fiber monoid equivalence 的命名义务 | **无 inhabitant** |

## 3. 已试构造（通用 ValueMonoid 路线）

**目标**：从 `degree : Mon v →* Multiplicative ℝ` 通用构造 `posRealAction : Multiplicative ℝ →* Mon v`，满足 `degree (posRealAction (ofAdd (log q))) = log q`。

### 3.1 等价条件
这样的 `posRealAction` 存在 ⇒ 它是 `degree` 的一个**幺半群截面**（在正实数子群上）：`degree ∘ posRealAction = id`（至少在实际用到的 `ofAdd b` 上）。反过来，`degree` 有截面且截面值域在正的“实幂”子幺半群内，就可构造。

### 3.2 q=1
常值 `1` 是 monoid hom，`degree 1=0`，故 `log q=0` 自动满足；`NativeRFDeep2`/`NativeRFProof` 已构造。

### 3.3 q≠1（精确数学障碍）
要 `degree (x) = log q ≠ 0`，首先需要 **`logDegreeAt` 在此处能取非零值**；一般 `Mon v` 的 `degree` 可能是零映射/非满射（例如 `Mon` 为挠群、单位群、或平凡 monoid），此时无解——`NativeRFDeep2` 的 `q_eq_one_of_logDegree_zero` 已把这一点证明为精确障碍。
即使 `degree` 在 `log q` 处有原像，仍需要把 `Multiplicative ℝ` 的**整个正实数乘法群**同态映入 `Mon v`：这要求 `Mon v` 带有相应的**实幂/可除幺半群结构**（至少 `ℚ`-向量空间型正锥）；`FPrimeStrip.Mon` 只声明 `CommMonoid`，没有该结构，也没有 `degree` 的截面。
因此“从通用 `ValueMonoidAt` 构造 `posRealAction`”**不成立**：所需的 `posRealAction` 不是由 `PrimeStripCore` 的字段推出的，而是额外源数据（`NativeNontrivialPosRealActionPrimitive` 型的 primitive）；`degree_of_q` 对 q=1 是 trivial，对 q≠1 等价于“存在 degree=log q 的实幂截面”，不能由现有字段证明。

### 3.4 已试构造结果
- q=1：成功（常值 action；green，`NativeRFDeep2`/`NativeRFProof`）。
- q≠1：**失败**（无通用构造；`NativeNontrivialPosRealActionPrimitive` 只是把缺失对象定义为结构，无 inhabitant；**这不是 Lean 缺失，而是数学上需要额外源结构**）。
- fiber F 字段：同样无 production inhabitant（`NativeC1.NativeStripFiberComparison` 空；`C1FiberMonTargetNoGo` 指出 raw unit monoid 与 value group 不等价）。

## 4. 结论

**R 部分（`posRealAction` + `degree_of_q`）不能从通用 `ValueMonoidAt`/`FPrimeStrip.Mon` 构造。**

1. `ValueMonoidAt = (I.primeStripAt n m).Mon v` 只是任意 `CommMonoid` + 度数同态；无实幂、可除性、满射性或截面。
2. **q=1**：已有 green 构造（常值 action；`NativeRFDeep2.realizationOfQOne` / `NativeRFProof.realizationOfImageFieldsAtQOne`）。
3. **q≠1**：需要 `logDegreeAt` 在 `log q` 处有原像且该元素带实幂结构；这等价于一个额外源 primitive（`NativeNontrivialPosRealActionPrimitive`），现有 source 字段不提供。`q_eq_one_of_logDegree_zero` 证明：在 degree 恒 0 的 fiber 上 q≠1 根本无 realization。
4. **这不是 Lean API 缺失**，是数学障碍：要么补“带 ℝ-幂/可除正锥的 `Mon v` + degree 截面”的源构造（新数学），要么把 `posRealAction`/`degree_of_q` 作为显式外部输入（class-B）登记；不能从抽象 prime-strip 数据自动得到。

**未写 Lean 草稿**（本任务只读+判定），故无 `_NATIVE-RF-R-DRAFT.lean`；若后续尝试，应把文件命名为 `tmp/sheaf/n8/closure/_NATIVE-RF-R-DRAFT.lean` 且不注册。