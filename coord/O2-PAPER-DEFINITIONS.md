# O2 论文定义审计：Θ^q / Θ^anab comparison、volume index、sign 与 normalization

日期：2026-10-24。范围：只审计 IUT III Theorem 3.11 / Remark 3.9.5 / Theorem B (Corollary 3.12) 中 O2 所需的论文定义与归一化，以及它们与当前 actual Lean 对象的对应。**不新增 Lean 目标、不新增 arbitrary comparison、不把审计结论写成定理。** 本文是 paper-definition audit，不是完成声明。


## 0. Paper input candidate 与 source discipline（2026-10-24 更新）

O2 audit 的 paper input 候选固定为 **`SourceInitialThetaData`**，而不是某个单独选出的 completion/shell 对象。

- 定义位置：`LeanFormal/IUT/IUTI/InitialTheta/SourceInitialThetaData.lean`，`structure SourceInitialThetaData (l : PrimeGeFive)`。
- 它对应 IUT I Definition 3.1 的完整六元组：`candidate`（F/Fbar、X_F、l、C_K、V、V_bad_mod、ε）连同 clauses (A)–(F)，并额外记录 arithmetic/order coherence；每一个 clause 的局部 exact sequence、place section、q-parameter、torsion representation、cusp normalization 都是显式字段，不是自由 `Prop`。
- 对每个 bad place `p`（`comap p ∈ VbadMod`），source 的 Tate q-parameter 是
  ```
  S.clauseB.qParameter p hp : NumberFieldFinitePlace.FinitePlaceQCandidate p.
  ```
  因此 O2 的 q-side 输入应在**这个 source q 参数**上定义，而不是另取一个 completion 元素。

N8 actual chain 使用 native presentation：`N8NativeInput.S : SourceNativeInitialThetaData l`，其 q 由 `NativeC3.nativeQActual` 给出；`SourceCompletion.toSourceNativeInitialThetaData` 与 `ofSourceNative` 提供 source completion/native presentation 的桥，但 paper `SourceInitialThetaData` 与 N8 `SourceNativeInitialThetaData` **不是同一个字段结构**。因此有：

- **G0 source-binding gap**：把 paper `SourceInitialThetaData` 的 selected bad place、q-parameter、V/V_bad_mod、F/Fmod 与 N8 `SourceNativeInitialThetaData`（进而 `nativeFPlaceOverBad`、`nativeQActual`）逐项绑定。没有这个绑定，不能把 `nativeQActual` 直接称为 paper source 的 q。
- actual log-shell 对象（`fPlaceShell`、`fPlaceVolumeConsumer`、`fPlaceVolumeIndex`）只是 source q 在**选定完成域**上的 readout 载体；它们本身不是 q-pilot，也不是 Θ-pilot。O2 audit 以 source `SourceInitialThetaData` 为输入，以 actual log-shell 作 readout，不能反过来把 log-shell index 当作 source q。

本文以下所有 formula 都应理解为：**给定同一 `SourceInitialThetaData`（或已登记 bridge 的 N8 native presentation）后**的 normalization；在 G0 关闭前，actual volume index 与 source q 的对应仍是条件/审计对象。

## 1. 审计结论（先写结论）

1. 论文的 q-pilot log-volume 是**有符号负量** `-|log(q)|`，且 `|log(q)|>0`；Θ-pilot/hull log-volume 是 `-|log(Θ)| ∈ R ∪ {+∞}`，并与 q-pilot 使用**同一 procession normalization**。两者相较的论文结论是

   `-|log(Θ)| ≥ -|log(q)|`

   （Theorem B / Corollary 3.12；等价地正幅度 `|log(Θ)| ≤ |log(q)|`）。
2. 当前 Lean 的 `fPlaceLogVolume = Real.log(fPlaceVolumeIndex)` 是非负的**正幅度** readout，不是论文的 signed log-volume；`etaPilot` 的 additive log 是负的 `qPilotSignedLog<0`。因此 naive identification `etaPilot = ofAdd(fPlaceLogVolume)` 方向/符号都错，已由 actual no-go 反驳。
3. 正确的 O2 比较不能是“把两个不同载体的实数直接设为相等”。在 log-volume shadow 上，正确的 q-pilot inverse 形式是

   `ofAdd(fPlaceLogVolume) = (etaPilot)⁻¹`，等价于 `fPlaceLogVolume = -qPilotSignedLog = |log(q)|`，

   也就是 volume index 条件

   `fPlaceVolumeIndex = exp(qPilotLogMagnitude)`（作为实数等式）。
4. 当前 `index = 1` 的 normalization 是**平凡线丛 / unit-ball normalization**，给出 `fPlaceLogVolume=0`。它既不是论文 q-pilot 的 `-|log(q)|`，也没有经过 Remark 3.9.5(vii) 的 `det^{⊗M}` 与 structure-sheaf `O(-)` inverse adjustment。因此 index 1 下 corrected identification 必然假：右边 `exp(qPilotLogMagnitude)>1`，左边 1；且左边 log-volume 0 与负的 q-pilot log-volume 不同。
5. 当前 actual Lean 的 `fPlaceVolumeIndex` 来自 production log-shell consumer 的整数 index；生产树没有证明它等于 `exp(-qPilotSignedLog)`，只有 F-place q/e/f 条件公式和 signed-criterion 的精确算术缺口。故 O2 当前 normalization **不成立**，不是差一个“小的 normalization 选择”。

## 2. 论文对象与原文引用

### 2.1 q-pilot

IUT III 的 q-pilot object 由 arithmetic divisor 的 zero locus `{q_v}_{v∈V_bad}` 给出（codomain of `Θ^{×μ}`-link 一侧）。其 log-volume 记为

```
-|log(q)| ∈ R,     |log(q)| > 0.
```

在 Corollary 3.12 / Theorem B 的约定中 `-|log(q)|` 已是**负实数**；它是 q-pilot 在 multiradial representation 中的 procession-normalized mono-analytic log-volume，且 q-pilot 一侧**不**施加 (Ind1),(Ind2),(Ind3)。

### 2.2 Θ-pilot 与 holomorphic hull

Θ-pilot object 由 theta values `{q_v^{j^2}}_{j=1,…,l^⋇}` 的 zero locus 给出（domain of `Θ^{×μ}`-link 一侧）。其 log-volume 定义为

```
-|log(Θ)| ∈ R ∪ {+∞}
```

它是以下对象的 procession-normalized mono-analytic log-volume：

1. Θ-pilot 的所有 possible images 的 union；
2. 该 union 的 holomorphic hull（Remark 3.9.5(i)）；
3. 对 `j ∈ F_l^⋇` 取 procession average；
4. 相对于 multiradial representation 的 Kummer isomorphisms；
5. 考虑 (Ind1),(Ind2),(Ind3)。

Remark 3.9.5(i) 的 hull：若区域相对紧，则取包含它的最小 `λ·O`，其中 `λ` 的每个分量非零；若区域不相对紧，则 hull 取整个 `I_Q`。Remark 3.9.5(ii)(iii) 还给出 hull-approximant 集合 `Φ(P), Ξ(P)`，其 log-volume 可能严格大于原区域；这解释了为什么 Θ-pilot 的 log-volume 不能简单取某个 arbitrary region 的值。

### 2.3 Theorem 3.11 的 multiradial/LGP 内容

Theorem 3.11 给出 data (a)(b)(c) 的 multiradial representation `n,o R_LGP`：

- (a) 局部 tensor packets/log-shells `I(S^±_{j+1}; ...)`，带 Proposition 3.9(ii) 的 **procession-normalized mono-analytic log-volumes**；
- (b) `V_bad` 的 splitting monoids `Ψ^⊥_LGP`；
- (c) `F_mod` 的 labeled copies 与 global Frobenioid isomorphisms；
- (Ind1): procession automorphisms；
- (Ind2): 每个 direct summand 上 independent copies of `Ism`（非阿）或 order-2 automorphisms（阿）；
- (Ind3): 沿 n-th column log-links 的 **upper semi-compatibility**（非阿为 `⊆`，阿为 `↠`）。

Theorem 3.11(ii) 的 log-Kummer correspondence 把这些 vertically coric data 与每个 `n,m` Hodge theater 的 local tensor packets 比较；Theorem 3.11(iii) 要求这些 Kummer isomorphisms 与 horizontal `Θ^{×μ}_LGP`-links 相容。O2 的 Θ^q/Θ^anab comparison 只能在**这套 multiradial/LGP 结构**中解释，不能退化为两个实数函数的等式。

### 2.4 Remark 3.9.5(vii) 的 weighted normalization

Remark 3.9.5(vii) 明确说明：为了把 multiradial output 与 q-pilot 所在的 arithmetic line bundle 比较，需要

1. 对 tensor packet 的各个 direct summand 的 determinant line bundles 取 **suitable positive tensor powers**（权重为 Remark 3.1.1(iv) 的 `N_v` 乘积）；
2. 再 tensor 上 **structure sheaf `O(-)` 的 determinant 的 inverse**，即 (Ob3-1-2) 的 adjustment，以计入 ramification；
3. 记该操作为 `det^{⊗M}(-)`，其中 `M` 是某个正整数的 tensor power；
4. (Ob3-3)：在 suitable normalization factors 下，arithmetic line bundle 的 arithmetic degree 可解释为原 arithmetic vector bundle 的 log-volume；因此只关心 log-volume 时中间 `det^{⊗M}` 步骤可省略，但**normalization 不可省略**。

这给出 O2 的关键约束：q-pilot 的 log-volume 不是任意 log-shell index 的 `Real.log`；它必须与 `det^{⊗M}`、`O(-)` inverse、procession normalization 一致。

## 3. 论文符号与 Lean actual readout 的字典

| 论文对象 | 论文 normalization/sign | 当前 Lean actual | 状态 |
|---|---|---|---|
| q-pilot log-volume | `-|log(q)| < 0` | `qPilotSignedLog X = Real.log ‖q‖ < 0`; `qPilotLogMagnitude = -qPilotSignedLog > 0` | actual/no-go 有 `qPilotSignedLog_neg` |
| q-pilot value group element | `etaPilot` (multiplicative) | `etaPilot = Multiplicative.ofAdd qPilotSignedLog` | actual (O2ConstructedIdentification) |
| q-pilot inverse | `etaPilot^{-1} = ofAdd(+|log q|)` | `(etaPilot)⁻¹ = ofAdd(qPilotLogMagnitude)` | formal inverse actual |
| Θ/hull log-volume | `-|log(Θ)| ∈ R∪{+∞}`，procession averaged over `j∈F_l^⋆` | `etaRssAtFPlace.logVolume = fPlaceLogVolume = Real.log(fPlaceVolumeIndex)`，非负 | actual carrier，但**正幅度而非 signed volume** |
| volume index | q-pilot 的 arithmetic normalization 的 index | `fPlaceVolumeIndex : Nat`，来自 `LogShellVolumeConsumer.index` | actual integer，但无 q-pilot equality |
| corrected index | `exp(|log q|)`（在 q-pilot normalization 下） | `O2CorrectedVolumeIndex = Real.exp(qPilotLogMagnitude)` | actual definition; `one_lt_O2CorrectedVolumeIndex` actual |

注意 sign 的两层：

- 论文的 `-|log(q)|` 与 `-|log(Θ)|` 都是**负的** signed volumes；
- Lean 的 `fPlaceLogVolume` 是 `Real.log N ≥0`，对应正幅度 `|log(Θ)|` 或 `|log N|`，不是 signed volume。

所以若把 `fPlaceLogVolume` 直接代入 paper 的 `-|log(Θ)|`，必须再加负号；若把它代入 q-pilot 的 inverse，则它对应 `+log(q^{-1})` 的正幅度。

## 4. 正确的 O2 formulas

设

```
L_q := |log(q)| = qPilotLogMagnitude > 0,
s_q := -L_q = qPilotSignedLog < 0,
A := fPlaceLogVolume = Real.log(fPlaceVolumeIndex) ≥ 0,
N := fPlaceVolumeIndex : Nat.
```

则论文 q-pilot 的 additive log-volume 是 `s_q`；其 multiplicative value-group element 是 `etaPilot = ofAdd(s_q)`。若把 F-place anab readout 解释为**正幅度** `A`，则对应的 signed hull log-volume 是 `s_Θ = -A`。论文的 log-volume compatibility（Theorem B）是

```
s_Θ ≥ s_q    (即 -A ≥ -L_q，等价 A ≤ L_q).
```

而 O2 的 Θ^q/Θ^anab **identification**（比单纯不等式更强）要求同一个 procession normalization 下两边 log-volume 相等：

```
A = L_q,     即    s_Θ = s_q.
```

写成 multiplicative value-group 形式：

```
ofAdd(A) = etaPilot⁻¹,   因为 etaPilot⁻¹ = ofAdd(-s_q) = ofAdd(L_q).
```

写成 volume index：

```
N = exp(A) = exp(L_q) = exp(qPilotLogMagnitude).
```

这是当前 Lean 中 `O2CorrectedVolumeIdentification` / `o2Corrected_iff_index` 的精确内容（文件 `tmp/sheaf/n8/closure/O2CorrectedVolumeIndex.lean`）：corrected identification iff `(fPlaceVolumeIndex : ℝ) = exp(qPilotLogMagnitude)`。注意这里没有 arbitrary real；`exp(qPilotLogMagnitude)` 由 actual q 的 norm 决定。

## 5. 为什么当前 index 1 是假的

### 5.1 代数理由

若 `N = 1`，则 `A = log 1 = 0`。而 actual `qPilotSignedLog<0`，所以

```
etaPilot 的 additive log = qPilotSignedLog < 0 = A;
```

naive `etaPilot = ofAdd(A)` 假；corrected inverse `ofAdd(A)=etaPilot⁻¹` 需要 `A=-qPilotSignedLog>0`，而 `A=0`，也假。等价地 corrected index 条件要求 `N=exp(qPilotLogMagnitude)>1`，不可能等于 1。`one_lt_O2CorrectedVolumeIndex` 已 actual 证明 `exp(qPilotLogMagnitude)>1`，故 `o2Corrected_false_of_index_one` 是 actual no-go。

### 5.2 normalization 理由（Remark 3.9.5(vii)）

index 1 对应 `O`（structure sheaf / unit ball）的 normalization：

```
μ(O) = 1,     log μ(O) = 0.
```

但论文的 q-pilot 是 arithmetic divisor 的 zero locus `{q_v}` 所确定的 arithmetic line bundle，不是 structure sheaf；其 normalized degree 是 `-|log(q)|`。Remark 3.9.5(vii) 的 (Ob3-1-2) 要求把 determinant 与 structure sheaf `O(-)` 的 determinant inverse 作 tensor adjustment；index 1 正是“没有做这个 adjustment / 取了 O 本身”的结果。省略它就把 q-pilot 的 nontrivial degree 抹成 0。

### 5.3 不能用 inequality 替代 identification

Theorem B 的 `s_Θ ≥ s_q` 在 `A=0` 时自动成立（因为 `s_q<0`），所以 index 1 的 readout 并不与 Theorem B 的**不等式**矛盾；但它与 q-pilot/Θ-pilot 的 **identification** 矛盾。O2 需要的是 identification/comparison，不是只验证一个容易满足的不等式。若只保留不等式，就会得到 vacuous/过弱目标，不能作为 O2。

### 5.4 不是“选择另一个 arbitrary index”

corrected index 不是 arbitrary：它是 `exp(-qPilotSignedLog)`，由 actual q 的 norm 唯一决定。当前 Lean 只证明：若 corrected identification 成立，则 index 必须等于该 exp；没有任意指定。实际 `fPlaceVolumeIndex` 由 production log-shell consumer 给出，可能是任意正整数，当前生产树没有证明 q-pilot 的 `det^{⊗M}`/`O(-)` normalization 使二者相等。

## 6. 当前 Lean 证据地图（只读审计）

| 文件 | 内容 | 与 O2 的关系 |
|---|---|---|
| `tmp/sheaf/n8/closure/O2ConstructedIdentification.lean` | `etaRssAtFPlace.logVolume = fPlaceLogVolume ≥0`；`etaPilot` additive log `<0`；`no_naive_identification` actual | 证明 naive equality 假；corrected inverse conditional on signed comparison |
| `tmp/sheaf/n8/closure/O2EtaIndependent.lean` | actual `etaQMap`/`etaAnabMap` independent；comparison at pilot iff missing source identification | 证明 O2 比较不能由两个 arbitrary 实数函数直接给出 |
| `tmp/sheaf/n8/closure/O2CorrectedVolumeIndex.lean` | corrected index `exp(qPilotLogMagnitude)`；`o2Corrected_iff_index`；`one_lt_...`；`o2Corrected_false_of_index_one` | 给出本文的核心公式与 index1 no-go |
| `tmp/sheaf/n8/closure/EtaQVolumeIndexComparison.lean` | raw `etaSelectedLogVolume = etaPilotQ` 假；若成立则 index=1 且 etaPilotQ>0 矛盾 | 另一个 decisive no-go，说明 raw index1 equality 不可能 |
| `tmp/sheaf/n8/closure/EtaVolumeIndexFormulaAttempt.lean` | F-place q/e/f 条件公式与精确算术缺口 | 说明当前 actual index 只有条件公式，不能直接等于 exp |
| `tmp/sheaf/n8/closure/PaperNormalizedVolume.lean` | group6 的 `Vμ(S)=(Lμ(S)-Lμ(O))/D` 等 | 提醒 O2 的 `O(-)` normalization 与 group6 的 volume normalization 必须一致 |

这些文件中没有 production 的 q-pilot/Θ-pilot arithmetic-line-bundle normalization 构造；O2 的 source comparison 仍是 gap，而不是已证定理。并且现有 N8 actual 链的 source 是 `SourceNativeInitialThetaData`；在 G0 bridge 关闭前，不能把 paper `SourceInitialThetaData` 的 q 与 `nativeQActual` 等同。

## 7. O2 正确的 target 形式（qualified-input 版）

若按论文合格输入处理，O2 的 target 应写成以下**比较数据**，而不是 arbitrary map：

1. **同一套 initial Θ-data** 和同一 `n`-procession；
2. q-side: actual q-pilot object，其 log-volume 为 `-|log(q)|`，不带 Ind1-3；
3. anab-side: Θ-pilot object + 所有 possible images + holomorphic hull，带 Ind1-3；
4. 两侧用**同一个** `j∈F_l^⋆` procession normalization（平均），不是各自任选 real；
5. 按 Remark 3.9.5(vii) 作 `det^{⊗M}` 与 `O(-)` inverse adjustment；
6. 由 Theorem 3.11(ii)(iii) 的 Kummer isomorphisms 与 LGP-link compatibility 连接；
7. 结论是 `-|log(Θ)| ≥ -|log(q)|`，并在 identification 情形下 `A=L_q`（或 inverse value-group `ofAdd(A)=etaPilot⁻¹`），而不是 `A` 与负的 `qPilotSignedLog` 反向相等。

在 Lean shadow 中最弱但正确的 O2 陈述：

```
O2CorrectedVolumeIdentification X :
  Multiplicative.ofAdd (etaRssAtFPlace.logVolume) = (etaPilot X)⁻¹
```

其 exact criterion 是 `(fPlaceVolumeIndex : ℝ) = exp(qPilotLogMagnitude)`；不得把 `1` 作为默认 index。

## 8. 精确 gaps / 不得跳过的 normalization

| gap | 内容 | 为什么不能 arbitrary |
|---|---|---|
| G0 source binding | paper `SourceInitialThetaData` 与 N8 `SourceNativeInitialThetaData`/actual `nativeQActual`、`nativeFPlaceOverBad` 未逐项绑定 | 不能把 actual native q 直接当成 paper source q；不能以 `N8NativeInput` 字段或 completion shell 替代 source six-tuple |
| G1 q-pilot/Θ-pilot source objects | 未有 actual arithmetic line bundles 与 theta divisor/hull 的源构造 | 不能以 `ofAdd` 实数或 `PUnit` 代替 |
| G2 det^{⊗M} 与 O(-) adjustment | 未证明 F-place log-shell index 的 normalization 与 q-pilot line bundle 的 `det^{⊗M}`/`O(-)` 一致 | 不能任选 M 或跳过 structure sheaf inverse；Remark 3.9.5(vii) 明确要求 |
| G3 procession normalization | 未证明 F-place readout 与 q-pilot 使用同一 `j∈F_l^⋆` 平均 | 不能两边各取不同 average |
| G4 Ind1-3 / Kummer / LGP compatibility | Θ side 需 Ind1-3；q side 不带；未构造 Thm3.11(ii)(iii) 的 actual Kummer compatible data | 不能把 arbitrary map 或 scalar equality 当作 comparison |
| G5 q/e/f index formula | F-place q/e/f hypothesis 未供给；production 只有 conditional formula | 不能无条件断言 `fPlaceVolumeIndex=exp` |
| G6 sign | paper signed volumes 负；Lean `fPlaceLogVolume` 非负 | 不能在未加负号/未取 inverse 时比较 |

## 9. 验收清单（O2 audit）

- [ ] 是否只使用同一 initial Θ-data、同一 n、同一 procession labels？
- [ ] q-pilot 是否不带 Ind1-3，Θ-pilot 是否带 Ind1-3 并取 hull？
- [ ] 是否使用 `-|log(q)|` / `-|log(Θ)|` 的负号，而不是 Lean 的非负 `fPlaceLogVolume`？
- [ ] 是否使用 `det^{⊗M}` + `O(-)` inverse adjustment，而不是 index 1/`O` 的平凡 normalization？
- [ ] volume index 是否用 `exp(-qPilotSignedLog)`，而不是任意正整数？
- [ ] 是否把 O2 identification 与 Theorem B inequality 分开（index1 可满足 inequality 但不满足 identification）？
- [ ] 是否避免在 q-side/anab-side 之间引入 arbitrary map/equality？

## 10. 结论

O2 当前不能构造，也不能以 index 1 完成。正确的 normalization 是

```
volumeIndex = exp(-qPilotSignedLog) = exp(qPilotLogMagnitude) > 1,
fPlaceLogVolume = log(volumeIndex) = -qPilotSignedLog = |log(q)|,
ofAdd(fPlaceLogVolume) = etaPilot⁻¹.
```

index 1 给出 `fPlaceLogVolume=0`，与负的 q-pilot log-volume `qPilotSignedLog<0` 矛盾；它只对应 `O` 的 unit-ball normalization，漏掉 Remark 3.9.5(vii) 的 `det^{⊗M}`/`O(-)` adjustment。O2 真正缺少的是 q-pilot/Θ-pilot arithmetic line bundle 的 source comparison 与同一 procession normalization，而不是一个可以任取的 volume index。

