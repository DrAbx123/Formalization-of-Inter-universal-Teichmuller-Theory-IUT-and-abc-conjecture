# S1539: promachina Gaussian 算术数据只读审计

日期：2026-10-31
快照：`D:\lean\vendor\promachina\snapshots\1fa6387f11fb6dc67eb618b8138e6bc64f56b039`
工具链：`leanprover/lean4:v4.30.0`；Mathlib `v4.30.0`（`lakefile.toml:15`）。
审计方式：只读源码与行号审计；未编译、未写入、未修改 `vendor/promachina`。
实测范围：`Iut/` 共 209 个 `.lean` 文件、43,428,751 字节、773,305 行。快照 review 记录为 310 个 tracked 文件 / 210 个 Lean 文件、上游构建 4443 jobs。用户给出的“9640 文件 / 3.4M 行”与 `Iut/` 子树不符，应指整个工作区；本报告的行号均针对上述快照。

## 0. 结论摘要

| 问题 | 判定 | 关键依据 |
|---|---|---|
| promachina 是否有 concrete Gaussian 算术数据（F/Fmod/K、curve、torsion、KernelField 的实例）？ | **没有。** 只有参数化接口和 abstract smoke tests；没有构造具体数域、具体曲线、具体 ClauseC/KernelField 实例。 | `InitialThetaDataExample.lean` 的 Fmod/F/K 全是 section 变量；全树无 `AdjoinRoot`、`GaussianInt`、`QuadraticField`、`ZMod 5`、`ℚ_5` 的具体构造。 |
| K 是否被强制为非平凡扩张？ | **接口层不强制。** `ThetaFieldTower`/`InitialThetaData` 允许 K=F；只有 `kIdentification` 把 K 钉到模 l 表示的核固定域。若同时有 `ImageContainsSL2`，数学上 K≠F（[K:F] ≥ l(l²−1) ≥ 120），但 promachina **没有形式化**这个非平凡性/次数下界。 | `InitialThetaData.lean:81`、`:4845`、`:4851`、`:4942`、`:4955`；无 `Nontrivial`/`K ≠ F`/`finrank F K` 定理。 |
| promachina 的 SourceClauseC 与 SL2 是否一致？ | **接口内部一致。** 表示由实际 Galois 作用和 torsion basis 定义，K 由 `kIdentification` 识别为核固定域，`IsKernelField` 是定理；不存在“独立表示与 K 不一致”的入口。但 clause 本身不包含 K 的有限/Galois 实例，也不包含 torsion23；两者在 ClauseB / 环境类型类中。 | `SourceInitialThetaDefinition.lean:162`、`:171`、`:173`；`toCore_kernelField` `:525`；`SourceInitialThetaCore.k_is_kernel_field` `SourceInitialThetaData.lean:5908`。 |
| 本地 concrete Gaussian 数据能否直接作 ClauseC witness？ | **不能。** 本地 `gaussianInitialThetaArithmeticData` / `concreteGaussianInitialThetaArithmeticData` 都取 Fmod=F=K=GaussianField（K/F 平凡），与 ClauseC + SL2 不相容。 | `ConcreteArithmeticExample.lean:64-77`；`ConcreteFinitePlaceBoundary.lean:25-31`；`SourceHodgeTheaterFamilyLawsReduction.lean:265-271`（`gaussianJ1728ArithmeticData`）。 |
| 可移植的是什么？ | **接口设计（kIdentification + 派生表示/核域）**，不是具体 Gaussian 数据。 | 见第 5 节。 |

一句话：**promachina 没有可抄的 concrete Gaussian arithmetic；它提供了正确的 K 绑定设计，但没有证明 K 非平凡。** 本地 K=F 的 Gaussian 测试载体不能用来填 ClauseC/SL2；若需要 ClauseC，K 必须换成实际 `galoisLTorsionKernelField`（或其同构像）。

## 1. 搜索证据：确实没有 concrete Gaussian 数据

在 `Iut/` 内检索（`*.lean`）：

| 模式 | 命中 | 说明 |
|---|---:|---|
| `AdjoinRoot` | 0 | 没有用多项式商构造具体数域。 |
| `GaussianInt` / `QuadraticField` | 0 / 0 | 没有高斯整数环或二次域类型。 |
| `ZMod 5` / `ℚ_5` | 0 / 0 | 没有把 l=5 或 Q_5 写成具体域。 |
| `NumberField` 的实例构造 | 只有 kernel field 的 `NumberField.of_module_finite`（`InitialThetaData.lean:4828-4835`） | 其余 `NumberField` 都是类型类假设。 |
| `ThetaFieldTower` 的使用 | 4 个文件、13 处 | 全部是参数化声明或 abstract constructor；无具体 `Fmod F K` 实例。 |

关键反证：

* `InitialThetaDataExample.lean:85-95` 明确在 `section AbstractConstructor` 中把 `Fmod F K` 设为变量，只做构造器 smoke test。
* `InitialThetaDataExample.lean:1300-1305` 的 `abstractThetaFieldTower` 只是把 `sqrtMinusOne` 和 `hDegree` 打包；F、K 仍是变量。
* `InitialThetaDataExample.lean:1414-1447` 的 `abstractInitialThetaData` 接收全部数据作为参数，不构造具体算术。
* `InitialThetaDataExample.lean:1318` 的曲线是 `PuncturedEllipticCurve.ofJ F (37 : F)`，F 仍是任意域，不是 Q(i)。
* `SourceInitialThetaData.lean:5670-5678` 的 `SourceInitialThetaCore` 以 `(Fmod F K : Type u)` 为参数。
* `InitialThetaDataExample.lean:21-24` 唯一的“具体”算术对象是 `primeFive : PrimeGeFive`（l=5）；它是标签素数，不是域。

“Gaussian”在 promachina 中的实际含义是**标签/次数层面的 Gaussian monoid**，不是高斯域 Q(i) 的算术：

* `Stage1/IUTStage1Gaussian.lean:208` 的 `IUTStage1ZModSquareWeightProfile`；
* `:1140` 的 `GaussianMonoidDegreeEvaluation`（environmentDegree : Real，gaussianDegree : label → Real）；
* `:2537` / `:2657` 的 theta value/evaluation source（只带 `{F : Type v} [Field F]` 和抽象 orbicurve）；
* `Foundations/SourceKummerGaussianSynchronization.lean:984` 的 `gaussianSquareWeight`、`:1012` 的 `gaussianArithmeticDegree`（Real 值）。

因此，把 promachina 的“Gaussian”误读为 Q(i) 的具体算术会得到错误结论；它没有这种数据。

## 2. 五个对象的准确声明

说明：下表中只写 `:行号` 的条目，沿用同一小节上一行明确写出的文件；跨文件条目会写全文件名。

### 2.1 F / Fmod / K

| 声明 | 文件:行 | 内容 / 依赖 |
|---|---|---|
| `Iut.PrimeGeFive` | `Foundations/InitialThetaData.lean:44` | `value : ℕ`、`prime : Nat.Prime value`、`ge_five : 5 ≤ value`。 |
| `Iut.SqrtMinusOneData` | `InitialThetaData.lean:69` | `element : F`、`square_eq_neg_one : element ^ 2 = -1`；依赖 `[Field F]`。 |
| `Iut.ThetaFieldTower` | `InitialThetaData.lean:81` | 字段只有 `sqrtMinusOne` 和 `degreePrimeToL_holds`；Fmod/F/K 是类型参数，带 `NumberField`、`Algebra`、`IsScalarTower`、`FiniteDimensional`、`IsGalois` 类型类。**没有 K≠F 字段。** |
| `Iut.InitialThetaData` | `InitialThetaData.lean:5009` | 顶层数据；`:5015` 要求 `[FiniteDimensional F K] [IsGalois F K]`；`lTorsionRepresentation` `:5020`，`lTorsionImageContainsSL2` `:5031`。 |
| `Iut.SourceInitialThetaDefinition` | `SourceInitialThetaDefinition.lean:397` | 逐 clause 的 Definition 3.1；`:404-405` 同样把 K 的有限/Galois 作为环境类型类；`toCore` `:464`。 |

### 2.2 curve

| 声明 | 文件:行 | 内容 / 依赖 |
|---|---|---|
| `Iut.PuncturedEllipticCurve` | `InitialThetaData.lean:144` | `curve : WeierstrassCurve F`、`isElliptic`、`puncture : curve.toProjective.Point`。 |
| `Iut.PuncturedEllipticCurve.ofJ` | `InitialThetaData.lean:162` | 从 `WeierstrassCurve.ofJ j` 造曲线，puncture=0；任意 F、任意 j。 |
| `Iut.ThetaCurveModuliData` | `InitialThetaData.lean:2542` | `xF : PuncturedEllipticCurve F`、`cF`、moduli/stable reduction/torsion23 等。 |
| `Iut.SourceThetaCurveModuliData` | `SourceInitialThetaData.lean:1242` | source-native 曲线 moduli；`xF` `:1247`，`schemeRealization` `:1248`，`fieldOfModuli` `:1250`，`torsion23Rational` `:1252`，`signQuotient` `:1253`。 |
| `Iut.SourceThetaKCoreData` | `SourceInitialThetaData.lean:1452` | K-侧 X_K/C_K 由 scalar extension 构造；`curveExtension` `:1456`，`orbicurveExtension` `:1458`。 |
| `Iut.PuncturedEllipticCurve.baseChangeOrigin` | `SourceInitialThetaData.lean:1278` | 实际 Weierstrass base change，puncture=0。 |

### 2.3 torsion clause

| 声明 | 文件:行 | 内容 / 依赖 |
|---|---|---|
| `Iut.PuncturedEllipticCurve.AllNTorsionRational` | `InitialThetaData.lean:502` | 所有 n-torsion 点 rational over F，用 base-change 点像表达。 |
| `Iut.PuncturedEllipticCurve.Torsion23Rational` | `InitialThetaData.lean:515` | `X.AllNTorsionRational 6`。 |
| `Iut.PuncturedEllipticCurve.LTorsion` | `InitialThetaData.lean:525` | `AddSubgroup.torsionBy X.AlgebraicClosurePoint l.value`；`:530` 给出 `ZMod l`-module。 |
| `Iut.ThetaCurveModuliData.torsion23RationalOverF` | `InitialThetaData.lean:2552` | 2/3 torsion 放在 curve moduli（ClauseB 的字段）。 |
| `Iut.SourceThetaCurveModuliData.torsion23Rational` | `SourceInitialThetaData.lean:1252` | source-native 版本。 |
| `Iut.ThetaLTorsionRepresentationData` | `InitialThetaData.lean:4845` | `torsionBasis` `:4849`、`kIdentification` `:4851`；表示本身由 `:4871` 定义。 |
| `Iut.ThetaFQParameterOrderData` | `InitialThetaData.lean:4966` | q 参数 order；`OrdersPrimeToL` `:4988`。 |

注意：promachina 的 `SourceInitialThetaClauseC`（`SourceInitialThetaDefinition.lean:162`）**没有** `Torsion23Rational` 字段；它在 ClauseB 的 `curveModuli` 中（`SourceInitialThetaClauseB` `:142`，`curveModuli` `:149`）。这不是丢失，而是 clause 拆分不同；移植时不要误以为 ClauseC 自带 torsion23。

### 2.4 KernelField

| 声明 | 文件:行 | 内容 / 依赖 |
|---|---|---|
| `Iut.PuncturedEllipticCurve.galoisLTorsionMatrixRepresentation` | `InitialThetaData.lean:4653` | 把 `E[l]` 的 Galois 作用经 torsion basis 转成 GL₂ 矩阵表示；依赖 `galoisActionOnLTorsionGeneralLinearRepresentation`、`Matrix.GeneralLinearGroup.toLin`、`LinearMap.GeneralLinearGroup.congrLinearEquiv`。 |
| `...galoisLTorsionKernelSubgroup` | `:4753` | 表示的核。 |
| `...galoisLTorsionKernelClosedSubgroup` | `:4762` | 带 Krull 闭性的核；依赖 `OpenSubgroup.isClosed`。 |
| `...galoisLTorsionKernelField` | `:4777` | `IntermediateField.fixedField` 的核固定域。 |
| `...galoisLTorsionKernelField_fixingSubgroup` | `:4787` | 固定核域的子群 = 表示核；依赖 `InfiniteGalois.fixingSubgroup_fixedField`，需 `[CharZero F]`。 |
| `...galoisLTorsionKernelField_finiteDimensional` | `:4800` | 由核开性得有限维；依赖 `InfiniteGalois.isOpen_iff_finite`。 |
| `...galoisLTorsionKernelField_isGalois` | `:4814` | 核正规 ⇒ 核域 Galois；依赖 `InfiniteGalois.normal_iff_isGalois`、`MonoidHom.normal_ker`。 |
| `...galoisLTorsionKernelField_numberField` | `:4828` | 依赖 `NumberField.of_module_finite`。 |
| `Iut.ThetaLTorsionRepresentationData` | `:4845` | 字段 `torsionBasis` (`:4849`)、`kIdentification : K ≃ₐ[F] X.galoisLTorsionKernelField l torsionBasis` (`:4851`)。 |
| `...representation` | `:4871` | 直接定义为 `X.galoisLTorsionMatrixRepresentation l data.torsionBasis`。 |
| `...kernelFixedField` | `:4910` | K 所识别的固定域。 |
| `...embeddedK` | `:4916` | `kIdentification` 诱导的 K→Fbar 像。 |
| `...embeddedK_eq_kernelFixedField` | `:4922` | 证明 `embeddedK = kernelFixedField`；这是 range 条件。 |
| `...IsKernelField` | `:4942` | `data.embeddedK = data.kernelFixedField`。 |
| `...isKernelField` | `:4946` | 由 `kIdentification` 直接推出 `IsKernelField`，不是输入。 |
| `...ImageContainsSL2` | `:4955` | `∀ g : SpecialLinearGroup (Fin 2) (ZMod l), ∃ sigma, representation sigma = toGL g`。 |

### 2.5 clause/core 包装

| 声明 | 文件:行 | 内容 / 依赖 |
|---|---|---|
| `Iut.SourceInitialThetaClauseB` | `SourceInitialThetaDefinition.lean:142` | `curveModuli` `:149`、`badModuli` `:150`、`degreePrimeToL` `:151`、bad places multiplicative reduction `:153`。 |
| `Iut.SourceInitialThetaClauseC` | `SourceInitialThetaDefinition.lean:162` | `representation : ThetaLTorsionRepresentationData l F K clauseB.curveModuli.xF` `:171`、`imageContainsSL2` `:173`、bad residue/q-order 条件 `:174-188`。**没有 K 的有限/Galois 字段，没有 torsion23。** |
| `Iut.SourceInitialThetaDefinition` | `SourceInitialThetaDefinition.lean:397` | 汇总 clauses A/B/C/D/F/E；`toCore` `:464`。 |
| `...fieldTower` | `:446` | 从 clauseA/B 派生 `ThetaFieldTower`。 |
| `...toCore_kernelField` | `:525` | 从 clauseC 派生 `IsKernelField`。 |
| `Iut.SourceInitialThetaCore` | `SourceInitialThetaData.lean:5670` | source-native 大记录；`lTorsionRepresentation` `:5706`、`lTorsionImageContainsSL2` `:5708`；`:5677-5678` 要求 K 的有限/Galois。 |
| `...k_is_kernel_field` | `:5908` | 从 core 直接读 `IsKernelField`。 |
| `...image_contains_SL2` | `:5912` | 从 core 直接读 `ImageContainsSL2`。 |
| `...xF_torsion23Rational` | `:5844` | 从 curveModuli 读 `Torsion23Rational`。 |

## 3. K 是否非平凡扩张

### 3.1 类型层：允许 K = F

`ThetaFieldTower`（`InitialThetaData.lean:81-90`）的字段只有：

- `sqrtMinusOne : SqrtMinusOneData F`；
- `degreePrimeToL_holds : Nat.Coprime (Module.finrank Fmod F) l.value`。

K 只出现在类型类参数中：

```lean
[Field K] [NumberField K] [Algebra F K]
[Algebra Fmod K] [IsScalarTower Fmod F K]
[FiniteDimensional F K] [IsGalois F K]
```

取 `K := F` 时，`Field F`、`NumberField F`、`Algebra F F`、`IsScalarTower Fmod F F`、`FiniteDimensional F F`、`IsGalois F F` 都成立；`degreePrimeToL_holds` 只涉及 `Fmod/F`，与 K 无关。因此 **`ThetaFieldTower` 不能排除 K=F**。

同样，`InitialThetaData`（`:5009-5015`）和 `SourceInitialThetaCore`（`SourceInitialThetaData.lean:5670-5678`）只要求 `[FiniteDimensional F K] [IsGalois F K]`；`SourceInitialThetaDefinition`（`:397-405`）也一样。整个快照没有 `K ≠ F`、`finrank F K > 1`、`Nontrivial (Gal(K/F))` 的字段或定理。

### 3.2 kIdentification 的约束

`ThetaLTorsionRepresentationData.kIdentification`（`InitialThetaData.lean:4851`）是唯一把 K 与曲线绑定的数据：

```lean
kIdentification :
  K ≃ₐ[F] X.galoisLTorsionKernelField l torsionBasis
```

它强制 K 是模 l 表示核的固定域（F-代数同构）。由此：

- `IsKernelField` 是定理（`:4946`），不是独立输入；
- K 的有限性/Galois 性在数学上随之而来（核域有 `:4800`/`:4814` 实例），但 promachina **没有**把它们作为 K 的实例或定理写出来；
- 若表示是平凡的，核固定域 = F，则 K=F 是被允许的；
- 单看 `kIdentification`，没有非平凡性。

### 3.3 加上 SL2 后的语义后果（未形式化）

设 `ρ = data.representation`，`H = ker ρ`，K ≅ Fbar^H。因为 H 开正规，`Gal(K/F) ≅ G_F/H ≅ im ρ`。`ImageContainsSL2` 给出

```
SL₂(F_l) ≤ im ρ.
```

取 `-I ∈ SL₂(F_l)`。l ≥ 5 时 `-1 ≠ 1` 于 `ZMod l`，故 `toGL (-I) ≠ 1`，于是 im ρ 非平凡，H ≠ G_F，K ≠ F。更定量地：

```
[K:F] = |Gal(K/F)| = |im ρ| ≥ |SL₂(F_l)| = l(l²−1) ≥ 120.
```

**但这个推导在 promachina 中不存在。** 我检索了 `InitialThetaData.lean` 与相关文件：没有 `K ≠ F`、没有 `finrank F K` 的下界、没有 `Nontrivial` 的核域/像定理。因此严格的回答是：

* **接口层：K 不是被强制为非平凡扩张；**
* **语义层：只要 `ImageContainsSL2` 为真，K 必然非平凡，且次数至少 120（l=5）；**
* **形式层：这一语义后果未被证明，也没有被记录为 theorem/instance。**

### 3.4 与本地 concrete Gaussian 数据的对照

本地 concrete Gaussian 数据（不在 promachina 中）是：

* `LeanFormal/IUT/IUTI/InitialTheta/ConcreteArithmeticExample.lean:44-45`：`GaussianField := AdjoinRoot (X^2 + 1)`；
* `:64-69`：`gaussianIdentityThetaTower`，三个域全是 `GaussianField`；
* `:71-77`：`gaussianInitialThetaArithmeticData`，`Fmod := GaussianField`、`F := GaussianField`、`K := GaussianField`。

另一份：

* `ConcreteFinitePlaceBoundary.lean:25-31`：`concreteGaussianInitialThetaArithmeticData`，同样 Fmod=F=K=GaussianField；
* `SourceHodgeTheaterFamilyLawsReduction.lean:265-271`：`gaussianJ1728ArithmeticData`，同样 Fmod=F=K=GaussianField，identity tower。

所以本地 concrete Gaussian 数据的 K/F 是**平凡扩张**（`Module.finrank_self = 1`，见 `ConcreteArithmeticExample.lean:67-69`）。它作为 `InitialThetaArithmeticData` 的测试载体是合法的，但**不能**作为 ClauseC/SL2 的 witness：`kIdentification : GaussianField ≃ₐ GaussianField` 只有在核固定域恰为 GaussianField 时才成立，而 `ImageContainsSL2` 要求表示非平凡，二者不相容（除非该曲线的模 l 表示平凡，此时 SL2 条件又失败）。这不是 promachina 接口的矛盾，而是本地具体实例选错了 K。

## 4. SourceClauseC / SL2 的一致性

### 4.1 promachina 的设计

`SourceInitialThetaClauseC`（`SourceInitialThetaDefinition.lean:162-188`）只有：

- `representation : ThetaLTorsionRepresentationData l F K clauseB.curveModuli.xF`（`:171`）；
- `imageContainsSL2 : representation.ImageContainsSL2`（`:173`）；
- bad residue/q-order 条件（`:174-188`）。

其中 `representation` 不是任意同态：`ThetaLTorsionRepresentationData.representation`（`InitialThetaData.lean:4871`）定义为 `X.galoisLTorsionMatrixRepresentation l data.torsionBasis`。`IsKernelField` 由 `kIdentification` 推出（`:4946`），clause 中没有独立的 `representation_eq_canonical` 或 range 字段。

因此：

* **不存在“独立表示与 K 不一致”的入口**；表示由实际 Galois 作用和 torsion basis 固定；
* **不存在“range 条件忘记证”的入口**；`embeddedK_eq_kernelFixedField` 直接由 `kIdentification` 推出；
* `ImageContainsSL2` 只是对曲线的附加条件，和 `kIdentification` 不冲突；它使 K 非平凡（语义上），但并不单独构造 K；
* 作为一个接口，它**一致**（没有 `False` 定理，也没有互相矛盾的两个表示）；它只是**条件性**的：需要一条实际曲线、一个 torsion basis 和 SL2 像条件。

### 4.2 与本地 `SourceClauseC` 的逐字段对照

本地 `SourceClauseC`（`LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:1007-1033`）与 promachina 的对应关系：

| 本地字段 | 本地行 | promachina 对应 | 判定 |
|---|---:|---|---|
| `torsion23_rational` | `:1011` | ClauseB 的 `curveModuli.torsion23Rational`（`SourceInitialThetaDefinition.lean:149` + `SourceInitialThetaData.lean:1252`） | 位置不同；内容相同，移植时需显式携带或从 B 取。 |
| `torsion_basis` | `:1012` | `ThetaLTorsionRepresentationData.torsionBasis`（`:4849`） | 相同。 |
| `representation` | `:1018` | `ThetaLTorsionRepresentationData.representation`（`:4871`） | promachina 是定义，本地是字段；可去掉本地字段。 |
| `representation_eq_canonical` | `:1021` | `rfl`（因为 `representation` 就是 canonical） | 可去掉。 |
| `image_contains_SL2`（`≤ range`） | `:1023-1026` | `ImageContainsSL2`（`∀ g, ∃ sigma`，`:4955`） | 等价；本地已有 `largeImageSL2_iff_forall`（`SourceTorsionCarrierReduction.lean:65`）。 |
| `kernel_field_identification` | `:1027-1029` | `kIdentification`（`:4851`） | 相同。 |
| `kernel_field_identification_range` | `:1030-1033` | `embeddedK_eq_kernelFixedField`（`:4922`） | promachina 证明它是定理；本地可删去该字段。 |

这张表说明：promachina 的设计比本地 `SourceClauseC` 更精简，且去掉了两个可推导字段。本地 `SourceTorsionCarrierReduction.lean` 已经在做同样的 reduction（`SourceTorsionDatum` `:130`、`kernelField_identification_range` `:168`、`toSourceClauseC` `:187`），但 `SourceClauseC` 结构本身仍保留旧字段。若移植 promachina 的设计，可以进一步简化本地结构。

### 4.3 形式缺口（不是矛盾，但移植必须补）

1. **K 非平凡性未证。** 建议新增引理（不在 promachina）：
   `kernelField_ne_bot_of_imageContainsSL2`，或 `finrank_kernelField_ge_sl2_card`。
   证明路线：`-I ∈ SL₂`、`toGL (-I) ≠ 1` ⇒ 表示非平凡 ⇒ 核真包含 ⇒ 固定域 ≠ F。
2. **ClauseC 不带 K 的完整 tower 实例。** `SourceInitialThetaClauseC` 的参数只有 `[Field K] [NumberField K] [Algebra F K]`；`[Algebra Fmod K]`、`[IsScalarTower Fmod F K]`、`[FiniteDimensional F K]`、`[IsGalois F K]` 只在 `SourceInitialThetaDefinition`/`InitialThetaData`/`SourceInitialThetaCore` 的环境类型类中。移植 ClauseC 时要么加参数，要么从 `kIdentification` 传输实例。
3. **ClauseC 不带 torsion23。** 它在 ClauseB；移植时保持本地 `torsion23_rational` 字段，或引入 `SourceInitialThetaClauseB` 风格的 curve moduli。
4. **没有给出具体曲线 + SL2 证明。** promachina 只把 `ImageContainsSL2` 当 `Prop`，不证明任何具体曲线的模 l 像包含 SL2；这不奇怪（Serre 型大像定理不在快照中）。
5. **没有构造 `ThetaLTorsionRepresentationData`。** 它要求实际 `torsionBasis : (Fin 2 → ZMod l) ≃ₗ X.LTorsion l`；promachina 只把它作为 clause 输入。

### 4.4 判定

* **promachina 的 SourceClauseC 与 SL2 一致**：同一 canonical 表示、K 是核固定域、SL2 是附加条件；没有形式矛盾。
* **但 ClauseC + SL2 强制 K 非平凡**；promachina 没有把这条语义后果形式化。
* **本地 concrete Gaussian 的 K=F 与 ClauseC + SL2 不一致**；该数据只能用于 `InitialThetaArithmeticData`/Hodge theater 的测试，不能作为 Definition 3.1(c) 的完整 witness。若要使用，必须把 K 换成实际核域（l=5 时次数至少 120）或同构的非平凡扩张。

## 5. 可移植声明清单

### 5.1 已经本地镜像的 KernelField 机制

本地 `LeanFormal/IUT/Foundations/Geometry/EllipticTorsion.lean` 已有与 promachina 几乎逐行对应的实现：

| promachina 声明 | 行 | 本地对应 | 本地行 |
|---|---:|---|---:|
| `galoisLTorsionMatrixRepresentation` | `InitialThetaData.lean:4653` | `PuncturedEllipticCurve.galoisLTorsionMatrixRepresentation` | `EllipticTorsion.lean:311` |
| `galoisLTorsionKernelSubgroup` | `:4753` | 同名 | `:410` |
| `galoisLTorsionKernelClosedSubgroup` | `:4762` | 同名 | `:419` |
| `galoisLTorsionKernelField` | `:4777` | 同名 | `:431` |
| `...fixingSubgroup` | `:4787` | 同名 | `:441` |
| `...finiteDimensional` | `:4800` | 同名 | `:454` |
| `...isGalois` | `:4814` | 同名 | `:467` |
| `...numberField` | `:4828` | 同名 | `:481` |

结论：**KernelField 的底层机制已经可移植/已移植**；真正缺的是更高层的 `ThetaLTorsionRepresentationData` 设计和 ClauseC 形状。

### 5.2 直接可移植（需改 namespace）

| 声明 | 快照位置 | 直接依赖 | 备注 |
|---|---|---|---|
| `Iut.SqrtMinusOneData` | `InitialThetaData.lean:69` | `Field` | 无曲线依赖。 |
| `Iut.ThetaFieldTower` | `:81` | `PrimeGeFive`、`SqrtMinusOneData`、数域/Galois 类型类 | 可移植；注意它不强制 K 非平凡。 |
| `Iut.PuncturedEllipticCurve` | `:144` | `WeierstrassCurve`、`IsElliptic` | 本地已有同名结构。 |
| `Iut.PuncturedEllipticCurve.ofJ` | `:162` | `WeierstrassCurve.ofJ`、`jInvariant` | 可移植。 |
| `AllNTorsionRational` | `:502` | `AlgebraicClosure`、base change point | 可移植。 |
| `Torsion23Rational` | `:515` | 上述 | 可移植。 |
| `LTorsion` + module instance | `:525` / `:530` | `AddSubgroup.torsionBy`、`ZMod` | 可移植。 |
| `galoisLTorsionMatrixRepresentation` | `:4653` | `galoisActionOnLTorsion...`、`Matrix.GeneralLinearGroup` | 本地已有。 |
| `galoisLTorsionKernelField` + 4 个实例 | `:4777-4835` | `InfiniteGalois.*`、`NumberField.of_module_finite` | 本地已有。 |
| `ThetaLTorsionRepresentationData` | `:4845` | `LTorsion`、`galoisLTorsionKernelField`、`GL₂` | 本地尚无同名；`SourceTorsionDatum` 是近邻。 |
| `...embeddedK_eq_kernelFixedField` | `:4922` | `kIdentification` | 可直接补本地 `kernel_field_identification_range` 的证明。 |
| `...IsKernelField` / `isKernelField` | `:4942` / `:4946` | `embeddedK_eq_kernelFixedField` | 可直接用。 |
| `...ImageContainsSL2` | `:4955` | `SpecialLinearGroup.toGL` | 与本地 `LargeImageContainsSL2` 等价。 |

### 5.3 需适配的 clause / core 层

| 声明 | 快照位置 | 依赖 | 移植建议 |
|---|---|---|---|
| `SourceInitialThetaClauseB` | `SourceInitialThetaDefinition.lean:142` | `SourceThetaCurveModuliData`、`SourceThetaBadModuliData` | 若本地保留 `SourceClauseB`，把 curve moduli/torsion23 放在这里。 |
| `SourceInitialThetaClauseC` | `:162` | ClauseB、`ThetaLTorsionRepresentationData`、`PuncturedEllipticCurveScalarExtension`、`ThetaTateParameterData` | 结构形状可参考；需补 `torsion23` 或从 B 取，补 K 的有限/Galois 实例。 |
| `SourceInitialThetaDefinition` | `:397` | clauses A-F、`SourceInitialThetaCore` | 太大；只在需要完整 Definition 3.1 时参考。 |
| `SourceInitialThetaCore` | `SourceInitialThetaData.lean:5670` | EtaleTheta 全套、Orbicurve、Tate | 不建议整包 port；只取 `lTorsionRepresentation`/kernel 部分。 |
| `SourceThetaKCoreData` | `SourceInitialThetaData.lean:1452` | scalar extension、orbicurve | 若只需要 K-侧 base change，可单独 port。 |

### 5.4 不建议 port

| 声明/文件 | 原因 |
|---|---|
| `InitialThetaDataExample.lean` | 只有 abstract smoke tests；没有具体算术，port 了也不产生数据。 |
| `Stage1/IUTStage1Gaussian.lean` 的 `GaussianMonoidDegreeEvaluation` 等 | Real 值标签/次数模型，不是 F/Fmod/K 或 KernelField。 |
| `Stage1/IUTStage1StepXI/Core.lean`、`Stage1/IUTStage1SourceCore.lean` | 大型下游消费者/通用包；对本问题只提供 shape 参考。 |
| `SourceInitialThetaCore` 整包 | 依赖过重，且仍以抽象 Fmod/F/K 为参数。 |

### 5.5 依赖摘要

* `Foundations/InitialThetaData.lean`：导入 20 个 Mathlib 模块；核心为 `Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ`/`Projective.Point`/`Reduction`、`Mathlib.FieldTheory.Galois.Infinite`、`Mathlib.NumberTheory.NumberField.Completion.FinitePlace`、`Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup`、`Mathlib.Tactic`（第 6-26 行）。
* `Foundations/SourceInitialThetaDefinition.lean`：导入 `Iut.Foundations.SourceInitialThetaData` 与 `Mathlib.NumberTheory.NumberField.Ideal.Basic`（第 6-7 行）。
* `Foundations/SourceInitialThetaData.lean`：导入 `Iut.Foundations.EtaleThetaCovers`、`InitialThetaData`、`Orbicurve`、`OrbicurvePullback`、`SourceAnabelioid`、`SourceTateCurve`（第 6-11 行）+ 4 个 Mathlib 模块。
* `Stage1/IUTStage1Gaussian.lean`：只导入 `Iut.Stage1.IUTStage1StepX`（第 6 行）。
* `Stage1/IUTStage1StepXI/Core.lean`：导入 `IUTStage1Theorem311`、`IUTStage1HodgeArakelovPilots`、`IUTStage1ConstructedTheorem311`（第 6-8 行）。
* `Stage1/IUTStage1SourceCore.lean`：导入 `IUTStage1HodgeTheaterSource`、`IUTStage1Data` + 9 个 Mathlib 模块（第 6-16 行）。

### 5.6 Lean 4.32.2 / 本地 Mathlib 兼容性

本项目的 Mathlib 为 4.32.2。上述 KernelField 证明依赖的关键 lemma 在本地 `D:/lean/.lake/packages/mathlib` 中存在：

* `InfiniteGalois.fixingSubgroup_fixedField`（`Mathlib/FieldTheory/Galois/Infinite.lean:145`）；
* `InfiniteGalois.isOpen_iff_finite`（`:240`）；
* `InfiniteGalois.normal_iff_isGalois`（`:260`）；
* `NumberField.of_module_finite`（`Mathlib/NumberTheory/NumberField/Basic.lean:65`）；
* `AddSubgroup.torsionBy.zmodModule`（`Mathlib/Algebra/Module/Torsion/Basic.lean:1009`）；
* `Matrix.SpecialLinearGroup.toGL_injective`（`Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean:264`）。

因此 **KernelField/矩阵表示链在 4.32.2 下按源码形状可移植**；但这只是 API 存在性检查，未编译移植结果。

## 6. 建议的下一步

1. **不要继续在 promachina 找 concrete Gaussian 数据**：没有；最多只能拿到抽象接口。
2. **若移植 ClauseC 设计**：采用 `ThetaLTorsionRepresentationData` 的 `torsionBasis + kIdentification` 结构；删掉本地 `SourceClauseC.representation`、`representation_eq_canonical`、`kernel_field_identification_range` 三个冗余字段（用 `rfl` 和 `embeddedK_eq_kernelFixedField` 替代），并相应修改 `SourceClauseConstructors.ofCanonicalRepresentation` / `SourceCompletion` / `SourceTorsionCarrierReduction.toSourceClauseC`。
3. **补 K 非平凡性引理**：从 `ImageContainsSL2` 证明 `data.kernelFixedField ≠ ⊥`（等价地 K≠F），最好再给 `[K:F] ≥ l(l²−1)`。这是 promachina 没有的、真正减少缺口的一步。
4. **本地 concrete Gaussian 数据只作 `InitialThetaArithmeticData` 测试载体**：`gaussianInitialThetaArithmeticData` / `concreteGaussianInitialThetaArithmeticData` 的 K=F 不能用于 ClauseC/SL2。若需要具体 ClauseC 数据，K 必须取实际 `galoisLTorsionKernelField`（l=5 时次数至少 120）或同构的非平凡扩张；不能再用 `GaussianField` 充当 K。
5. **若移植 ClauseC**：显式携带 `Torsion23Rational`（或从 ClauseB 取），并显式携带/派生 `[FiniteDimensional F K]`/`[IsGalois F K]`。
6. **不要修改 promachina**；所有改动只在本项目。

## 7. 验证状态

* 本报告是**只读源码审计**：未在 promachina 运行 `lake build`、`lake env lean`、`#check`、`#print axioms`，未生成/修改任何 `.olean` 或源文件。
* 行号通过直接读取快照文件核对；文件计数/行数由 PowerShell 统计。
* 审计的四个重点文件（`IUTStage1Gaussian.lean`、`IUTStage1StepXI/Core.lean`、`IUTStage1SourceCore.lean`、`SourceInitialThetaData.lean`）以及 `InitialThetaData.lean`、`SourceInitialThetaDefinition.lean` 经文本扫描：无 `sorry`/`admit`，无顶层 `axiom`/`opaque` 声明；`StepXI/Core.lean:6809`、`:10738` 与 `SourceCore.lean:36826` 的 “opaque” 只出现在注释/文档字符串中。
* promachina 的 `review-1fa6387f.json` 记录上游完整构建通过（4443 jobs, Lean 4.30.0）；本审计未重新运行该构建，故不把“构建通过”当作本次审计结果。
* 第 3.3 节的 K 非平凡性/次数下界是**数学论证**，不是本次运行的形式化定理；promachina 中没有对应声明。
* 依赖/兼容性结论来自源码与本地 Mathlib API 检索，未编译验证移植。

## 8. 附：最小结论表

| 需要的东西 | promachina 是否有 | 准确入口 | 备注 |
|---|---|---|---|
| 具体 Fmod/F/K | 否 | `ThetaFieldTower` `InitialThetaData.lean:81` | 参数化，非具体。 |
| 具体 curve | 否 | `PuncturedEllipticCurve` `:144`；`ofJ` `:162` | 任意 F/j。 |
| 2/3 torsion | 接口有，数据无 | `Torsion23Rational` `:515`；ClauseB `SourceInitialThetaDefinition.lean:149` | 无具体曲线实例。 |
| l-torsion basis | 接口有，数据无 | `ThetaLTorsionRepresentationData.torsionBasis` `:4849` | 由 clause 输入。 |
| SL2 大像 | Prop 有，证明无 | `ImageContainsSL2` `:4955` | 无曲线验证。 |
| KernelField | 构造有 | `galoisLTorsionKernelField` `:4777` | 但 K 的非平凡性未证。 |
| K = 核固定域 | 有 | `kIdentification` `:4851`；`isKernelField` `:4946` | 这是最值得移植的设计。 |
| K≠F | 无 | — | 需新增引理。 |
| SourceClauseC | 有（抽象） | `SourceInitialThetaClauseC` `SourceInitialThetaDefinition.lean:162` | 不含 torsion23/K 实例。 |

