# IUT-COMPLETION — lana Iut vs LeanFormal（A871 快照）

日期 2026-11-12。数据来自本地源/olean 实际计数；`missing` = 源存在但没有匹配 olean。**oleans 存在 ≠ proof body/axioms 已 gate；最终证据仍需逐文件 `#print axioms` trio。**

## 0. 总览

| 树 | source `.lean` | olean | missing | 量级 |
|---|---|---|---|---|
| lana `Iut/` | 950 | 339 | **611** | 缺失约 177,603 行 / 8.74 MB |
| `LeanFormal/` | 1,189 | 1,011 | **178** | 缺失约 41,677 行 / 1.80 MB |
| `LeanFormal/IUT/Project.lean` import 闭包 | 787 | 787 | **0** | production 链 olean 已闭合 |

关键口径：LeanFormal 的 production `Project` 闭包 **0 missing oleans**；全局 178 missing 全部在 Project 之外（主要是 `Foundations/AlgebraicGeometry`，多数是未接入的可选几何文件）。因此「IUT 形式化除 SSIneq 外完成」在 **LeanFormal production 链** 的意义上是“oleans 已闭合”，但仍需 axiom gate；在 **lana `Iut` standalone MainTheorem** 意义上还差 108 个 closure oleans（见 §2）。

## 1. lana `Iut/` 逐目录

| 目录 | source | olean | missing |
|---|---:|---:|---:|
| Foundations | 256 | 205 | 51 |
| Reconstruction | 156 | 1 | 155 |
| Frobenioid | 138 | 8 | 130 |
| EtaleTheta | 89 | 9 | 80 |
| Concrete | 51 | 6 | 45 |
| Cor312 | 43 | 34 | 9 |
| Tripod | 39 | 9 | 30 |
| AutHolomorphic | 35 | 31 | 4 |
| Anabelian | 23 | 14 | 9 |
| Tower | 20 | 6 | 14 |
| HodgeTheater | 17 | 4 | 13 |
| LogLink | 15 | 0 | 15 |
| Multiradial | 14 | 0 | 14 |
| Wall | 12 | 1 | 11 |
| Abc | 10 | 2 | 8 |
| Implication | 7 | 1 | 6 |
| Arakelov | 5 | 0 | 5 |
| ThetaLink | 5 | 0 | 5 |
| WallEquiv | 5 | 0 | 5 |
| Torsion | 4 | 4 | 0 |
| NumberTheory | 4 | 4 | 0 |
| **total** | **950** | **339** | **611** |

说明：Reconstruction/Frobenioid/EtaleTheta 等大目录缺 olean 多数**不在** MainTheorem 闭包；它们是否必需取决于最终链是否消费。Wall/WallEquiv（SSIneq 所在）也不在 MainTheorem 闭包。

## 2. lana `Iut.MainTheorem` closure（除 SSIneq 的主链）

目标：`Iut/MainTheorem.lean` + `Iut/Concrete/ThetaRegion.lean`。

- import 闭包：**184** 个源文件；
- missing oleans：**108**；
- 缺失体量：**30,809 行 / 1.43 MB**；
- 依赖/构建顺序（自底向上，拓扑序）：`Anabelian -> Cor312 -> Concrete -> Implication -> Tower -> Tripod -> MainTheorem`。

### 2.1 按目录

| 目录 | required | missing |
|---|---:|---:|
| Concrete | 49 | 43 |
| Tripod | 39 | 30 |
| Tower | 20 | 14 |
| Cor312 | 41 | 7 |
| Anabelian | 21 | 7 |
| Implication | 7 | 6 |
| (root) | 1 | 1 |
| Abc | 2 | 0 |
| Torsion | 4 | 0 |

### 2.2 缺失 closure oleans（按拓扑序）

```text
Anabelian/Tempered.lean
Anabelian/GenuineEtale.lean
Cor312/ThetaData/Orbicurve.lean
Cor312/ThetaData/LocalConditions.lean
Anabelian/Torsion.lean
Cor312/ThetaData/LocalTateOfExistence.lean
Cor312/ThetaData/Basic.lean
Cor312/LeftHandSide.lean
Cor312/RightHandSide.lean
Cor312/Statement.lean
Concrete/LocalTheory.lean
Concrete/LocalConstruct/Packet.lean
Concrete/LocalConstruct/Integral.lean
Concrete/LocalConstruct/Indeterminacy.lean
Concrete/LocalConstruct/MaximalOrder.lean
Concrete/LocalConstruct/Archimedean.lean
Concrete/LocalConstruct/Volume.lean
Concrete/LocalConstruct/Admissible.lean
Concrete/LocalConstruct/ThetaAdmissible.lean
Concrete/ThetaLocalConstruct/Ordp.lean
Concrete/LocalConstruct/Arithmetic.lean
Concrete/LocalConstruct/LogShell.lean
Concrete/LocalConstruct/ArchLogShell.lean
Concrete/LocalConstruct/ResidueField.lean
Concrete/LocalConstruct/Hull.lean
Concrete/LocalConstruct/Prop14.lean
Concrete/LocalConstruct/ArchIndAut.lean
Concrete/LocalConstruct/IndAut.lean
Concrete/LocalConstruct/FactorShell.lean
Concrete/LocalConstruct/PacketDifferent.lean
Concrete/LocalConstruct/LatticeSandwich.lean
Concrete/LocalConstruct/TensorIntegral.lean
Concrete/LocalConstruct/ScaleVolume.lean
Concrete/LocalConstruct/LocalDifferent.lean
Concrete/LocalConstruct/Prop14Lattice.lean
Concrete/LocalConstruct/ShellBound.lean
Concrete/LocalConstruct/Theory.lean
Concrete/Container.lean
Anabelian/LocalInputs.lean
Concrete/ThetaLocalConstruct/Data.lean
Concrete/ThetaRegion.lean
Implication/Invariants.lean
Implication/LogVolumeBound.lean
Implication/Theorem110.lean
Concrete/Invariants.lean
Concrete/GaloisPlaces.lean
Concrete/TorsionFieldGalois.lean
Concrete/SectionAverage.lean
Concrete/LocalEstimate.lean
Implication/Corollary22.lean
Implication/Corollary23.lean
Concrete/Main.lean
Anabelian/Existence.lean
Concrete/Existence.lean
Tripod/CurveOf.lean
Concrete/TateInputsConstruct.lean
Concrete/CyclicSubgroup.lean
Concrete/ModEllRepGalois.lean
Concrete/SL2Image.lean
Tripod/CurveFacts.lean
Tripod/TorsionDegree.lean
Tripod/TorsionBasis.lean
Tripod/Galois.lean
Concrete/CurveArithmeticProved.lean
Tripod/StableOdd.lean
Tripod/StableTwo.lean
Concrete/ModEllRepConstruct.lean
Tripod/Providers.lean
Implication/ChebyshevExplicit.lean
Tripod/TwoAdic.lean
Tripod/LogCond.lean
Anabelian/CanLift.lean
Anabelian/CoreOfJ.lean
Tripod/Core.lean
Tripod/Height.lean
Tripod/CyclicTorsion.lean
Tripod/CyclicLocal.lean
Tripod/CyclicBound.lean
Tripod/CyclicIsogeny.lean
Tower/Basic.lean
Tower/Residual.lean
Tower/RamIdx.lean
Tower/LogDK.lean
Tower/DifferentBound.lean
Tower/Different.lean
Tower/StepIII.lean
Tower/Main.lean
Tripod/TpdGalois.lean
Tripod/TpdRamIdx.lean
Tripod/Tower.lean
Tower/Inertia.lean
Tower/TorsionRigid.lean
Tripod/Unramified.lean
Tower/MultiplicativeKernel.lean
Tower/InertiaBound.lean
Tower/WildBound.lean
Tripod/BadRamIdx.lean
Tripod/TpdTorsionRep.lean
Tripod/InertiaUnipotent.lean
Tripod/WildRamIdx.lean
Tripod/TpdInertia.lean
Tripod/TowerFacts.lean
Tower/InertiaInvolution.lean
Tripod/TameTwo.lean
Tripod/Main.lean
Tripod/ClassicalAbc.lean
Tripod/GeneralPosition.lean
MainTheorem.lean
```

结论：若目标是 lana 的 `MainTheorem`，还差 **108 个 oleans**；其中 Concrete 43、Tripod 30、Tower 14、Cor312 7、Anabelian 7、Implication 6、MainTheorem 根 1。**这 108 个中没有 `Iut/Wall`/`WallEquiv`**，SSIneq 是单独 wall（16 missing：Wall 11 + WallEquiv 5）；若把 SSIneq 也纳入最终链，需要额外 16 oleans（且 wall 的数学内容仍需审计）。

## 3. LeanFormal 逐目录

| 目录 | source | olean | missing | 备注 |
|---|---:|---:|---:|---|
| IUT/ABCBridge | 164 | 163 | 1 | ABCBridge 主链几乎全绿 |
| IUT/Audit | 5 | 5 | 0 |  |
| IUT/Foundations | 548 | 373 | 175 | 主要是 AlgebraicGeometry 339/163/176；LocalFields/Geometry 等全绿 |
| IUT/IUTI | 69 | 69 | 0 |  |
| IUT/IUTII | 194 | 191 | 3 |  |
| IUT/IUTIII | 190 | 190 | 0 |  |
| IUT/IUTIV | 14 | 15 | -1 | olean 多于 source（历史/共享） |
| IUT/Verification | 1 | 1 | 0 |  |
| Archive | 1 | 1 | 0 |  |
| **total** | **1,189** | **1,011** | **178** | |

`LeanFormal/IUT/Project.lean` 闭包：**787 个源文件 / 787 oleans / 0 missing**（production 链已闭合）；全局 178 missing 不在 Project 闭包内，不阻塞 `Project`。

## 4. 「除 SSIneq 外完成」还需哪些 oleans

1. **LeanFormal production 链**：`Project` 闭包 0 missing；因此 no missing oleans for the production import graph. 剩余工作是逐文件 `#print axioms` trio gate 和 SSIneq/Cor312 的语义桥，不是补 olean。
2. **lana `Iut` standalone MainTheorem**：还差 §2.2 的 **108 个 closure oleans**（30,809 行 / 1.50 MB）。按依赖序先 Concrete/Cor312/Anabelian，再 Implication/Tower/Tripod；这是编译/闭包工作，不代表 108 个文件都缺数学证明。
3. **SSIneq 自身**：`Iut/Wall` 11 missing + `Iut/WallEquiv` 5 missing = 16 个 oleans；不在 MainTheorem 闭包内，若纳入最终链需单列审计。
4. **其余 lana 缺失**（Reconstruction 155、Frobenioid 130、EtaleTheta 80 等）当前不在 MainTheorem 闭包；不要把它们计入「除 SSIneq 外完成」的必要清单，除非最终链选择消费。

## 5. Multi-lane 进度表

| lane | 当前 green/产物 | 进行中 | 剩余 gap / 下一步 |
|---|---|---|---|
| **mainline** | `Mzk1CRouteAssemblyActual` 装配壳；`ABCFrontier`/height-criterion 等价；`Mzk1FinalBoundarySzpiroActual` 条件桥 | G6 装配壳 | 显式 `E7_radicalBound`/`hE7` 仍未证；ABC gate 未通过 |
| **abc** | `Mzk1RouteCInternalActual`、`Mzk1E7ReductionActual`、`ModularParameterizationDegree`/E7 wire | G2/G3/G4 | E7 四组件内容（Faltings/Petersson/Néron/optimal quotient）；Frey dictionary 两式 |
| **hull** | `Mzk1FreyABCInvariantsActual`、`Mzk1FreyConductorFinalActual`、`Mzk1NeronPeriodBridgeActual` | G1 p∤6 conductor | `N=rad(abc)`、Frey valuations/Weierstrass bridge；Néron period lower bound |
| **shehdd** | `Mzk1DExactLowerActual` L1–L6 + L7 target + exception table；`Mzk1PrimeConductorRouteActual` | L7 D_exact | L7 geometric lower bound；例外 e_p 精确值（external） |
| **qpilot** | green inventory（8,525）；port source inventory；`GREEN-INVENTORY.md`/`PORT-PRIORITY.md` | port sourcing | FLT271 70 sorry/3 axiom；anthro 0 compiled；toolchain drift |
| **lattice** | C-route audits/docs：CLASS-C-UNBLOCK、E7-GAP、OUR-GAPS、IUT-COMPLETION | 文档对账 | 无数学 proof；只做审计/缺口表 |
| **stage4** | evidence isolation registry；theta/deficit 修正 | 上游证据隔离 | FLT271/anthro/vendor 不得进证据链；gate 抽检 |
| **stepxi** | MODULARITY-LINE / old route-α artifacts | 历史线 | 当前无新增 green；是否恢复由 Lead 定 |

## 6. 编译量估计

| 目标 | missing files | source lines | bytes | 说明 |
|---|---:|---:|---:|---|
| lana MainTheorem closure | 108 | 30,809 | 1.43 MB | 实际需要补的 oleans；按依赖序编译 |
| lana Iut all | 611 | ~177,603 | ~8.74 MB | 含大量不在主链的目录 |
| LeanFormal global | 178 | ~41,677 | ~1.80 MB | 不在 Project 闭包；主要是 AlgebraicGeometry |
| LeanFormal Project | 0 | 0 | 0 | production 链无缺 olean |

估计口径：以上是文件/行数，不是 wall-clock；真实编译量取决于 Mathlib import、单文件内存和是否并行。**不得把“oleans 已存在”当作 proof body 已 gate。**


## 7. Executable owner map (A873)

Owner assignment: **qpilot = SSIneq + MainTheorem trunk**, **shehdd = Wall/WallEquiv**, **hull = Concrete**, **stepxi = Tripod/Tower**, **mainline = LeanFormal**, **abc = glue3**.

### 7.1 MainTheorem closure: 108 missing by owner

| owner | files | lines | bytes |
|---|---:|---:|---:|
| qpilot | 21 | 4,322 | 0.20 MB |
| hull | 43 | 12,615 | 0.58 MB |
| stepxi | 44 | 13,872 | 0.65 MB |
| **total** | **108** | **30,809** | **1.43 MB** |

#### qpilot (21)

```text
Anabelian/Tempered.lean
Anabelian/GenuineEtale.lean
Cor312/ThetaData/Orbicurve.lean
Cor312/ThetaData/LocalConditions.lean
Anabelian/Torsion.lean
Cor312/ThetaData/LocalTateOfExistence.lean
Cor312/ThetaData/Basic.lean
Cor312/LeftHandSide.lean
Cor312/RightHandSide.lean
Cor312/Statement.lean
Anabelian/LocalInputs.lean
Implication/Invariants.lean
Implication/LogVolumeBound.lean
Implication/Theorem110.lean
Implication/Corollary22.lean
Implication/Corollary23.lean
Anabelian/Existence.lean
Implication/ChebyshevExplicit.lean
Anabelian/CanLift.lean
Anabelian/CoreOfJ.lean
MainTheorem.lean
```

#### hull (43)

```text
Concrete/LocalTheory.lean
Concrete/LocalConstruct/Packet.lean
Concrete/LocalConstruct/Integral.lean
Concrete/LocalConstruct/Indeterminacy.lean
Concrete/LocalConstruct/MaximalOrder.lean
Concrete/LocalConstruct/Archimedean.lean
Concrete/LocalConstruct/Volume.lean
Concrete/LocalConstruct/Admissible.lean
Concrete/LocalConstruct/ThetaAdmissible.lean
Concrete/ThetaLocalConstruct/Ordp.lean
Concrete/LocalConstruct/Arithmetic.lean
Concrete/LocalConstruct/LogShell.lean
Concrete/LocalConstruct/ArchLogShell.lean
Concrete/LocalConstruct/ResidueField.lean
Concrete/LocalConstruct/Hull.lean
Concrete/LocalConstruct/Prop14.lean
Concrete/LocalConstruct/ArchIndAut.lean
Concrete/LocalConstruct/IndAut.lean
Concrete/LocalConstruct/FactorShell.lean
Concrete/LocalConstruct/PacketDifferent.lean
Concrete/LocalConstruct/LatticeSandwich.lean
Concrete/LocalConstruct/TensorIntegral.lean
Concrete/LocalConstruct/ScaleVolume.lean
Concrete/LocalConstruct/LocalDifferent.lean
Concrete/LocalConstruct/Prop14Lattice.lean
Concrete/LocalConstruct/ShellBound.lean
Concrete/LocalConstruct/Theory.lean
Concrete/Container.lean
Concrete/ThetaLocalConstruct/Data.lean
Concrete/ThetaRegion.lean
Concrete/Invariants.lean
Concrete/GaloisPlaces.lean
Concrete/TorsionFieldGalois.lean
Concrete/SectionAverage.lean
Concrete/LocalEstimate.lean
Concrete/Main.lean
Concrete/Existence.lean
Concrete/TateInputsConstruct.lean
Concrete/CyclicSubgroup.lean
Concrete/ModEllRepGalois.lean
Concrete/SL2Image.lean
Concrete/CurveArithmeticProved.lean
Concrete/ModEllRepConstruct.lean
```

#### stepxi (44)

```text
Tripod/CurveOf.lean
Tripod/CurveFacts.lean
Tripod/TorsionDegree.lean
Tripod/TorsionBasis.lean
Tripod/Galois.lean
Tripod/StableOdd.lean
Tripod/StableTwo.lean
Tripod/Providers.lean
Tripod/TwoAdic.lean
Tripod/LogCond.lean
Tripod/Core.lean
Tripod/Height.lean
Tripod/CyclicTorsion.lean
Tripod/CyclicLocal.lean
Tripod/CyclicBound.lean
Tripod/CyclicIsogeny.lean
Tower/Basic.lean
Tower/Residual.lean
Tower/RamIdx.lean
Tower/LogDK.lean
Tower/DifferentBound.lean
Tower/Different.lean
Tower/StepIII.lean
Tower/Main.lean
Tripod/TpdGalois.lean
Tripod/TpdRamIdx.lean
Tripod/Tower.lean
Tower/Inertia.lean
Tower/TorsionRigid.lean
Tripod/Unramified.lean
Tower/MultiplicativeKernel.lean
Tower/InertiaBound.lean
Tower/WildBound.lean
Tripod/BadRamIdx.lean
Tripod/TpdTorsionRep.lean
Tripod/InertiaUnipotent.lean
Tripod/WildRamIdx.lean
Tripod/TpdInertia.lean
Tripod/TowerFacts.lean
Tower/InertiaInvolution.lean
Tripod/TameTwo.lean
Tripod/Main.lean
Tripod/ClassicalAbc.lean
Tripod/GeneralPosition.lean
```

### 7.2 SSIneq: 16 missing by shehdd (topological order)

All 16 are outside the MainTheorem closure; qpilot owns SSIneq semantics, shehdd owns these Wall/WallEquiv oleans.

```text
Wall/Pilots.lean
Wall/Rss.lean
Wall/Ind3.lean
Wall/EtaAlg.lean
Wall/Checks.lean
Wall/IdentifiedCopies.lean
Wall/QPilotRegion.lean
Wall/Constraints.lean
Wall/Scaling.lean
Wall/MultiContainer.lean
Wall/MultiConstraints.lean
WallEquiv/Basic.lean
WallEquiv/Forms.lean
WallEquiv/Gap.lean
WallEquiv/NonDerivable.lean
WallEquiv/VcI.lean
```

Order rationale: `Wall/Pilots` -> `Rss` -> `Ind3` -> `EtaAlg` -> `Checks` -> `IdentifiedCopies` -> `QPilotRegion` -> `Constraints` -> `Scaling` -> `MultiContainer` -> `MultiConstraints`; then `WallEquiv/Basic` -> `Forms` -> `Gap` -> `NonDerivable`, and `VcI` after `Gap`.

### 7.3 LeanFormal: mainline

- `LeanFormal/IUT/Project.lean` closure: **787/787/0 missing**; production chain has no missing olean and is owned by mainline.
- Global `LeanFormal` missing: **178** (mostly `Foundations/AlgebraicGeometry` 176 outside Project); mainline owns the decision of which optional files enter the production graph. Do not count them as Project blockers.

### 7.4 abc = glue3

Three glue files (the current C-route glue layer):

```text
Mzk1RouteCInternalActual.lean
Mzk1E7ReductionActual.lean
Mzk1CRouteAssemblyActual.lean
```

Their status is green interface/wiring; `Mzk1CRouteAssemblyActual` still requires explicit `E7_radicalBound`/`hE7`, so glue3 does not prove the E7/ABC-strength input.

### 7.5 Owner/compile summary

| owner | outstanding | scope |
|---|---:|---|
| qpilot | 21 closure files + SSIneq semantics | Anabelian/Cor312/Implication/root MainTheorem |
| hull | 43 closure files | Concrete |
| stepxi | 44 closure files | Tripod + Tower |
| shehdd | 16 oleans | Wall + WallEquiv (SSIneq compile) |
| mainline | 0 Project blockers; 178 optional global | LeanFormal production |
| abc | 3 glue files | RouteC/E7/assembly glue; not proof of E7 |

No owner assignment above claims a mathematical gap is closed; it is a build/ownership plan. The 108 MainTheorem oleans + 16 SSIneq oleans are still missing oleans; 178 LeanFormal global missing are outside Project.
