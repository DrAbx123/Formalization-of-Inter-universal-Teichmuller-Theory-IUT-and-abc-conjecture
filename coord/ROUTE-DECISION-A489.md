# A489 路线决定：直接定性版 no-go（parked），显式版为主线

## 决定
- **不再直接攻定性版**（非有效紧性/K_V/存在性抽取是反复卡死点，形式化成本高且不收敛）。
- **显式/有效版为唯一主线**；定性版最终通过 `ExplicitABC ⇒ ABCConjecture`（mainline 已交付 `Mzk1ExplicitABCWeakeningActual`）作为推论得到。

## 显式版前置清单（[ExpEst] 路线）
1. IUT I–III：`Cor312Variant`（LANA `Iut/Cor312`、`Multiradial`、`HodgeTheater`、`Frobenioid`、`EtaleTheta`、`ThetaLink`、`LogLink`、`Tower`、`Torsion`、`Anabelian`、`Reconstruction` 等）
2. IUT IV §1：`Iut4Sec1/Basic, ArithmeticDivisor, Pullback, WeightedAverage, RangeAverages, LogError`；LANA `Implication/Theorem110, LogVolumeBound`
3. IUT IV §2：`Iut/Implication/Corollary22`（构造 initial Θ-data）、`Corollary23`（Cor 2.3 ⇒ ABC，显式输入）、`Iut/Abc/{Classical,FormalConjectures,Target}`
4. GenEll 高度理论：LANA `genl`（`Genl.GeneralPosition.*`，Theorem 2.1）
5. 显式 PNT/Chebyshev：LANA `Implication/ChebyshevExplicit`（`chebyshevBoundExplicit`/`primeCountingBoundExplicit` 已从 Mathlib 证明）+ `PrimeSelection`、`Invariants`
6. 数值估计：`heights`（高度/椭圆曲线）、`padic-log-volume`（Prop 1.1）、`tate-curves-theta`（θ/Kummer）、`elliptic-curves`、`pi1`、`orbicurve-cores`、`tempered-fundamental-groups`、`oka`、`belyi`、`continuous-kummer-theory`
7. 主定理：LANA `Iut/MainTheorem.lean`（`classicalABC_of_variant : Cor312VariantHolds → ClassicalABC`）

## 仓库映射（很多已有）
- LANA 生态在仓库内：`tmp/dsh-oct6-openai-math-survey-20261016/repos/lana/`（20 个包）
- `Iut.MainTheorem` 的 import 闭包 = **1,230 个模块**：tempered-fundamental-groups 626、iut 184、oka 109、tate-curves-theta 79、orbicurve-cores 79、heights 56、belyi 37、elliptic-curves 25、pi1 13、continuous-kummer-theory 12、genl 8、padic-log-volume 2
- 已移植到本树：`tmp/sheaf/lana/<pkg>/...`（imports 改写为 `tmp.sheaf.lana.<pkg>.*`），1,046 个进入编译队列（另 184 个路径待补）；目标文件 `tmp/sheaf/lana/iut/Iut/MainTheorem.lean`

## 接线与证明步骤
1. 按依赖序编译叶子包 → 目标 `Iut.MainTheorem`（watchdog 队列，逐步 per-file 修 4.32.0→4.32.2 差异）
2. `Iut.ClassicalABC` 与我们 `ABCConjecture` 的桥（mainline）：形状对照 + 适配定理
3. `ExplicitABC ⇒ ABCConjecture`（已有）与 LANA 显式常数形式的对接
4. 显式常数：`ExpEst02` Class B（由 `chebyshevBoundExplicit`/`primeCountingBoundExplicit` 证明）
5. 3.12 条件链（step3115/R4/endgame）保留为 IUT III 骨架，不再作为定性版主攻方向