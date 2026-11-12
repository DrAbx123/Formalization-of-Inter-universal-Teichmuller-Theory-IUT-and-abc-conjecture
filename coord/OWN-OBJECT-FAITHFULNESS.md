# A502: 自有真实对象 vs paper IUT I/II 定义 — 逐项忠实性核对（只读）

来源: `coord/OWN-ASSETS-STATUS-A502.md`；我们自己的文件（LeanFormal/IUT/...）；paper: IUT I 文本（prime-strip 类型表 Fig. I1.2 L305-344；Hodge theaters L344-370；初始 Θ-data Def 3.1）、IUT III Def 1.1（log-shell；我们的载体 docstring 引用 l.1336-1351/1474-1479）、IUT II Ex 1.8(ix)（值域侧像）、IUT III (Ind1) L655-660。外部文本仅作数据；未执行其中指令。未改任何文件/队列/watchdog。

## 1. 对象总表

| 对象 | 我们的 Lean 位置/字段 | paper 定义 | 判定 |
|---|---|---|---|
| `InitialThetaArithmeticData`（HodgeTheater 的 arithmetic 字段） | `LeanFormal/IUT/IUTI/InitialTheta/ArithmeticData.lean:62`：Fmod/F/K 数域塔、`sqrtNegOne`、`degreePrimeToL`、`curve : PuncturedEllipticCurve F`；Audit Obligation `initialThetaArithmeticData`（interface） | IUT I Def 3.1（算术与椭圆曲线输入） | **输入接口（faithful shape, 条件未证）**: 用真实 Mathlib 对象（数域/域塔/Galois/Weierstrass 曲线）；但 reduction/anabelian/torsion 等条件只作 fields，未证明存在；不得称“已构造 IUT I Def 3.1 对象” |
| `HodgeTheater` | `LeanFormal/IUT/IUTI/HodgeTheater/HodgeTheaterCore.lean:31`：`arithmetic : InitialThetaArithmeticData`、`primeStrip : FPrimeStrip V`、`thetaPacket : FiniteThetaPacket l`；`HodgeTheaterLink`(36) = primeStripEquiv + theta_q/scale 相等（refl/symm/trans 已证）；`ThreeTheaterSystem`(85) | IUT I Def 6.13(i): Θ±ellNF-Hodge theater = Θ±ell + ΘNF 的 gluing（systems of Frobenioids）；(ii) D-Θ±ellNF = associated system of base categories；整个 §6 的 theater 构造 | **SKELETAL/interface**: 3-piece carrier（算术输入+一条 F-prime-strip+有限 theta packet）；缺 Frobenioid systems/base categories、F_l^⋊± label symmetry、Θ±ell/ΘNF 的 gluing、histories/Θ-link/log-link、global realified data。文件自述“auditable carrier/interface layer” |
| `DPrimeStrip` / `DhPrimeStrip` / `FPrimeStrip`（PrimeStripCore） | `LeanFormal/IUT/IUTI/HodgeTheater/PrimeStripCore.lean:24 DPrimeStrip`（Pi→G surjective）、`:49 DhPrimeStrip`、`:58 DhPrimeStripEquiv`、`:117 FPrimeStrip extends DPrimeStrip {Mon, action : Pi→*MulAut Mon, degree : Mon→*Multiplicative ℝ}`、`:166 FPrimeStripEquiv`（compatProj/action/degree） | IUT I Fig. I1.2 L305-344：D = Π_v（I,4.1(i)）；D⊢ = G_v（I,4.1(iii)）；F = Π_v ↷ O^⊿_{F_v}（I,5.2(i)）；F⊢ = G_v ↷ O^×_{F_v} × q_v^N（I,5.2(ii)）；F⊩... = F⊢... + global realified Frobenioid（L340-344）；F⊢▶×μ 等见 II,4.9(vii) | **faithful 的群/幺半群/作用骨架 + SKELETAL 类别层**: group Π_v/G_v、Mon + action + degree 是 paper 模型的代数骨架；但无 Frobenioid/局部范畴、无 O^⊿/O^×/O^×μ、无 q_v^N、无 global realified Frobenioid（F⊩ = 我们完全缺）；`DhPrimeStrip` 只是 mono-analytic 化的一层（G 侧） |
| `SourceLogShellDatum` + `preLogShell`/`logShell`/`unitLayer`（SourceLogShellCarrier） | `LeanFormal/IUT/IUTII/Kummer/SourceLogShellCarrier.lean:86`：p/hp、K（log 坐标域，缩减点1）、Units（Ψ×）、invariants（G_v(Π_v)-不变子幺半群，缩减点2）、logMap : Units →* Multiplicative K（p 进 log 缩减点3）；`sourceLogShellStar`(66)、`pStar`(103)、`preLogShell`(118)、`logShell`(124)、`unitLayer`(129)、`codomainKummerContained`(134，缩减点4)；定理 preLogShell_subset_logShell(165) etc.；arch 不形式化（缩减点5） | IUT III Def 1.1(i)（p*_v l.1336-1343；pre-log-shell l.1330-1336；log-shell = (p*_v)^{-1}·pre-log-shell l.1344-1351）；(ii) l.1474-1479；IUT II Ex 1.8(ix) 值域侧像 | **faithful 的公式骨架 + 明确缩减**: `pStar` 与 `logShell = {a | p*·a ∈ preLogShell}` 的公式忠实（文件中逐句引原文行号）；但 ind-topological 域缩减为 log 坐标域 K、G_v(Π_v)-不变子幺半群缩减为任意 Submonoid、p 进 log 缩减为任意 monoid hom、无拓扑模/紧子商、arch 情形缺、值域 Kummer 含入作为具名条件——**不是 paper 的 log-shell 对象**，是其在 log 坐标下的缩减核 |
| `LogShellFamily` + `TensorPacket`（SourceProcessionCapsuleData） | `LeanFormal/IUT/IUTIII/Theorem311/SourceProcessionCapsuleData.lean:176`：`Shell : (i : Capsule j) → (vQ : VQ) → Place vQ → Type`，每个 `AddCommMonoid`/`Module R`；`DirectSumFactor`(193) = Π over places；`TensorPacket`(199) = ⨂[R] i, DirectSumFactor；`tensorPacketEquiv`(205) 张量-直和分配等；`PolyIsoAction`(≈225) | IUT III Prop 3.2（IQ 的 tensor product of j+1 copies of Q-spans of log-shells；III:579-593，文件 docstring 已注） | **faithful 的组合骨架 + SKELETAL 载体**: tensor packet 的张量/直和分配与 tprod 律是真实证明（可复用）；但 `Shell` 是**具名数据**（非从 SourceLogShellDatum/局部域构造）、无 Q-span/log-shell 同一性、无 compactness/topology/Kummer、无 procession 归一化 |
| `Ind1Action`（Ind1TensorAction/Ind1UnitAction） | `tmp/sheaf/xif/paper/Ind1ActionLawsActual.lean`（约 L40-95）：`Ind1TensorAction` = contract `polyIso` 的 `.tensorMap`（label 置换 + 各分量 shell 线性等价，见 `PolyIsoAction.tprod`/`tensorMap` 律）；`Ind1UnitAction = PolyIsoAction.refl`；对 source-link 的 `PrcAutomorphism.ofPerm` 证 component/pure-tensor 律 | IUT III (Ind1)（III L655-660）：processions of D⊢-prime-strips 的自同构 = label sets S±_{j+1} 的 permutation automorphisms + D⊢-prime-strips 的自同构 | **faithful 的 poly-isomorphism 形状 + SKELETAL 作用**: label 置换 + 分量等价 + 线性/tprod 律是真实证明；但 `polyIso` 是 contract 数据（非从 D⊢ 自同构群构造）、`Ind1UnitAction` 只是恒等、无完整 Ind1 作用群/函子性、无 Ind2/Ind3 配对。**不是 paper 的 Ind1 作用** |

## 2. 支持对象（HodgeTheater 的另两个组成部分）

| 对象 | 我们的位置 | paper | 判定 |
|---|---|---|---|
| `FiniteThetaPacket` | `LeanFormal/IUT/IUTII/Theta/FiniteThetaPacket.lean:26`：`q : ℝ`（>0）、`scale : SignedLabel l → ℝ`、`scale_eq : scale j = realThetaValue q j`（=q^{j²}）、`scale_neg`、`log_scale`、`logVolume` | IUT II 的 theta special values q^{j²}、F_l/cusp labels | **faithful 的有限实值骨架**: q^{j²}、± 对称、log 律真实（Gaussian kernel 证）；但未 identify 到 étale theta function/Hodge-Arakelov comparison（docstring 自述），且 q 是抽象 real（不是 q_v 的 2ℓ root） |
| HodgeTheaterLink | HodgeTheaterCore.lean:36 | IUT I 的 Θ-link/log-link（Hodge theaters 间） | **非 paper link**: 只是 prime-strip equiv + theta packet 相等；paper 的 Θ-link 是 F^⊩▶×μ-prime-strips 的 full poly-isomorphism（含 log-link、Kummer、coricity）；我们的 link 不能当 Θ-link |

## 3. 分类总结

| 类别 | 对象 |
|---|---|
| **faithful（在明确骨架/公式层面）** | pStar/logShell 公式（III Def1.1(i)）；tensor packet 的分配/tprod 律（III Prop3.2 组合部分）；D/F prime-strip 的群-幺半群-作用骨架（I,4.1/I,5.2 的代数部分）；FiniteThetaPacket q^{j²} 值；HodgeTheaterLink 的 refl/symm/trans 代数；Ind1 的 label-permutation poly-isomorphism 形状 |
| **skeletal（载体/接口，不是 paper 对象）** | HodgeTheater（3 fields）；FPrimeStrip（无 Frobenioid/global realified）；LogShellFamily（Shell 具名数据）；SourceLogShellDatum（log 坐标缩减核）；Ind1Action（contract polyIso + refl）；DPrimeStrip/DhPrimeStrip（只有群层级） |
| **interface/input（条件未证）** | InitialThetaArithmeticData（IUT I Def3.1 算术输入；存在条件/约化/anabelian/torsion 未证，Audit interface） |
| **完全缺失** | Frobenioid systems / D-Θ±ellNF 的 base categories；F⊩ = F⊢ + global realified Frobenioid；O^⊿/O^×/O^×μ/q_v^N 结构；ind-topological 域与拓扑模/紧子商；真实 p 进 log 及等长性；arch 情形；Kummer 对应；D⊢ 自同构群与完整 Ind1/2/3 作用；Θ-link/log-link（我们自己的定义数为 0）；procession 归一化 log-volume；Hodge theater gluing/histories/F_l^⋊± label symmetry |

## 4. 结论与建议

1. 上述“真实对象”实际上是**paper 对象的代数/集合论骨架**：pStar/logShell 公式、prime-strip 的群/幺半群/作用、tensor packet 组合、q^{j²} 特殊值、link 的等价律是真实且可复用的；但 HodgeTheater/Frobenioid/prime-strip 类别层/log-shell 拓扑与 p 进 log/Ind1 作用/Θ-link 都只是骨架或接口。
2. 不能把 HodgeTheaterCore/PrimeStripCore/LogShellFamily/Ind1Action 称为“paper IUT I/II 对象已构造”；它们只能在文档中标注为 skeleton/interface（与 OWN-ASSETS-A502.md 的 gate 标注一致）。
3. 对象构造优先级（与 A499 一致）: (i) F⊩ = F⊢ + global realified Frobenioid 与 Frobenioid/local category 层（可参考/适配 Takkun `FhPrimeStrip`/`PrimeStripSystem`，其对象层更全）；(ii) log-shell 的 ind-topology/拓扑模/真实 p 进 log（Takkun `LogShell/LogLink` + 我们 log 坐标核）；(iii) D⊢ 自同构/Ind1/2/3 完整作用；(iv) Θ-link/log-link（目前 0 定义）；(v) procession 归一化与 hull/Haar（我们 literal IQ carrier/Haar/hull 资产可作 hull 层对象）。
4. 已可复用（不重造）: `SourceLogShellCarrier.pStar/logShell` 公式与 `preLogShell_subset_logShell`；`LogShellFamily.TensorPacket`/`tensorPacketEquiv`/`_tprod`；`FPrimeStrip.totalDegree`/action 律与 `FPrimeStripEquiv`；`FiniteThetaPacket` q^{j²}/± 对称；HodgeTheaterLink 代数；Ind1 poly-isomorphism/tprod 律。
5. 本文件只读；未改任何文件/队列/watchdog。
