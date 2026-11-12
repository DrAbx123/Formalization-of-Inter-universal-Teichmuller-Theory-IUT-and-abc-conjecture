# GenEll 形式化计划（[GenEll] = Arithmetic Elliptic Curves in General Position）

## 0. 论文与关键结果（仓库内全文）
- 论文：S. Mochizuki, **Arithmetic Elliptic Curves in General Position**, Math. J. Okayama Univ. 52 (2010) 1-28。
- corpus：`papers/motizuki_corpus/text/Arithmetic Elliptic Curves in General Position.txt`；工具论文 `Noncritical Belyi Maps.txt`（[Mzk1]）。
- 主要结果：
  - §1（行 99-604）：高度 ht_{ωX(D)}、log-diff/log-cond、BD 类（Def 1.2/1.5）、compactly bounded subsets（Ex 1.3）、Prop 1.4/1.6/1.7。
  - §2（行 606-687）：**Theorem 2.1**：(i) ABC/Efective Mordell/Vojta for all hyperbolic curves over number fields ⇔ (ii) ABC for Σ-supported compactly bounded subsets（BD 类不等式 ht ≲ (1+ε)(log-diff+log-cond)）。
  - §3（行 738-1199）：full SL2 Galois actions：Lemma 3.1（SL2 结构）, 3.2, Prop 3.4（Faltings heights）, Lemma 3.5/3.6/3.7, **Theorem 3.8**（general-position 椭圆曲线的 full special linear Galois action）。
  - §4（行 1200-1425）：Lemma 4.1（prescribed-size primes，GRH 条件）, Lemma 4.2（初等估计）, **Cor 4.3/4.4**（degenerating/compactly bounded 的 full Galois actions）。
- 与 IUT IV §2 的关系：IUT IV §2（`LeanFormal/IUT/IUTIV/Estimates/Section2.lean` 目前是 [machine-gap]）用 [GenEll] 把 IUT 的 general-position/compactly-bounded 估计推广到任意点，从而由 Thm 1.10 得 ABC。GenEll 形式化 = 关掉该 machine-gap 的 citation 层，并明确剩余输入（[Mzk1] 非临界 Belyi 存在性、Thm 3.8 的深结果）。

## 1. 既有资产（STEP 0 已做，不得重证）
- BD 类工具：`S3131BDClassCompositionActual`（IsBDLe refl/trans/add_right）、`S3136BDClassChainToolActual`（IsBDLe/IsBDEq，8 decls）。
- GenEll 形状：`S3131GenEllPaperInputActual`（CompactlyBoundedCut/GenEllEquivalenceStatement）、`S3131GenEllInputDetailedActual`（BDClass/GenEllTheorem21）、`S3131GenEllEquivalenceShapeActual`、`S3131GenEllShapeStatementsActual`、`S3131IUTIVTheoremAInputActual`（BDClassInequality）。均 CITABLE。
- 高度/权重函数层：`LeanFormal/IUT/IUTIV/Estimates/ArithmeticDivisorDegree.lean:1214 heightWeight, :1221/:1225 hTerm`；`ABCBridge/Arithmetic/RationalPointDictionary.lean`（ABC 有理点字典 Height.logHeight1 = log c）。
- GenEll 影子接口：`S3132IVGenEllShadowAdapterActual.genEll_transfer`（本仓库形状）。
- vendor 源码参考（不可 import）：`Iut/Stage1/IUTStage1IUTIVAlgebra.lean:8056 height_le_weighted_logDiff_logCond_minus_lowerBound (+:8085), :9900 genEll_transfer (+:9919 compact_subset_theoremA)`。

## 2. 阶段与文件
### P0 陈述层（首要，6-8 文件）
1. `GenEll01BasicActual`：数域 F、V(F)=V_non ⊔ V_arc、高度 ht_{ωX(D)}、logDiff_X、logCond_D、BD 类 `IsBDLe`（§1 Def 1.2/1.5 行 180-500）、Example 1.3 compactly bounded 子集、ABC 点字典对接（复用 RationalPointDictionary）。
2. `GenEll02Prop14Actual`：Prop 1.4 (Basic Properties of Heights) 精确陈述 + 初等部分（行 294-423），Remark 1.4.1。
3. `GenEll03Prop16Actual`：Prop 1.6 (Conductor Bounded by the Height) 陈述（行 505-523）。
4. `GenEll04Prop17Actual`：Prop 1.7 (Conductors and Log Differents) 陈述（行 524-604）。
5. `GenEll05Theorem21Actual`：Theorem 2.1 陈述（行 615-687）+ (i)⇒(ii) 证明（trivial）+ (ii)⇒(i) 归约骨架（列出所需：非临界 Belyi 存在性 [Mzk1]、覆盖 Y→X 构造、Prop 1.4/1.7 链）。
6. `GenEll06Section3StatementsActual`：Lemma 3.1/3.2、Rem 3.3.1、Prop 3.4、Lemma 3.5/3.6/3.7、Theorem 3.8 精确陈述（行 738-1199）。
7. `GenEll07Section4StatementsActual`：Lemma 4.1（prescribed-size primes；注明 GRH 条件）、Lemma 4.2、Cor 4.3、Cor 4.4 陈述（行 1200-1425）。
8. `GenEll08MainReductionActual`：GenEll 主归约陈述：ABC(all) ⇔ ABC(general position)，由 Thm 2.1 + Thm 3.8 + Cor 4.3/4.4 组装；给出与 IUT IV §2 的消费接口。
### P1 初等证明层（并行）
- Prop 1.4 初等部分、BD 类代数（复用现有工具）、Lemma 3.1（SL2 结构）、Lemma 4.2（初等估计）、Prop 1.6/1.7 的初等方向；每文件 checker+probe。
### P2 深输入层（分类 + 尽量形式化）
- [Mzk1] Noncritical Belyi Maps：Def 1.1/Cor 1.2/Lemmas 2.1-2.4/Thm 2.5/Cor 3.1-3.2 精确陈述与可证性分类（corpus 文本）；
- Theorem 3.8 依赖的 Faltings-height/Serre 型输入（Prop 3.4、Lemma 3.5-3.7）——先做精确 paper-input 陈述，不假装证明；
- Lemma 4.1 的 GRH 条件显式命名。
### P3 集成层
- `GenEll.Theorem21` + `MainReduction` 接入 IUT IV §2：把 `Section2.lean` 的 [machine-gap] 替换为 'IUT Thm 1.10 + GenEll reduction ⇒ ABC' 的显式条件定理；关掉 H6 GenEll transfer。

## 3. 分工
- **mainline**（lead）：P0 核心陈述 + GenEll08 组装 + P1 复用工具；协调编译。
- **abc**：§1 定义/高度/BD 类（GenEll01-04）+ Prop 1.4/1.6/1.7 陈述与初等证明；对接 ArithmeticDivisorDegree/RationalPointDictionary。
- **stage4**：[Mzk1] 形式化（P2）+ §3/§4 陈述（GenEll06/07）+ Thm 3.8/Cor 4.3/4.4 的输入分类。
- **lattice**：statement ledger/INDEX/citation 行 + 数据文件；与 PRIOR-ART-INDEX 同步。
- **stepxi**：P3 集成（IUT IV §2 consumer）+ route 接口。
- **shehdd**：checker/audit/watch（每批验证 CITABLE + 声明列表）。

## 4. 纪律
- 文件名 `tmp/sheaf/xif/paper/GenEll<NN><Name>Actual.lean`，namespace `LeanFormal.IUT.XiFPaper.GenEll...`；每文件 checker+probe；每批 6-8 文件，一次短等。
- 每批报告第一行 `STEP 0 prior-art: ...`；新先例追加 `coord/PRIOR-ART-INDEX.md`；
- 不重证仓库已有结果；论文已证但不打算形式化的部分，必须登记为**精确命名的 paper-input 定理**（corpus 行号 + 状态），不假装证明。
- registry frozen 14041；不做中间 reopen，只有论文级定理（GenEll 陈述层完成、Thm 2.1 归约、P3 集成等里程碑）才考虑一次更新。
