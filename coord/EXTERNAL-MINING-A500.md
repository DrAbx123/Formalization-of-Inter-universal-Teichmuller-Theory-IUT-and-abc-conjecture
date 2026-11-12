# A500 外部挖掘：仓库内的完整 IUT 形式化对象层（范围扩大后的发现）

## 之前搜索范围过小，实际仓库内至少有 4 个 IUT 形式化项目
1. `tmp/external/Takkun-IUT_LEAN`（68 文件、37 模块）：**完整逻辑骨架 + 对象层**：InitialThetaData/Anabelian/Theta/HodgeTheater/LogTheta(Lattice,LogShell,Indeterminacy)/Multiradial(MainTheorem,Cor312,Thm311)/Diophantine(Thm110,Cor22,Szpiro,PrimeCounting)/Padic。Ledger 声称无 sorry/axiom；其 `REQUEST_theta_hull_derivation.md` 明确：整条链归约到 **一个输入 (P)**（IUT IV Thm1.10 Step (v) 的 θ-包体积比较 Step：标签→测度），并给出等价形式 `L ≥ (l(l+1)/12−1)·|log q|`。
2. `tmp/external/promachina-iut-lean-latest`（200 文件、1 处代码 sorry）+ `promachina-iut-lean`（152 文件）：Stage1 实验 + Foundations，含 `Source*` 大量真实构造。
3. `tmp/external/Takkun-IUT_LEAN` 之外还有 `tmp/external/iut4-sec1`（IUT IV §1 blueprint + Lean）、`PriestAmbrose-IUT-Corollary3_12-Lean`。
4. 我们自己的 `Iut/`（根目录 256 文件、0 sorry）只有 Foundations（anabelian/源层）。

## 已执行
- 把 Takkun 68 文件移植到 `tmp/sheaf/takkun/IutLean/...`（import 改写），入队（队列 540）。这是**对象层来源**，先编译，后按对象适配。

## 重要说明（不盲信）
- Takkun 项目的 `REQUEST` 是其作者的**结论/立场**（认为 (P) 未被推导）；我们只采纳其**对象定义与已验证引理**，其结论作为待审计数据，不能代替我们的证明。
- 任何采纳的对象都要过保真审计（是否 faithful、是否 skeletal、是否过强/过弱）。

## 对象映射（Takkun → 我们的 O1–O12）
- O1 q-pilot：`Diophantine/Thm110`、`Padic/LogVolume`、`Frobenius/PrimeStrip*`
- O2 Θ-pilot：`Theta/ThetaValues`、`Theta/MonoTheta`、`Theta/ThetaGroup`、`LogTheta/LogKummer`
- O3 multiradial rep：`Multiradial/MainTheorem`、`LogTheta/Lattice`、`HodgeTheater/Defs`
- O4 dsc/Ind：`LogTheta/Indeterminacy`、`Multiradial/Thm311`
- O5 etHT：`Theta/*`、`Cyclotome/Kummer`、`Cohomology/*`
- O6 hull/det：`Padic/LogShellRadius`、`Padic/LogVolume`、`Multiradial/Cor312`、`ThetaHullDichotomy`
- O7 SHE/HDD：`Multiradial/TwoSidedLink`、`HodgeTheater/Symmetry`、`Multiradial/Cor312`
- O12 比较：`Multiradial/Cor312` + `REQUEST` 的 (P)（我们的 hcomp 同名缺口）

## 下一步
1. 编译移植模块（watchdog，非 priority）；修 4.31→4.32 API 差异
2. 按对象映射审计 Takkun 定义 vs paper 定义（lattice/shehdd）
3. 提取 Takkun 已验证的 (xi-d)-(xi-f) containment 与 ledger/Diophantine 引理，接到我们的对象层
4. (P)/hcomp 仍为唯一 named 真缺口；尝试用我们/literal HullDet + Takkun 的 containment 证明它