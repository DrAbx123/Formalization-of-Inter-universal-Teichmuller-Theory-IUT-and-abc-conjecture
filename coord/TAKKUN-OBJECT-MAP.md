# TAKKUN OBJECT MAP（A500）— `tmp/sheaf/takkun/IutLean` → O1–O12

来源：外部 Takkun-IUT_LEAN 移植（540 模块入队）。只采纳**对象定义/已验证引理**；其结论（含 REQUEST 的 (P)）仅作待审计数据。

## O1–O12 编号（沿用 `coord/OBJECTS-3115-312-A498.md`）

O1 BPS/value-pilot 对象；O2 multiradial algorithm（Steps 1–9 环境）；O3 mlt representation（Hodge theater/log-shell/tensor packets/Θ-pilot）；O4 dsc + Ind1/2/3；O5 etHT；O6 0-column/etHT transport；O7 hull；O8 det；O9 Holomorphic hull；O10 HDD 分解；O11 SHE；O12 q/Θ 比较（Cor 3.12）。

## 对象映射表

| Takkun file:decl | O 编号 | 定义内容（逐字摘要） | faithful / 骨架 |
|---|---|---|---|
| `LogTheta/LogShell.lean:24` `structure LogShell`（`carrier : Type u`, `[AddCommGroup carrier]`） | **O3**（object (a) 对数殻） | 仅记录加法群载体；注释声明「I_v ⊆ (k)+，I_v⊗_ℤℚ=(k)+，含 (O_Fv)+」，但字段中没有范畴/整结构/紧性/体积数据 | **骨架**（载体骨架） |
| `LogTheta/LogShell.lean:33` `structure LogLink (U) [CommGroup U] (S : LogShell)`（`logMap : Additive U →+ S.carrier`） | **O2**（log-link/纵向 link；亦与 O5 log-Kummer 相关） | 乘法单位群 → 加法对数殻的加法同态；`logMap_one : log 1 = 0`、`logMap_mul : log(a·b)=log a+log b`（真实定理） | **结构性定义**（对 log-link 的真实抽象；不含正則結構依賴） |
| `LogTheta/LogShell.lean` `structure LogChain`（`shell : ℤ → LogShell`, `unit : ℤ → Type`, `logLink : ∀ m, LogLink (unit m) (shell (m+1))`） | **O2**（Steps 1–9 的纵向链） | log-theta-lattice 纵向骨架（log : O×µ_m → I_{m+1}） | **骨架**（无链接相容/可换性数据） |
| `LogTheta/Lattice.lean:23` `structure LogThetaLattice`（`HT : ℤ × ℤ → Full`） | **O2**（Steps 1–9 环境）；亦触及 O6（0-column=`n=0` 列） | ℤ×ℤ 的 Θ±ellNF Hodge theater 网格；`thetaColumn n := fun m => HT (n,m)`、`logRow m := fun n => HT (n,m)`（rfl 引理） | **骨架**（无 Θ-link/log-link 相容与不交换性证明；注释只说「本质重要」） |
| `LogTheta/Indeterminacy.lean:29` `def UpperSemiCompatibility (Γ) [Group Γ] (I) [MulAction Γ I] : Prop := ∀ x g, g • x ∈ MulAction.orbit Γ x` | **O4**（Ind3）/O2 | 把「(Ind3) 上半両立性」形式化为轨道成员；`upperSemiCompatibility` 由 `MulAction.mem_orbit` **恒真** | **骨架/弱**（注释自认是轨道模型近似；不能当 paper Ind3 内容） |
| `LogTheta/Indeterminacy.lean:44` `structure LogShellIndeterminacy`（`Γ : Type`, `[Group Γ]`, `I : Type`, `[MulAction Γ I]`, `ind3 : UpperSemiCompatibility Γ I`） | **O4** | (Ind1)×(Ind2) 生成群 Γ 对对数殻 I 的作用 + Ind3 | **骨架**（群/作用为参数，无 Aut(G_v)/I^sm 构造） |
| `:57` `def multiradialOutput (x : D.I) : Set D.I := MulAction.orbit D.Γ x` | **O3**（多radial 输出的轨道模型） | 多radial 输出 = Γ-轨道 | **骨架**（orbit 定义真实，但未证明与 paper object (a) 的关系） |
| `HodgeTheater/Defs.lean:36` `structure AdditiveHodgeTheater`（`l`, `[Fact l.Prime]`, `5 ≤ l`, `primeStrips : PrimeStripSystem l`） | **O3**（D-Θ±ell Hodge theater） + **O5**（加法的/étale 部分） | 素数 l + 具体素点縞系（PrimeStripSystem） | **真实数据骨架**（primeStrips 为具体结构；缺 ell/Θ 数据与 Hodge-Arakelov 层） |
| `:49` `structure MultiplicativeHodgeTheater`（同上） | **O3** + **O5**（乘法的/数論的） | 同上 | 同上 |
| `:63` `structure Full`（`add`, `mul`, `glue : add.l = mul.l`） | **O3**（Θ±ellNF Hodge theater）；O2 lattice 节点类型 | 贴合的完整 Hodge theater；`l`/`l_ge_five`/`addSymmetry=GeoSym l`/`mulSymmetry=LabCusp l` 与两个**单純推移性**（复用 `Symmetry.lean` 真实证明） | **真实数据骨架**（贴合的仅是 l 相等；无 D-/D^>/D_< 分层、ellNF 主体、Θ±ell 与 ΘNF 的实质 glue 数据） |
| `HodgeTheater/PrimeStripData.lean:38` `structure PrimeStripSystem (l) [Fact l.Prime]`（`V`、`addSystem : LabeledPrimeStripSystem V (LabCuspPM l) (GeoSym l)`、`mulSystem`、`gaussian : GaussianPrimeStrip`、`glue`、`nondegenerate`） | **O1**（prime-strip 输入）/O3 | 加/乘标签化素点縞系 + Gaussian 縞（θ 值 q_v^{j²}）+ 单解析核贴合 + 非退化性 | **忠实度较高**（Takkun 中最实质的 Hodge theater 数据；仍是抽象 `DPrimeStrip` 层，非具体曲线构造） |
| `PrimeStripData.lean:~?` `theta_symmetric`、`kummer`（Gaussian 縞的 Kummer 円分指標） | **O5**（etHT/Kummer 类）/O12 前置 | θ 值 ±1 对称性与 Kummer 円分指標（从 Gaussian 縞自动得到，真实证明） | **真实引理**（有价值，可使用） |
| `Frobenioid/PrimeStripSystem.lean:159` `structure DhPrimeStrip`（`G : V → Type`, `[Group]`） | **O1/O3**（mono-analytic core D⊢） | 每素点绝对 Galois 群；`DPrimeStrip.toDh` 遗忘 Π | **真实结构定义** |
| `:203` `structure FhPrimeStrip extends DhPrimeStrip`（`Mon`, `action : G_v →* MulAut Mon_v`） | **O1/O3**（F⊢-prime-strip，Θ-link 的载体） | 局部单项式 + Galois 作用 | **真实结构定义** |
| `:214` `structure FhPrimeStripEquiv`（`isoG`, `isoMon`, `compat` 同变性）及 refl/symm/trans | **O1/O3**（Θ-link poly-同型骨架） | 同变同构 | **真实定义+证明** |
| `:309` `structure GaussianPrimeStrip extends FhPrimeStrip`（`qParam : ∀ v, Mon v`）；`thetaValueAt v j := gaussianValue (qParam v) j`；`thetaValueAt_neg/zero` | **O3/O5**（θ 值 q_v^{j²} 的入れ物） | Gaussian 縞 + q 参数 + θ 值 ± 对称 | **真实定义+证明**（θ 值层可用） |
| `:337` `structure ThetaChain`（`core : ℤ → DhPrimeStrip`、相邻 Θ-link） | **O2/O6**（横方向 Θ-link 链） | Θ-link 链的 mono-analytic core 族 | **骨架**（core 族+link 数据；无兼容/复合证明） |
| `:449` `structure LabeledPrimeStripSystem (V L Sym) [Group Sym] [MulAction Sym L]`（`strip : L → DPrimeStrip`, `symIso`） | **O1/O3**（label 管理的素点縞系） | 对称化同型骨架 | **真实定义** |
| `:457` `constantLabeledSystem` | 非空 witness | 所有 label 同一 DPrimeStrip、symIso=refl | witness（弱） |

## 结论（faithful 判定）

1. **可采纳的真实定义/引理**：`DhPrimeStrip`/`FhPrimeStrip`/`FhPrimeStripEquiv`（+refl/symm/trans）、`GaussianPrimeStrip`（qParam/thetaValueAt/thetaValueAt_neg/thetaValueAt_zero）、`LabeledPrimeStripSystem`、`PrimeStripSystem`（addSystem/mulSystem/gaussian/glue/nondegenerate）、`Full`（在 PrimeStripSystem 之上的 Θ±ellNF 贴合数据）、`LogShell`/`LogLink`/`LogChain`/`LogThetaLattice`、`Symmetry` 的单純推移性、θ 值 ± 对称与 Kummer 円分指標。
2. **仅骨架/不可当 paper 内容**：`UpperSemiCompatibility`（orbit 恒真）、`multiradialOutput`=orbit（未连 paper object (a)）、`LogShell` 的「compact/log/units」字段缺失、`LogThetaLattice`/`ThetaChain`/`LogChain` 的 link 相容性、`Full` 的 D-/D^>/D_< 与 ellNF 主体、Ind1/2/3 的具体构造（Aut(G_v)/I^sm/upper-semi log-Kummer）。
3. **与 O1–O12 的缺口**：O1（BPS=value/pilot 对象）Takkun **未覆盖**；O4 的 Ind1/2/3 只有轨道模型（不含 Aut(G_v)/I^sm 构造）；O7/O8/O9（hull/det/holomorphic hull）Takkun **未覆盖**（我们自己的 `HolomorphicHull` 树更全）；O10/O11/O12 未覆盖。
4. **诚实边界**：Takkun `Full`/`PrimeStripSystem` 是「抽象素点縞骨架 + 具体标签/θ 值」，不是具体曲线/数域构造；其 `IsTrivial`/`trivialAlg`（Checks）类实例不得用于证明 wall/variant。

## 先适配的 1–2 个对象（已选）

**适配对象：`FhPrimeStrip`（含 `FhPrimeStripEquiv`）** —— 我们 `IUTI/HodgeTheater/PrimeStripCore.lean` 的 `FPrimeStrip`（含 Pi/proj/degree）→ Takkun `FhPrimeStrip`（G/Mon/action）的遗忘适配 + 同构适配：
- `takkunFhOfOur : FPrimeStrip V → IUT.Frobenioid.FhPrimeStrip V`（`G := F.G`, `Mon := F.Mon`, `action := F.action`）；
- `takkunFhEquivOfOur : FPrimeStripEquiv F F' → IUT.Frobenioid.FhPrimeStripEquiv (takkunFhOfOur F) (takkunFhOfOur F')`（`isoG`, `isoMon`, `compat` 由我们的同构字段给出）。
实现文件：`tmp/sheaf/xif/paper/Mzk1TakkunPrimeStripAdapterActual.lean`（import 我们的 `PrimeStripCore` + Takkun `Frobenioid/PrimeStripSystem`，真实 Lean，无 sorry）。