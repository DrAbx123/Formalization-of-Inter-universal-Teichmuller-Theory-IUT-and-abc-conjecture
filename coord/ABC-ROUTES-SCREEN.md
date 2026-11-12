# ABC-ROUTES-SCREEN — 能证 ABC 的路线筛查

日期：2026-11-12。作者：单线程审阅会话（只读源码，未编译，未改其它文件）。
规则（用户给定）：只收"有可能跑通到 ABC"的路线；等价改写不收；现在就看得到头的不收。
lana 路径一律指仓库根 `Iut/` 树。

## 0. 结论

按上面的规则筛完，**仓库对象内能写的路线是零条**。

- 这不是说不等式为假，也不是说它不可证。
- 说的是：原文对象里没有一条可供形式化的推导；补全任何原文对象，Step (xi) 都还是同一条数值不等式。
- 依据是 §1 的四环论证，每一环都可以单独核对；其中 E2 是我对 IUT IV 的读法，需要对照原文复核。

如果 §1 的某一环被推翻，§4 写了对应的后果。

## 1. 障碍论证（四环）

记 `A = |log q|/(2ℓ)`，`sF = ℓ(ℓ+1)/12`，`V = logVol(hull(VC(I)))`，
`R = −|log Θ|`（Θ-pilot 区域壳的 log-volume），`Box` = IUT IV Thm 1.10 Step (v) 的上界。

**E1. ABC 的装配同时需要两条。**

- (i) `−A ≤ R`（IUT III Cor 3.12）。
- (ii) `R ≤ Box`（IUT IV Thm 1.10）。
- `Box = (ℓ+5)/4·D − (ℓ+1)/24·Q + S + (ℓ+5)·T`，含负的 Q 项。
  证据：`tmp/sheaf/xif/paper/Mzk1BoxConstantAuditActual.lean` 文件头（语料 L1736–L1783），
  `LeanFormal/IUT/IUTIV/Estimates/StepVProcessionAverage` 的 `processionAverage_le`。
- 两条合起来是 `−A ≤ Box(D)`，两边都只由 D 决定。

**E2. (ii) 里的负 Q 项，只在"theta 值按本位赋值作用、不确定性保 log-shell 格"时才算得出来。**

- IUT IV Prop 1.2 的估计形如 `φ(p^λ·O) ⊆ p^{⌊λ − d − a⌋}·I`，前提是 φ 保持 log-shell 格。
- 所以任何让 (ii) 成立的对象读法，都满足 lana 的 `EtaAlg.LGPLaw`，且位移 `κ_ι = −sF·A`。
- 状态：我的读法，未在本轮重读 IUT IV 原文。**这是四环里唯一需要复核的一环。**

**E3. 在 E2 的前提下，Step (xi) 等价于数值不等式。**

- `Iut/Wall/README.md:133-137`：LGPLaw 下 `Wall ⟺ ∃ι, −A − κ_ι ≤ V`（`EtaAlg.wall_iff_of_lgpLaw`）。
- `κ_ι = −sF·A` 时即 (SS)：`(sF−1)·A ≤ V`（`wall_idAlg_iff`）。
- 壳取到 Ind2 并之后即 (Var)：`(sF−1)·A ≤ V + gap`，`gap ≥ 0`
  （`Iut/WallEquiv/Gap.lean`：`ss_iff_le_rhs_sub_gap`、`variant_iff_le_rhs`、`gap_nonneg`）。
- 多副本模型不改变这一点：Kummer 等同保 log-shell 时畸变为 0
  （`Iut/ThetaLink/Wall.lean:228 distortion_eq_zero`，`:232 wallOn_thetaRow_iff`）。

**E4. 这条数值不等式的两边是逐位局部量之和，而原文没有用到把各位绑在一起的算术约束。**

- `A` 来自 `QPilotData.logQ`（各坏位 `ord_v(q)·log p` 之和）。
- `V` 来自 `logVol_hull_vcI_eq`（各位 `hullPacket` 之和，只依赖域 `Kt`）。
- `gap` 来自 `gap_eq`（各坏素数的 Ind2 项之和）。
- 对任意独立给定的局部数据，这条不等式是假的（某一位的 `ord_v(q)` 取大即可）。
  所以证明必须用到"E 整体存在"加给局部数据的约束。
- 原文 Step (xi) 用到的整体事实只有两条，都不带这种约束：
  - 乘积公式，只进入实化 Frobenioid（`rlf_unique`、`scaling_iff`）；
  - `F_mod` 的整体单位对素条不可见（`Iut/LogLink/Thm311Rest.lean` 的 `fmodOxMu_eq_one`）。

**合起来**：补全 mono-theta 环境、κ-coric 函数、tempered Frobenioid、`G_v`、`D^⊩(D^⊢)` 之后，
能得到的是"Step (xi) 对真实对象等价于 (Var)"这条定理，得不到 (Var) 本身。

## 2. 试金石

任何新提案先过这一条，过不了就是换说法。

**全称 (Var) 推出一个公开未解决的问题。**

- 取 Frey 曲线 `(a,b,c) = (1, 3^k − 1, 3^k)`，固定 `ℓ ≥ 29`，`k` 与 `ℓ` 互素。
- `log q ≥ 2k·log 3 + 2·log M_k`，`M_k` 为 `3^k − 1` 中指数不被 ℓ 整除的奇部分。
- `V ≤ (ℓ+5)/4·log rad(3(3^k−1)) + C(ℓ)`，`gap ≤ log rad(3(3^k−1))`。
- 代入 (Var)：`rad(3^k − 1) ≥ 3^{(1/2+δ)k}`。
- 按 Silverman 1988 的论证，这推出以 3 为底的非 Wieferich 素数有无穷多个。
- 状态：我的推导，常数与可容许性条件需复核。

**同一量级的另一种说法。** `Kt = ℚ(i, E[6ℓ])` 固定时，同一 Galois 模的曲线是 `X(6ℓ)` 某个扭曲上的有理点。
(Var) 相当于给这些点一个线性于 log-判别式的高度上界，即一种很强的有效 Mordell。

**用法。** 对每个提案问一句："`3^k − 1` 不是近似完全幂"这条信息从哪一步进来？
答不出来的提案，最后一定停在同一条数值不等式上。

## 3. 十个方向的筛查

每个方向都问同一件事：不等号本应从哪里来，实际停在哪里。

| # | 方向 | 不等号本应的来源 | 停在哪里 |
|---|---|---|---|
| 1 | 论文原路：真实 η-算法 + Step (xi) | Θ-link 把 Θ-pilot 等同于 q-pilot | §1 E3：等价于数值不等式本身 |
| 2 | 放大不确定性（真实 `Aut(G_v)`、Ism、Ind3） | 并更大则 R 更大 | 保格自同构的并只把赋值下取整，每坏素数每 capsule 增益不到 `log p`；再大就破坏 E1(ii) |
| 3 | 全纯结构族 / Fargues–Fontaine 容器 | q-pilot 是族成员 | 塌缩：含 q-pilot 的 P 壳体积不小于 q-pilot 的，上箱要对 P 重证（`THREE-CHAINS-TEST.md` A896） |
| 4 | 整体截面 / Arakelov 差丛（face5） | 非零小截面则次数非负 | 秩一丛的范数和与截面无关（`deg_mul_principal`）；小整截面存在等价于目标 |
| 5 | 算术 Kodaira–Spencer / Hodge–Arakelov | 整态射给次数不等式 | 秩一态射就是乘一个整体元素，逐位赋值之和为零；Gaussian 极点在 Galois 共轭位上精确抵消（`Σ_j B₂(j/ℓ) = 1/(6ℓ)`） |
| 6 | 高秩丛的斜率 / 半稳定 | `μ(sub) ≤ μ ≤ μ(quot)` | 相关的格是 `F(T)` 的理想格，子线丛和商线丛给出的都是"判别式 ≤ 高度"方向 |
| 7 | 同源 + 整体乘性子空间（[GenEll] Lemma 3.5） | 同源下 Faltings 高度至多变 `½·log ℓ` | 有 F-有理的 H 时成立（`Iut/Tripod/CyclicBound.lean`）；真实数据里 H 只在 `ℓ+1` 次扩域上有理，那里乘性位与非乘性位的贡献精确抵消 |
| 8 | 模性 + 降级 + Ribet–Takahashi / Shimura 曲线 | 两种参数化的次数比等于 `∏ n_p` | 已知方法界的是 `∏ n_p ≤ N^{11/2+ε}`，目标是 `Σ n_p·log p ≤ 6·log N`，差一个指数 |
| 9 | 超越方法（Baker、G-函数、Runge） | 小的非零代数数有下界 | Baker 类只到指数界；Runge 条件在 K 上不满足（逼近尖点的位约 `ℓ⁴` 个，尖点约 `ℓ²/2` 个）；G-函数法需要特殊点处的非平凡整体关系，abc 点没有 |
| 10 | Bogomolov / Milnor–Wood 与 Wronskian | 拟态射亏量；导数 | `SL₂(𝔽_ℓ)`、`SL₂(ℤ_ℓ)` 上没有无界拟态射；Fermat 商不可加，没有整体的算术 Wronskian |

说明：

- 第 1–7 行是仓库对象内的方向，停点都是我推导或读源码得到的。
- 第 8–10 行需要仓库外的定理，停点是公开文献里的已知障碍。
- 所有行的共同原因是 §1 E4：局部量之和之间的不等式，只能靠整体算术约束来证，而每个方向手里的整体工具最后都只是乘积公式。

## 4. 什么会改变这个结论

1. **E2 被推翻**：有人指出 IUT IV 的上箱不依赖"本位赋值 + 保格"。
   后果：必须同时给出新的上箱推导，否则 E1(ii) 丢失，ABC 仍然装配不出来。
2. **出现一条新的整体约束**：把各坏位的 `ord_v(q)` 与分歧数据联系起来，且不是乘积公式。
   处理：先过 §2 的试金石。
3. **作者方的 Lean 骨架**（"3.11.5 ⟹ 3.12"）里，SHE / APT 有不依赖数值比较的定义。
   处理：核对这些定义对真实对象是否可证；按 E3，若可证则其中必含一条算术不等式。

## 5. 不是 ABC、但能做成定理的三件事

列在这里只为避免重复劳动，不算路线。

- "Step (xi) 对真实对象等价于 (Var)"：把 §1 的 E2–E3 在真实对象上证出来。
- Ind2 项的精确公式：`ind2Term = frac(j²·v_p(q)/(2ℓ))·log p`（我的推导，lana 标为 Open）。
- 条件 ABC：`(∀ D, Var D) → ABC`（lana `classicalABC_of_variant` 已有，缺的是本地字典）。
