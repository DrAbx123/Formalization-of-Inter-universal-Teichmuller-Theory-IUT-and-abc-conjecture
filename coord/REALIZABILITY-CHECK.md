# REALIZABILITY-CHECK：`e=1, r/n=1` 与 p=2 漏洞的核查

日期：2026-11-12（A800/A804，stage4 部分；**无 Lean 文件改动**，新增 `Mzk1P2DeficitActual.lean`）。

## 0. 结论（先给）

1. 按项目自己的 r 定义（`coord/ROUTES-FINAL-GAP.md` §6.1：**`p^r` = 域内 p 幂单位根个数**，
   即 r = log_p #μ_{p^∞}），`Q_2` 有 #μ_{2^∞}={±1}=2=2^1 ⇒ **r=1**，
   `logMuPaper(2,1,1,1) = (1+1−1−1)·log 2 = 0`，**不是 −log 2**。
   ⇒ A804 的 p=2 "漏洞" 是元素个数误读；**p=2 不构成忠实反例**。
2. 同一约定下，`e=1 ∧ r/n=1`：奇 p 时 e=1 ⇒ r=0；p=2 时 e=1 ⇒ r=1（#μ=2），
   `r/n=1` 需 n=1（K=Q_2），但系数为 0；**不是 −1**。
3. 加 ζ_l（l≥5）Θ-data 约束后：p≠l 且 e=1 ⇒ n≥ord_l(p)≥2 ⇒ p=2,n=1 也被排除。
4. 独立矛盾：θ 恒等式 `sumTheta = c_lana·A`（green），`c_lana>0`、`ssCoeff>0`；
   `ssCoeff·A=1 ⇒ sumTheta>0`，与 witness 的 `sumTheta=0` 矛盾。

## 1. r 的定义与核对表

引用（`coord/ROUTES-FINAL-GAP.md` §6.1 第 71 行）：

> `vol(log O^×) = 1/(q_k·p^r)`，其中 `q_k = p^f` 是剩余域大小，**`p^r` 是域内 p 幂单位根的个数**。

| 域 | #μ_{p^∞} | r | e | n | r/n | logMuPaper 系数 | logMuPaper |
|---|---|---|---|---|---|---|---|
| Q_p（p 奇，未分歧） | 1 | 0 | 1 | 1 | 0 | 0 | 0 |
| Q_p(ζ_p)（p 奇） | p | 1 | p−1 | p−1 | 1/(p−1) | 1−2/(p−1) | (p−3)/(p−1)·log p |
| Q_2 | 2 | 1 | 1 | 1 | 1 | **0** | **0** |

⇒ A804 的 "±1 共 2 个 ⇒ r=2" 与项目定义不符；若按元素个数约定，则 Q_p(ζ_p) 会给 r=p，
与项目模型 r=1 冲突（`Mzk1DiffNonnegActual` 头注释、`Mzk1PaperNormMuActual` 注释均用 r=1）。

## 2. 数值枚举（A800 要求域）

域：p∈{2,3,5}, n≤6, e|n, r∈[0,6]（放宽）⇒ **294** 个 (p,n,e,r) 元组。

| 统计（按项目 r 约定可实现性） | 数值 |
|---|---|
| 可实现元组（奇 p: r≥1 ⇒ φ(p^r)|e；p=2: r=0 不可能, r=1 无约束, r≥2 ⇒ 2^{r−1}|e） | **55** |
| 其中 `e=1 ∧ r=n` | **1** 个：(p,n,e,r)=(2,1,1,1)（系数=0） |
| 系数 `1+[p=2]−1/e−r/n` 最小值 | **0**（无 ≤ −1） |
| 加 ζ_5 约束（p=2,3 ⇒ n≥ord_5(p)=4；p=5 ⇒ e≥4）后可实现 | 32，其中 e=1∧r=n **0** 个 |

原始（无算术约束）`e=1∧r=n` 有 18 个（n=1..6 各行），但绝大多数不满足根塔整除约束：
奇 p 的 e=1 未分歧不含 p 幂根（r=0），p=2 的 r≥2 需 2^{r−1}|e。

## 3. 算术约束推导（排除定理形状）

- **T1**：奇 p，e=1（未分歧）⇒ K 不含 p 幂单位根 ⇒ r=0。
  （Q_p(ζ_p)/Q_p 全分歧 e=p−1≥2，不能嵌入未分歧扩张。）
- **T2**：若 μ_{p^r} ⊆ K，则 φ(p^r)=p^{r−1}(p−1) | e（奇 p；p=2 时 r≥2 ⇒ 2^{r−1}|e；r=1 无约束）。
- **T3**：可实现元组上系数 ≥0。奇 p: r=0 ⇒ 1−1/e≥0；r≥1 ⇒ 1/e+r/n ≤ (1+r)/φ(p^r) ≤ 1。
  p=2: 系数 = 2−1/e−1/n ≥ 0，等号仅 (e,n)=(1,1)（K=Q_2）此时系数=0。
- **T4**（ζ_l，l≥5）：若 ζ_l ∈ K_v：p≠l ⇒ f≥ord_l(p)≥2，故 e=1 ⇒ n=e·f≥2（排除 p=2,n=1）；
  p=l ⇒ e≥l−1≥4。⇒ `e=1 ∧ r/n=1` 完全不可实现。
- **T5**（θ 恒等式）：`sumTheta=c_lana·A`，`c_lana=(sFactor(nC)−1)/(2l)>0`（nC≥2），
  `ssCoeff=(l+1)/24−1/(2l)>0`（l≥5）；`ssCoeff·A=1 ⇒ A>0 ⇒ sumTheta>0`，与 `sumTheta=0` 矛盾。

## 4. A804：p=2 是不是漏洞？

**不是**（按项目定义）。`Q_2`: e=1,f=1,n=1,#μ_{2^∞}=2 ⇒ r=1 ⇒ logMuPaper=0。
负值 −log2 只在元素个数约定（r=2）下出现，而该约定与 Q_p(ζ_p) 的 r=1 模型及 ROUTES 公式冲突。

**已形式化**：`tmp/sheaf/xif/paper/Mzk1P2DeficitActual.lean`（单文件 `lake env lean` EXIT=0，
gate trio `[propext, Classical.choice, Quot.sound]`，olean 已生成、`extras_add` 已注册）：

- `logMuPaper_2_r1_eq_zero : logMuPaper 2 1 1 1 = 0`（项目约定）；
- `logMuPaper_2_r2_eq_neg_log2 : logMuPaper 2 1 2 1 = -log 2`（元素个数约定算术事实，仅记录）；
- `deficit_pos_of_p2_r2 : 0 < paperNormDeficit 1 1 (-log 2) 0`（=1+log2>0，仅该约定）；
- `deficit_nonpos_of_p2_r1`（项目约定：sumLogMu=0、sumTheta>1 ⇒ deficit<0）；
- `logMuPaper_2_faithful_nonneg : 0 ≤ logMuPaper 2 e 1 n`（e,n≥1）。

**最小参数组合（仅元素个数约定下）**：`ssCoeff·A=1`、sumTheta=0、一个 p=2 位（e=1,r=2,n=1）
⇒ deficit=1+log2>0；若 sumTheta>0，需 k≥2 个 2 分裂完全位抵消：deficit = 1 − k·log2 − sumTheta。

## 5. 最终判定

- **按项目 r 定义（p^r = #μ）**：`e=1∧r/n=1` 不可实现；p=2 给 0 贡献；`deficit=1+log p` 正例
  （A798 的纯代数 witness）在忠实模型不可实现 ⇒ **3.12 未被此 route 反驳**。
- **若把 r 改成元素个数**：Q_2（r=2）与 Q_3(ζ_3)（r=3,e=2,n=2）可实现系数 −1 ⇒ 反例；
  但这会同时改变 Q_p(ζ_p) 的归一化（r=p），与 ROUTES 公式不一致。
⇒ **决定性待确认项：r 约定**（本文件给出项目文件依据：log_p 约定）。建议 abc/lattice 复核论文
  定义并给出 green 引用；若确认 log_p，则本路线关闭，3.12 一致性保留。

## 6. 复现/引用

- 枚举逻辑：p∈{2,3,5}, n≤6, e|n, r∈[0,6]，294 元组；可实现性谓词见 §3 T1/T2；
- green 引用：`Mzk1PaperNormMuActual.paperMuCoeff/logMuPaper`、`Mzk1PaperNormThetaActual.thetaSumPaper_eq_clana_mul`、
  `Mzk1DifferentDictionaryActual.torsionConstant/diffPaperPerPlace_eq`、`Mzk1DiffNonnegActual` 头注释（Q_p(ζ_p) r=1）；
- `coord/ROUTES-FINAL-GAP.md` §6.1 L71（r 定义）；
- 新 Lean 文件：`tmp/sheaf/xif/paper/Mzk1P2DeficitActual.lean`（EXIT=0）。

---

## 10. A805：两种 r 约定下的判定分支与 Θ-data 合法性

### 10.1 分支表（在论文 r 约定未知前的并列结论）

| 分支 | r 定义 | Q_2 | Q_p（奇，未分歧） | Q_l(ζ_l) | e=1∧r/n=1 | 每处系数 `1+[p=2]−1/e−r/n` | deficit 分支结论 |
|---|---|---|---|---|---|---|---|
| **A（项目/ROUTES）** | `p^r = #μ_{p^∞}`（r=log_p） | r=1 ⇒ **0** | r=0 ⇒ 0 | r=1, e=n=p−1 ⇒ (p−3)/(p−1) | **不可实现** | **≥0**（min 0） | `ΣlogMu≥0` 且 `c_lana−ssCoeff=(l+1)(3l+2)/(24l)>0` ⇒ **deficit<0 恒成立（A>0）**；3.12 一致，无 counterexample |
| **B（元素个数）** | `r = #μ_{p^∞}` | r=2 ⇒ **−log2** | r=1, e=n=1 ⇒ **−log p** | r=l ⇒ −2/(l−1)·log l | 可实现 | 可为 −1 | 显式 candidate `l=5, q=22, bad {2,5,11}`：deficit≈**+0.2287>0** ⇒ model-level 反例 |

（分支 A 的 `c_lana−ssCoeff` 恒等式：`(sFactor(l)−1)/(2l) − ((l+1)/24 − 1/(2l)) = (l+1)(3l+2)/(24l) > 0`，l≥5。）

### 10.2 分支 B：最小合法反例所需的 Θ-data 条件（逐条检查）【A808 修正：本小节 r 读取有误，已被 §12 取代】

设 `l≥5` 素数，`q` 为 q-pilot，`A = log q`（q-magnitude），bad 位集含 `q` 的素因子与 `l`。

| # | 条件 | 可实现性检查 |
|---|---|---|
| B1 | `l≥5` 素数、`q>1`、`A=log q` | ✓（取 l=5, q=22） |
| B2 | bad 集 = `primes(q) ∪ {l} ∪ (disc)` | ✓ q=2·11 给 {2,11}，加 l=5 ⇒ {2,5,11} |
| B3 | `ζ_l ∈ F` ⇒ 每位 `K_v ⊇ ζ_l`；p≠l 时 `n_v ≥ ord_l(p)`（未分歧部分），e 可=1 | ✓ p=11: ord_5(11)=1 ⇒ n=1,e=1; p=2: ord_5(2)=4 ⇒ n=4,e=1 |
| B4 | p=l 位：`Q_l(ζ_l)/Q_l` 全分歧 ⇒ `e=n=l−1`（可取 f=1），r=#μ_l=l | ✓ p=5: e=n=4,r=5 |
| B5 | 负贡献处：p≠l 且 `p≡1 (mod l)`（ord_l(p)=1）⇒ e=n=1、r=1（元素个数）⇒ 系数 `1−1−1 = −1` ⇒ `−log p` | ✓ p=11 |
| B6 | p=2 位在 ζ_l 约束下 `n≥ord_l(2)≥2`，系数 `2−1−2/n ≥ 0`（n=4 ⇒ +0.5）⇒ p=2 **不能**给负贡献 | ✓（用 p=2 作正项，靠 p=l 与 p≡1 mod l 的坏位给负项） |
| B7 | p=l 位贡献 `1−(l+1)/(l−1)` 系数 `= −2/(l−1)` ⇒ `−2/(l−1)·log l` | ✓ l=5: −0.5·log5 |
| B8 | 需要 `ΣlogMuPaper < (ssCoeff−c_lana)A` 才能 deficit>0 | ✓ l=5,q=22: Σ=−2.856, (ssCoeff−c_lana)A=−2.627 ⇒ deficit=+0.229 |
| B9 | 胶囊数 nC=l ⇒ `c_lana=(sFactor(l)−1)/(2l)`、`ssCoeff=(l+1)/24−1/(2l)` | ✓ l=5: c_lana=1, ssCoeff=0.15 |
| B10 | **未核**：q-pilot 的精确归一化（A 是否 = log q 还是 (1/2l)log q）、q 与 l 的除法约束、torsion/arch 在 diff 字典中的项、Θ-data 对 F 含 2,5,11,ζ_5 的全局合法性 | ⚠ 模型级成立；精确 Θ-data 合法性待 abc 校验 |

**分支 B 显式候选（模型级）**：`l=5, q=22, A=log 22=3.091`；

| 位 | (e,n,r) | logMuPaper |
|---|---|---|
| p=2 | (1,4,2) | +0.5·log2 = +0.3466 |
| p=5 | (4,4,5) | −0.5·log5 = −0.8047 |
| p=11 | (1,1,1) | −1·log11 = −2.3979 |
| 合计 ΣlogMu | | −2.8560 |

`deficit = (ssCoeff−c_lana)·A − ΣlogMu = −2.6270 + 2.8560 = **+0.2287 > 0**`。
（同一数据在分支 A：ΣlogMu=+1.3246，deficit=−3.952<0。）

### 10.3 分支 A：无条件（模型级）无 counterexample

- 每处系数 ≥0（A800 枚举 55 个可实现元组，min=0；奇 p r≥1 时 φ(p^r)|e ⇒ 1/e+r/n≤1；p=2 e=1⇒r=1,n=1 系数 0）；
- 故 `ΣlogMuPaper ≥ 0`；
- `deficit = (ssCoeff−c_lana)·A − ΣlogMuPaper ≤ (ssCoeff−c_lana)·A`，而 `ssCoeff−c_lana = −(l+1)(3l+2)/(24l) <0`、`A=log q>0`
  ⇒ **deficit < 0 恒成立**（模型级）⇒ 归一化 verdict 成立，3.12 未被反驳。

### 10.4 结论（论文约定未知前）

- **若 r=log_p #μ（ROUTES §6.1 / 项目所有现有 green 注释）**：deficit<0 恒成立（模型级），p=2 与 e=1 都不产生反例，3.12 一致。
- **若 r=#μ 元素个数**：模型级已有显式反例候选（l=5,q=22,bad{2,5,11},deficit≈+0.229>0）；
  该分支下 3.12 的 paper 归一化不等式在忠实（但未完全校验的）Θ-data 模型中为假，需 abc 做 B10 的精确合法性校验。
- **判据**：分支 B 与 ROUTES §6.1 的 "p^r=#roots" 及 "非分歧奇素数给 0" sanity check 冲突；
  在 abc 确认论文 r 定义前，branch A 为项目内部一致的解释，branch B 为待验证的替代解释。

---

## 11. A805 B10 数据校验：nC = l* ⇒ c_lana = ssCoeff 精确相消（决定性化简）

**数据校验结果**（lana 源码）：tmp/external/ported/lana/Iut/Concrete/LocalEstimate.lean:117-118：

    /-- The number of capsules, ℓ* = (ℓ − 1)/2. -/
    abbrev nCaps : ℕ := (D.ℓ - 1) / 2

即 nC = l* = (l−1)/2。由 sFactor n = (n+1)(2n+1)/6（本项目 sFactor_eq 已证），sFactor(l*) = l(l+1)/12，于是

    c_lana = (sFactor(l*)-1)/(2l) = (l(l+1)/12 - 1)/(2l) = (l+1)/24 - 1/(2l) = ssCoeff(l)   EXACTLY.

**推论（B10 (a) 解决）**：sumTheta = c_lana·A = ssCoeff·A，deficit 中 A 项完全相消：

    deficit = ssCoeff·A − sumLogMu − sumTheta = ssCoeff·A − sumLogMu − ssCoeff·A = −sumLogMu.

⇒ (1) q-magnitude 归一化 A（以及 q-pilot 的 A 常数）对 deficit 符号完全无关；分支 B 候选里 A=log q 的用法作废，deficit 直接 = −ΣlogMuPaper；
  (2) 分支 A（r=log_p #μ，每处 logMuPaper ≥0）⇒ **deficit ≤ 0 无条件成立**（模型级）；
  (3) 分支 B（元素个数）⇒ 任一负 logMuPaper 位（如 p=11, e=n=1, r=1 元素 ⇒ −log 11）就使 deficit>0；候选 l=5, bad {2,5,11}：ΣlogMu=−2.856 ⇒ **deficit=+2.856>0**（A 无关）。

**形式化**（新文件 tmp/sheaf/xif/paper/Mzk1ThetaCancelActual.lean，单文件 lake env lean EXIT=0，gate trio，olean 已生成、extras_add 已注册）：

- sum_range_sq_one_add：Σ_{j<n}(j+1)^2 = n(n+1)(2n+1)/6（ℝ）；
- sFactor_eq：sFactor n = (n+1)(2n+1)/6；
- **clana_eq_ssCoeff (k) (hk:2≤k) : clana k (2k+1) = ssCoeff (2k+1)**（nC=k=l*, l=2k+1）；
- **paperDeficit_cancel : paperDeficit (ssCoeff l) A sumLogMu (clana k l · A) = -sumLogMu**；
- paperDeficit_cancel_thetaSum（thetaSumPaper 形式）；
- paperDeficit_nonpos_of_sum_nonneg（分支 A 符号结论）；
- paperMuCoeff_odd_unramified：paperMuCoeff p 1 0 1 = 0（p≠2）。

**B10 剩余待核项（已缩小）**：

1. A 归一化：**已解决**（相消，见上）。
2. q-pilot 是否允许 bad 集含 p=11（及 q 含 11，如 q=22）——需 abc 的 q-pilot 定义/约束；
3. ζ_5 全局包含下 p=11 处未分歧（11≡1 mod 5 ⇒ ord_5(11)=1，且 μ_5 ⊂ Q_11）⇒ e=n=1 合法；p=5 处需 e=n=4（Q_5(ζ_5)）——需确认 Θ-data 允许 l 上位全分歧；
4. p=2 处 ζ_5 迫使 n≥ord_5(2)=4（e=1）——合法但只给正贡献；
5. diff−arch+torsion 在 logMuPaper 已内含（ROUTES §6.1 公式），无额外项（待 abc 复核）。

**结论**：B10 的核心代数据已核实并形式化——c_lana = ssCoeff、deficit = −ΣlogMuPaper；分支 A 下 3.12 归一化 verdict 恒成立（模型级），分支 B 下反例候选只需负的 logMuPaper 位。


---

## 12. A808 修正：r 是 p 幂单位根指数，不是 l 次根 —— 分支 B 候选作废

**纠正**：r 的定义是 p^r = #μ_{p^∞}（p 幂单位根指数），与辅助素数 l 的 l 次根无关。
此前 §10.2 把 p=11 处的 μ_5（l=5 的 l 次根）误当成局部 p-power 根，导致 r=1 的错误；
在 Q_11 中 11 幂单位根只有 {1}，故 r=0。同理 p=2 处 2 幂根为 {±1} ⇒ 2^r=2 ⇒ r=1；
p=5 处 5 幂根为 μ_5（5 个）⇒ 5^r=5 ⇒ r=1。

**修正后的候选表**（l=5, nC=l*=2, ζ_5 全局包含；元素个数读法一并作废，r 按指数）：

| 位 | 域 | #μ_{p^∞} | r | e | n | 系数 1+[p=2]−1/e−r/n | logMuPaper |
|---|---|---|---|---|---|---|---|
| p=2 | Q_2(ζ_5)（未分歧，次数 ord_5(2)=4） | 2 | 1 | 1 | 4 | 2−1−1/4 = 3/4 | +(3/4)log2 = +0.5199 |
| p=5 | Q_5(ζ_5) | 5 | 1 | 4 | 4 | 1−1/4−1/4 = 1/2 | +(1/2)log5 = +0.8047 |
| p=11 | Q_11（ζ_5 ⊂ Q_11，因 5 | 10） | 1 | 0 | 1 | 1 | 1−1−0 = 0 | 0 |

**ΣlogMuPaper = (3/4)log2 + (1/2)log5 = 1.3246 > 0**。

由 §11 的精确相消 deficit = −ΣlogMuPaper：**deficit = −1.3246 < 0** ⇒ 分支 B 的反例消失；
3.12 归一化 verdict 在模型级成立。

**形式化更新**（Mzk1ThetaCancelActual.lean，单文件 EXIT=0，gate trio，olean 已刷新、已注册）：

- logMuPaper_11_eq_zero : logMuPaper 11 1 0 1 = 0；
- candidate_sum_nonneg : 0 ≤ logMuPaper 2 1 1 4 + logMuPaper 5 4 1 4 + logMuPaper 11 1 0 1；
- candidate_deficit_neg (A) : paperDeficit (ssCoeff 5) A (上列三项和) (clana 2 5 * A) < 0；
- 原有：clana_eq_ssCoeff、paperDeficit_cancel (= −sumLogMu)、paperDeficit_cancel_thetaSum、
  paperDeficit_nonpos_of_sum_nonneg、paperMuCoeff_odd_unramified。

**修正后总结论**：

1. 唯一与项目定义一致的读法是 r = log_p #μ（指数）；分支 B（元素个数）是误读，作废；
2. 该读法下每个可实现位的 logMuPaper ≥ 0，且 deficit = −ΣlogMuPaper ⇒ deficit ≤ 0 恒成立（模型级）；
3. e=1 ∧ r/n=1、p=2 负值、p=11 负值等候选全部消失；3.12 未被此路线反驳；
4. 仍待 abc 核对的只剩 Θ-data 合法性细节（q-pilot 允许的 bad 集、l 上位的全分歧性），
   而它们已不影响 deficit 符号（因为 ΣlogMuPaper 每项非负）。
