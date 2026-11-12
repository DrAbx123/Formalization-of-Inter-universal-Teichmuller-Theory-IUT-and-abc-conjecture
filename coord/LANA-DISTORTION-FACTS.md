# LANA-DISTORTION-FACTS — 用户引用事实的根树逐行核验

日期：2026-11-12；qpilot（A896）。**所有路径相对根 `Iut/` 树（`D:/lean/Iut/...`）**。

## 0. 结论

用户四条事实**全部指向 `Iut/ThetaLink/Wall.lean` 与 `Iut/Wall/MultiContainer.lean`**，内容与用户所述一致，但有三点需钉死：
1. “Wall.lean:228/232”的 Wall.lean 是 **`Iut/ThetaLink/Wall.lean`**（根树另有 `Iut/EtaleTheta/Wall.lean`、`Iut/Frobenioid/Wall.lean`、`Iut/HodgeTheater/Wall.lean`，均无这两个声明）；
2. `Wall.lean:27`（`1/s` 不作用容器）是 **docstring 的建模陈述（L27–28）**，不是定理；该模型条件是 `LinkedChain.LogShellCompat` 假设字段，源码 L59–61 明确说“论证但未从 anabelian 重构推出”；
3. `MultiContainer.lean:248` 的 `distortion` 是精确的 `def`（见下）；它与链二 `allowedLower·logp` 的对应是**公式级**的：仅在 distortion 集中在一个固定坏素数且为纯 `q`-幂漂移时严格写成 `allowedLower·logp`。

## 1. 逐行核验

### F1 `distortion_eq_zero`（用户：Wall.lean:228）
- **实际**：`Iut/ThetaLink/Wall.lean:228`
```lean
theorem distortion_eq_zero (m n : ℤ) : C.toModel.distortion m n = 0 :=
  C.toModel.distortion_eq_zero_of_volCompat C.volCompat m n
```
- **判定：内容如用户所述（TRUE）**；路径须写 `Iut/ThetaLink/Wall.lean`。
- **条件性**：证明用 `C.volCompat`；`volCompat` 来自 `C.kummerVolCompat : C.toModel.KummerVolCompat`（L220–221），后者由 `C.logShell : ∀ n, LogShellCompat D (C.kum n)`（`LinkedChain` 字段，L203–204）经 `shift_eq_zero_of_logShellCompat` 得到。故该定理是 **modelling hypothesis 下**的结果，不是无条件 IUT 事实。
- 同型声明在其它包：`Iut/LogLink/GalKummer.lean:381/417`、`Iut/LogLink/Kummer.lean:279`、`Iut/LogLink/StripKummer.lean:194`、`Iut/LogLink/GalKummerAll.lean:609`（各自不同的 `distortion_eq_zero`，勿混用）。

### F2 `wallOn_thetaRow_iff`（用户：Wall.lean:232，`WallOn thetaRow ↔ SSIneq D`）
- **实际**：`Iut/ThetaLink/Wall.lean:232`
```lean
theorem wallOn_thetaRow_iff : C.toModel.WallOn thetaRow ↔ SSIneq D :=
  C.toModel.wallOn_iff_ss_of_volCompat (theaterAlg_thetaShift D C.pic.H) C.volCompat
    ⟨(0 : ℤ), (1 : ℤ), (zero_add 1).symm⟩
```
- **判定：内容如用户所述（TRUE）**；路径 `Iut/ThetaLink/Wall.lean`；同样依赖 `C.volCompat`（即 `LogShellCompat` 建模假设）。
- 配套：`:237 wall3_iff`（所有对）；`:245 answer`（含 `distortion n (n+1)=0` 与 `WallOn thetaRow ↔ SSIneq D` 的合取）。

### F3 `Wall.lean:27`（用户：`1/s` 缩放不作用容器）
- **实际**：`Iut/ThetaLink/Wall.lean:27–28`（连续 docstring 两行）：
  - L27: “Proposition 3.9(ii)). The value-group portion, which the Θ-link rescales by `1/s`”
  - L28: “(`ThetaLinkIso.val_apply`), does not act on the containers.”
- **判定：陈述如用户所述（TRUE as doc claim）**；但它是**建模陈述**，不是定理。源码 L56–61 的 Scope 明确：
  > “Whether the output of an actual η-algorithm through the Θ-link has this law is not decided here … Log-shell compatibility is a modelling condition (a hypothesis field of `LinkedChain`), argued above but not derived from an anabelian reconstruction of the log-shells …”
- 形式化落点：`LinkedChain.logShell : ∀ n, LogShellCompat D (C.kum n)`（L203–204）；`kummerVolCompat`（L220–221）把它变成 `shift = 0`；`distortion_eq_zero`（L228）由此推出。**没有**定理断言真实 Θ-link 的 value-group `1/s` 不作用容器；这是假设。

### F4 `distortion`（用户：MultiContainer.lean:248）
- **实际**：`Iut/Wall/MultiContainer.lean:248`
```lean
noncomputable def distortion (h₁ h₂ : M.HT) : ℝ := shift D (M.kum h₂) - shift D (M.kum h₁)
```
- **判定：精确如用户所述（TRUE）**。
- 上下文：`shift` 定义 `Iut/Wall/Scaling.lean:311` `shift D w := logVol D (act D w (integralRegion D))`；`logVol_act`（L314）：`logVol(act w S) = shift w + logVol S`。
- 关键定理：`Iut/Wall/MultiContainer.lean:252–253`：`M.vol h₂ (transport h₁ h₂ U) = M.vol h₁ U + M.distortion h₁ h₂`；`:286 distortion_eq_zero_of_volCompat`；`:295 def WallOn`；`:341 wallOn_iff_of_thetaShift`。
- 墙带 distortion 的精确形式（L341–344）：
```lean
theorem wallOn_iff_of_thetaShift (hS : M.alg.ThetaShift) (L : M.HT → M.HT → Prop) :
    M.WallOn L ↔ ∀ h₁ h₂, L h₁ h₂ →
      (sFactor (nC D) - 1) * D.qPilot.absLogQ - M.distortion h₁ h₂ ≤
        logVol D (hullOf D (vcI D))
```
- Drift 实例：`Iut/Wall/MultiConstraints.lean:225 chainModel D k`，`:236 distortion_chain`：
  `(chainModel D k).distortion n m = k * (m - n) * D.qPilot.absLogQ`；
  `:244 wallOn_chain_iff`：`(chainModel D k).WallOn thetaRow ↔ (sFactor(nC D) − 1 − k) * |log q| ≤ logVol(hull)`；
  `:271 exists_wallOn_chain`：对每个 `D` 都有 `k` 使墙成立（**说明仅靠可自由漂移的 distortion，墙本身没有信息**）。

## 2. distortion 与链二模型 `allowedLower·logp` 的对应

链二模型（`tmp/sheaf/xif/paper/Mzk1Chain2CoreActual.lean`，`structure Chain2Data`）：
```lean
structure Chain2Data where
  baseShellVolume : ℝ
  logp : ℝ;  logp_pos : 0 < logp
  allowedLower allowedUpper : ℝ;  lower_le_upper : allowedLower ≤ allowedUpper
  qPilotOrd : ℝ;  qPilot_lower : allowedLower ≤ qPilotOrd;  qPilot_upper : qPilotOrd ≤ allowedUpper
def shellVolume (D) : ℝ := D.baseShellVolume - D.allowedLower * D.logp
theorem survival_iff : req ≤ shellVolume D ↔ allowedLower ≤ (baseShellVolume - req)/logp
```

**公式级对应（严格，在单坏素数/纯 q-幂漂移时）**：

| 链二 | lana 根树 | 关系 |
|---|---|---|
| `shellVolume = baseShell - allowedLower·logp` | 墙：`(sFactor−1)|log q| − distortion ≤ logVol(hull)` | 令 `baseShell − req = (sFactor−1)|log q|`，`allowedLower·logp = distortion`，则 `req ≤ shellVolume ⇔ 墙` |
| `allowedLower` | `distortion h₁ h₂` | `allowedLower = distortion / logp` |
| `qPilotOrd` | `|log q| / logp`（归一化 ord） | `qPilotOrd = D.qPilot.absLogQ / logp` |
| drift 模型 | `distortion_chain n m = k(m−n)|log q|` | `allowedLower = k(m−n)·qPilotOrd`；单步（m−n=1）：`allowedLower = k·qPilotOrd` |

**关键注意事项**：
1. `allowedLower·logp = distortion` **仅在** distortion 完全集中在所固定坏素数 p 上、且为纯 `q`-幂漂移时严格成立。lana 的 `distortion` 是全体 tensor 分量（`Scaling` 在 `i, p, c` 上）的 `shift` 差之和；一般情形需写成 `allowedLower := distortion/logp`（把全部 distortion 折算成 p 的对数单位），或投影到 p-分量再比较；
2. `distortion_eq_zero`（F1）在 `LogShellCompat` 建模假设下成立；链二若取该假设，`allowedLower = 0`（无漂移）——这与 `CHAIN2-PHASE2` “decisive requirement allowedLower ≤ −1” 是一致性检查点：**漂移符号/大小是 chain-2 的输入参数，不是 lana 已证事实**；
3. `exists_wallOn_chain` 表明任何想要的墙都可用合适 `k` 满足（墙本身不约束 SSIneq）；因此链二真正需要的是 `allowedLower` 的**全局确定**（G），而 lana 只给“distortion 是自由漂移”的结构，不给 G。

## 3. 与链二 G1/G2/G3 的接口位置

- lana `distortion` = 容器 transport 的 log-volume 偏移；链二 `allowedLower·logp` = hull 壳体积可下移的量；**二者在 drift 模型中相等**，这给 `Chain2Data.allowedLower` 一个真实的 lana 对应量；
- G1（`rlf_unique`/`scaling_iff`）固定的是 PF/1-s 标度，不直接给 distortion；G3（`componentVol` 乘积律）给的是 log-volume 的加性计算，二者结合可以计算 `shellVolume` 侧；
- 但 `MultiContainer.distortion` 是**model-level**对象（依赖 `kum : Scaling` 数据），不是真实 Θ-link 的算子；真实 Θ-link 的 distortion 是否为零/多少是 §14 链二的开放点（matching `LogShellCompat` 是建模假设）。

## 4. 用户事实判定汇总

| 用户引用 | 实际根树位置 | 陈述 | 判定 |
|---|---|---|---|
| Wall.lean:228 `distortion_eq_zero` | `Iut/ThetaLink/Wall.lean:228` | 精确如上 | ✅ TRUE（路径需加 `ThetaLink/`；条件：LogShellCompat） |
| Wall.lean:232 `wallOn_thetaRow_iff` | `Iut/ThetaLink/Wall.lean:232` | `WallOn thetaRow ↔ SSIneq D` | ✅ TRUE（路径同上；条件：LogShellCompat） |
| Wall.lean:27 `1/s` 不作用容器 | `Iut/ThetaLink/Wall.lean:27–28` | docstring 建模陈述 | ✅ 内容 TRUE，但**非定理**（`LogShellCompat` 假设；Scope L56–61） |
| MultiContainer.lean:248 distortion | `Iut/Wall/MultiContainer.lean:248` | `def distortion := shift h₂ − shift h₁` | ✅ TRUE（精确） |

**结论：用户引用的四条事实内容均成立**；需补的限定是：文件路径为 `ThetaLink/Wall.lean`（不是其它 Wall.lean）、L27 是建模 docstring（非定理）、distortion 与 `allowedLower·logp` 的对应在 drift/单素情形下成立（一般 distortion 是全体分量之和）。