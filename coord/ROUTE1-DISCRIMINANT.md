# ROUTE1-DISCRIMINANT — 路线一轨道生成格判别（task-78 / R29 P2）

日期：2026-11-13；qpilot。**Status: source-level construction + read-only substrate audit + build record**；未编辑 `GlobalThetaPilot*`（shehdd task-79 负责）。

## 0. 结论先行

**判定：该局部构造无增益；在 A-Source 成立的前提下落入 HANDOFF §4.8 的 (A8) 公共标量停止情形。**

理由：实际 native bad-place Theta-pilot 像全部是**同一个 q-log 向量**的整数倍：
```
route1Image(m,j) = (gaussExponent j) • (m • route1QLog)
```
其中 `route1QLog b = baseQLogMagnitude T b`。`j=1` 是合法 signed label，且 `gaussExponent 1 = 1`，
所以 orbit lattice 已经等于 base lattice；有限商恒平凡、与 m 无关。

更早的 A-Source 也尚未成立：现有实际像是 bad-place **value group 的 log 值乘积**，没有构造到 paper 锁定 U_theta / C3 tensor block 的运输；
`GlobalThetaPilotPlaceMapActual` 只给出 `BadToC3TensorMap` 的 obstruction，没有 map。

## 1. 新文件与 build 证据

文件：`tmp/sheaf/xif/paper/Mzk1Route1OrbitLatticeActual.lean`
- 大小：**7,493 B**；SHA256 前 16 位：`7441898c2f1375ec`；
- imports：`GlobalThetaPilotLogVolumeActual`（green，olean 190,152B）及 Mathlib；**不 import 5 个 red 的 GlobalThetaPilot 文件**；
- 编译：watchdog **DONE EXIT=0**（2026-11-12T20:11:27Z，91s；olean 141,144B）；
- 无 `sorry`/axiom/True/PUnit/toy carrier；无 `.olean` 产物（直接 lean 编译，未走 lake build）；
- 核心声明行：`route1Image` 60，`route1BaseLattice` 70，`route1OrbitLattice` 75，`route1Image_eq_nsmul` 98，`route1OrbitLattice_eq_base` 134，`route1OrbitLattice_rank_le_one` 140，`route1_quotient_trivial` 152，`route1_globalThetaPilotLogVolume_eq` 159。

### 1.1 实际像来源（file:line）

| 事实 | 路径:行 |
|---|---|
| red：bad q parameter = `I.initial.reduction.qParameter b` | `tmp/sheaf/xif/paper/GlobalThetaPilotPossibleImagesActual.lean:45-46`（olean **无**） |
| red：local theta value = `q_b^(gaussExponent j)` | 同上 `:49-50` |
| red：global candidate = `b ↦ ofAdd(log theta)`，possible images = Set.range | 同上 `:54-63` |
| red：positive theta value from native base q | `GlobalThetaPilotPossibleImageGeometryActual.lean:37-39`（olean **无**） |
| red：geometric possible image/set | 同上 `:48-57`；multiradial hull **obstruction** `:89-96` |
| red：global theta value = Σ −log thetaValue | `GlobalThetaPilotProcessionActual.lean:34-35`（olean **无**） |
| red：possible image set (global) / hull obstruction | 同上 `:55-70` |
| red：BadToC3TensorMap obstruction（no map） | `GlobalThetaPilotPlaceMapActual.lean:48-56`（olean **无**） |
| red：PlaceComparisonData / obstruction | `GlobalThetaPilotPlaceComparisonActual.lean`（olean **无**） |
| green：actual native q family log-magnitude | `BaseQLogVolumeActual.lean:49`（olean **有**） |
| green：global Theta-pilot log-volume = coeff × q-pilot magnitude | `GlobalThetaPilotLogVolumeActual.lean:150-154`（olean **有** 190,152B） |

## 2. §4.10 六检查点逐条

| # | 检查点 | 结论 | 证据 |
|---|---|---|---|
| 1 | 作用是否混合不同赋值方向 | **否** | `route1Image_eq_nsmul`：所有像都是同一个向量 `route1QLog` 的整数倍；没有 Q_p-linear 自同构/矩阵混合不同 bad-place 方向。 |
| 2 | O_E-闭包是否使候选像相同 | **闭包后相同；且当前没有实际 O_E 作用** | 当前 carrier 是 `Bad → Real`；`AddSubgroup.closure` 下所有像生成 `Z·g`，而 `j=1` 的像就是 g，故 orbit=base；paper 的 O_E hull 未构造。 |
| 3 | 原始格是否满维 | **否（对 d=#bad>1）** | `route1OrbitLattice_rank_le_one`：orbit ≤ `Z·g`，rank ≤1；满维只在 d=1 时可能。 |
| 4 | 有限商大小是否随 m 增长 | **否** | `route1_quotient_trivial`：对每个 m，orbit=base；`route1Image`/`route1ScaledQLog` 都是 `m` 的公共标量；商平凡，index=1。 |
| 5 | 增长在原权重下是否仍在 | **否** | `route1_globalThetaPilotLogVolume_eq`：global theta log-volume = `(gaussExponentSum/card)·globalQPilotLogMagnitude`，是已有 q-pilot 量的固定倍数，无新的 m 增长。 |
| 6 | 是否重复计入已有修正项 | **是** | 同一 `baseQLogMagnitude`、同一 `gaussExponentSum`；与 CTheta/Gap 的 q-side 修正重叠。 |

## 3. 代数判别（A-Source / A-Rank / A8）

- **A-Source：FAIL（当前）**：red `GlobalThetaPilotPossibleImagesActual` 的像是 bad-place value group 的 log 值乘积，不是 paper 的锁定 U_theta / C3 tensor block；
  `BadToC3TensorMap` 在 `PlaceMapActual:51-56` 只是 structure + obstruction `Nonempty`，没有构造实际 map；
  `GlobalThetaPilotMultiradialGeometryData` 仅是 exact obstruction；
  ⇒ 这些像先要经过 bad-place → C3 tensor block 的运输，才有资格进入“像属于 U_theta”。
- **A-Rank：FAIL**：即使忽略 A-Source，orbit 由单个向量生成，rank≤1；对 d≥2 不满行秩。
- **A8：APPLIES**：所有 g 是 Q_p-linear（这里是恒等/公共标量），base lattice = `Z·(m g)`，像集 = `{n_j·(m g)}`；
  `orbit = Z·(m g) = base`；相对 ratio =1，与 m 无关。
- **A-Formula：仅有平凡公式**：`Λ_G=Z·g`，`#(Λ_G/Λ_0)=1`；没有随 m 增长的初等因子。

## 4. 停止条件对照（HANDOFF §4.11）

| 停止条件 | 本构造 |
|---|---|
| 所需矩阵不属于真实允许作用 | 是：没有 Q_p-linear g 的矩阵；只有恒等/公共标量 |
| 公共标量引理 (A8) 覆盖全部候选 | **是** |
| 生成矩阵在需要维度恒不满秩 | **是**（rank≤1） |
| 只有扩大标签/替换载体/删权重才出现增益 | 是：标签只改变整数倍 n_j |
| 下界依赖 M≥0 或等价式 | 否（本文件不依赖），但这不产生增益 |

**结论：该局部构造无增益。** 它是一个 source-level、可编译的**判别/停止证据**，不是路线一进展，也不能作为 M≥0 的新证明。

## 5. 仍需 Lead/其他任务协调的事项

1. **A-Source transport**：需要 `BadToC3TensorMap`/`GlobalThetaPilotPlaceMapData` 的实际构造（当前只是 obstruction）；
2. **shehdd task-79**：5 个 `GlobalThetaPilot*` 文件的编译修复；本文件只依赖 green `GlobalThetaPilotLogVolumeActual`，未编辑 red 文件；
3. **若要继续路线一**：必须找到**多个线性独立**的实际像/作用；当前 actual q_v^(j^2) 族在数学上只有一条公共方向，扩大标签不会增加 rank；
4. **路线二**：本判别不支持路线一局部增益，但 `Z·g`/公共标量结构可直接作为路线二对偶侧的失败对照。

## 6. 文件/证据

- 新 Lean：`tmp/sheaf/xif/paper/Mzk1Route1OrbitLatticeActual.lean`（7,493B；SHA `7441898c…`；EXIT0）；
- 本文件：`coord/ROUTE1-DISCRIMINANT.md`；
- 只读源：`GlobalThetaPilotPossibleImagesActual.lean`、`PossibleImageGeometryActual`、`ProcessionActual`、`PlaceMapActual`、`PlaceComparisonActual`、`ThetaPilotObjectActual`、`GlobalThetaPilotLogVolumeActual`；
- build 证据：`dag/watchdog/watchdog.log` 的 DONE EXIT=0；olean 141,144B；不自行编译；未跑全项目构建。