# INFEASIBILITY-EVIDENCE — lana 已证定理作为“不可行/换概念无效”判据

日期：2026-11-12；qpilot（A899）。**所有路径相对根 `Iut/` 树（`D:/lean/Iut/...`）。** 以下三条均为 lana **已证**定理（源级读取；相关 olean 属根闭包，部分未产）。

## 判定（先给）

**换概念/换说法 = 不可行。** 三条 lana 已证定理合起来给出一个穷尽二分：
- 若保持在 lana 的 `LinkedChain`/LogShellCompat 模型内：容器 freedom 只能用 `1/s` 值群标度，**q-幂 drift 被排除**（①），且墙作为存在/接口陈述**等价于 variant**（②）；
- 若加上唯一已知的非平凡强化 T4（LGP 律）：墙精确等于数值不等式，在 identified-copies 模型下**恰好等于 `SSIneq D`**（③）；
- 因此任何“新概念/新说法”若落在模型内 ⇒ 只是 variant/SSIneq 的等价改写（循环）；若要靠 q-幂 drift/其它容器 freedom ⇒ 与 ① 矛盾（须放弃 LogShellCompat，即离开 lana 已验证模型，成为新猜想，不再有 ②③ 的桥）；
- 缺少的内容**恰好就是** `SSIneq D`（= Corollary 3.12 variant），不是接口/表述缺口。lana 源明确：`SSIneq D` 与其否定都未证（`Iut/Wall/MultiContainer.lean:86–87`）。

## ① q-幂 drift 链不满足 LogShellCompat（排除“把 Θ-link 读成 q-幂 drift”的换概念）

- 定义：`Iut/ThetaLink/Wall.lean:80`
  ```lean
  def LogShellCompat (w : Scaling D) : Prop := act D w (vcI D) = vcI D
  ```
- **定理**：`Iut/ThetaLink/Wall.lean:294`
  ```lean
  theorem not_logShellCompat_chainModel {k : ℤ} (hk : k ≠ 0) :
      ¬ LogShellCompat D ((Wall.chainModel D k).kum (1 : ℤ))
  ```
- 强化：`Iut/ThetaLink/Wall.lean:299`
  ```lean
  theorem LinkedChain.kum_ne_chainModel {k : ℤ} (hk : k ≠ 0) (C : LinkedChain D) :
      C.kum ≠ fun n => (Wall.chainModel D k).kum n
  ```
  即**不存在**任何 `LinkedChain` 使用 drift Kummer 恒等。
- 源文档（L291–293）：“The drifting M3 rows are not log-shell compatible: for `k ≠ 0`, the Kummer identification `q^{−k}` of the theater `1` of `Wall.chainModel D k` does not preserve the log-shell container, so no `LinkedChain` has these Kummer identifications.”
- **判据作用**：把 Θ-link 的 `1/s` 解释为可自由 q-幂 drift 的容器机制，会违反 `LogShellCompat`；因此该“新概念”在 lana 模型内自相矛盾。若放弃 `LogShellCompat`，则离开已验证模型，②③的等价桥不再可用。

## ② 接口 (T1)–(T3) 的 wall 存在陈述 ⟺ variant（“墙的存在性只是 variant 重述”）

- `Iut/Wall/Checks.lean:162`
  ```lean
  theorem exists_isTrivial_iff :
      (∃ A : EtaAlg D, A.IsTrivial) ↔ Corollary312Variant (concreteVariantData D)
  ```
  其中 `IsTrivial`（`:83`）= “对所有 choice `(ι,S)`，`η^anab_{ι,S} = η_q`”（trivial 算法，`trivialAlg` 见 `:142`）。
- `Iut/Wall/Checks.lean:173`
  ```lean
  theorem exists_wall_iff :
      (∃ A : EtaAlg D, Wall D A) ↔ Corollary312Variant (concreteVariantData D)
  ```
- 支撑：`Iut/Wall/Checks.lean:61 numericalWall_iff : NumericalWall D ↔ Corollary312Variant …`（(9-1) 数值形式即 variant）；`Iut/Wall/EtaAlg.lean:201 variant_of_wall`；`Wall` 定义见 `Iut/Wall/EtaAlg.lean:173`（(9-1) 为假设，源注释“never assumed”）。
- 源文档（Checks.lean L25–34）：“the fields (T1)–(T3) do **not** rule out the trivial solution unconditionally; ruling it out is as hard as refuting the variant… As an existential statement over interfaces, the wall is a restatement of the variant: the interface (T1)–(T3) is too weak to encode the provenance of `η^anab`.”
- **判据作用**：任何只在 (T1)–(T3) 接口层做“换说法”（包括 trivial 算法、数值形式 (9-1)、`WallOn` 改写等），得到的都**当且仅当** variant；新表述不增加内容，属于循环。只有对**给定**算法 `A`（Milestone 2–3）墙才非循环。

## ③ T4 下墙 = 显式数值不等式；idAlg 下恰为 SSIneq（“换说法”最终等价于目标不等式）

- `Iut/Wall/Checks.lean:112`
  ```lean
  theorem wall_iff_of_lgpLaw (κ : ∀ {B : A.BPSA} {h : A.Side}, A.Choice B h → ℝ)
      (hκ : ∀ …, logVol D (A.out ι S) = κ ι + logVol D S.1) :
      Wall D A ↔ ∀ h₁ h₂ : A.Side, ∃ ι : A.Choice (A.qBPS h₂) h₁,
        (concreteVariantData D).qPilot.lhs - κ ι ≤ logVol D (hullOf D (vcI D))
  ```
- `Iut/Wall/IdentifiedCopies.lean:479`
  ```lean
  theorem idAlg_lgpLaw : (idAlg D).LGPLaw
  ```
  （`LGPLaw` **T4** 定义：`:93`，输出为 `κ_ι + log-vol(S)`。）
- `Iut/Wall/IdentifiedCopies.lean:488`
  ```lean
  theorem wall_idAlg_iff :
      Wall D (idAlg D) ↔
        (sFactor (nC D) - 1) * D.qPilot.absLogQ ≤ logVol D (hullOf D (vcI D))
  ```
- 右侧正是 `SSIneq` 的定义（`Iut/Wall/MultiContainer.lean:88`）：
  ```lean
  def SSIneq (D : InitialThetaData.{0}) : Prop :=
    (sFactor (nC D) - 1) * D.qPilot.absLogQ ≤ logVol D (hullOf D (vcI D))
  ```
  因此 `Wall D (idAlg D) ↔ SSIneq D`（定义展开）。
- 辅助：`idAlg_not_isTrivial`（`:483`，T4 排除 trivial 实例，但墙仍是数值条件）；`exists_wallOn_chain`（`Iut/Wall/MultiConstraints.lean:271`）说明允许 distortion 自由 drift 时墙可被任意 `k` 满足 ⇒ 墙本身不约束 SSIneq；必须固定 T4/idAlg 才有内容。
- **判据作用**：任何“新概念”若声称给出 T4/identified-copies 模型下的墙，它证明的就是显式数值不等式；在 `idAlg` 上就是 `SSIneq D` 本身。没有比 `SSIneq` 更弱的中间陈述可停靠。

## 汇总：不可行判据表

| 换概念类型 | lana 已证反制 | 结果 |
|---|---|---|
| 把容器 freedom 读成 q-幂 drift | ① `not_logShellCompat_chainModel`（k≠0 无 LogShellCompat；`LinkedChain.kum_ne_chainModel`） | 模型内矛盾；放弃 LogShellCompat 则离开已验证模型 |
| 在 (T1)–(T3) 接口层重述墙/数值形式 | ② `exists_isTrivial_iff`、`exists_wall_iff`（⟺ variant）；`numericalWall_iff` | 循环：等价于 variant，无新内容 |
| 加 T4/LGP 律后重述墙 | ③ `wall_iff_of_lgpLaw` + `idAlg_lgpLaw` + `wall_idAlg_iff`（⟺ `SSIneq` 定义） | 等价于目标不等式 `SSIneq D` 本身 |
| 任意“新说法” | 要么落入 ①（被排除），要么落入 ②/③（等价改写） | **不可行**：缺少的内容恰是 `SSIneq D`/variant，不是表述/接口缺口 |

## 附：证明结构要点

- `Wall`（`Iut/Wall/EtaAlg.lean:173`）本身是 (9-1) 的假设（“A hypothesis, never assumed”）；`wall_iff_forall`（`:183`）显示 Θ-link 数据是 vacuous 的；
- `variant_of_wall`（`:201`）把墙变成 variant；`exists_wall_iff` 反过来把 variant 变成某算法（trivial）的墙；两者合起来就是“存在性循环”；
- ②③的数值化不引入新数学：`idAlg` 的 `κ = logVol(lgp(integralRegion))`，`logVol_lgp_integral` 算出 `(sFactor−1)|log q|`，于是墙的 RHS 就是 `SSIneq`。

**结论（给 lead/用户）**：lana 已证的三条定理把任何“换概念/换说法”的路线逼入死角——要么被 LogShellCompat 排除，要么只是 variant/SSIneq 的等价改写。**不可行结论成立**；唯一未证内容就是 `SSIneq D`（Scholze–Stix 不等式）本身，lana 源也明确其与否定均未证（`Iut/Wall/MultiContainer.lean:86–87`）。
## ④ face5（Arakelov-degree / hull-difference）— **尚未否决**

face5 不是 face1–face4 的换说法：它试图用 Arakelov 次数直接证明
`logVol(hull) + A >= avgDeg(gaussGen) = sF*A`（等价于 `SSIneq`），而不经过 q-power drift/接口层。

- **候选工具**: `Iut/Arakelov/LineBundle.lean:101` `deg`、`:105` `degNorm`；`Iut/Arakelov/QPilot.lean:262` `logVol_lgp_integral_eq_degNorm`；`Iut/ThetaLink/Gauss.lean:228` `avgDeg_gaussian`、`:292` `gaussLink`、`:393` `avgDeg_gaussGen`；`Iut/WallEquiv/VcI.lean:741` `logVol_hull_vcI_eq`、`:762` `logVol_hull_vcI_sub_eq`。
- **状态**: 全部为 lana 根 `Iut/` 源级；本地 oleans 未产；尚无 face5 定理。
- **判据**: 若 P5 显示只是等价改写/恒等式/需要新未登记假设，则按用户定义判不可行；若给出真正新不等式，则 face5 可行。
- **结论**: **face5 尚未否决（NOT REJECTED）**，与 face1–face4 的已否决状态分开登记；详见 `coord/FACE5-ATTACK.md`。
