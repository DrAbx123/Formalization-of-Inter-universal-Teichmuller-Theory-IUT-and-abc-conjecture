# FACE5-SECTION-CORIC — 候选 3（κ-coric 截面）核验

日期：2026-11-12；qpilot（A909）。**路径相对根 `Iut/` 树（`D:/lean/Iut/...`）**。

## 0. 结论（先给）

**κ-coric 在根 `Iut/` 树中没有定义（不是“未用于 face5”，而是“未形式化”）。** `Iut/LogLink/Thm311Rest.lean:108` 位于 **“What is not formalised (precisely)”** 小节：
> “(d): the `κ`-coric functions, `π_1^{κ-sol}(D^⊛)` and the cyclotomic rigidity of IUT I, Example 5.1(v) are **not formalised**; only the interaction of `F_mod^×` with the unit portions.”

全根树 grep（`κ-coric`、`kappaCoric`、`kappa_coric`、`KappaCoric`、`κsol`、`Ksol`、`pi1Ksol`）**零命中**；因此：

| 问题 | 答案 |
|---|---|
| ① 精确定义与 namespace？ | **无定义**。第 108 行只是“未形式化”清单条目；最近的形式化对象是 `Iut.LogLink.BiCoricKummer`（structure，L173）与 `Iut.LogLink.MonoThetaKummer`（L270），二者是 **模型数据/同构**，不含 κ-coric 函数。 |
| ② 能否作 Face5SectionData 截面候选？ | **不能**。它没有线丛/截面对象，没有逐位赋值（`ord`）与 arch 范数数据；`Face5SectionData` 所需 `degNorm`/`archTerm`/`section_nonzero`/`deg_identity` 全部无法给出。 |
| ③ 是否有 degree 定理？ | **没有**。`BiCoricKummer` 只含 `cor/kum/env/envIso` 及同构定理；`Thm311iii` 只含 (a)–(d) 同构/刚性陈述；无任何 `deg`/`degNorm` 或 κ-coric 度。 |

## 1. 第 108 行上下文（`Iut/LogLink/Thm311Rest.lean`）

- 文件结构：L94 `## What is not formalised (precisely)` 起，逐条列出未形式化部分；L96–101 coric strips/env strips 是 `BiCoricKummer`/`MonoThetaKummer` 的**数据**；L102–107 环境是 abstract mono-theta env；**L108–109 (d) κ-coric functions / π₁^{κ-sol} / IUT I Example 5.1(v) cyclotomic rigidity 未形式化**；L110–112 Theorem 1.5(v) 的 `D^⊩(D^⊢)` 未构造；L113–114 这些不影响 multi-container model (`XiPrinciple`, `xi_iff_ss`)。
- 即：该行不是定义，而是**排除声明**；不能作为“已有构造”引用。

## 2. 最近的形式化对象（但不是 κ-coric）

### 2.1 `BiCoricKummer`（`Iut.LogLink.BiCoricKummer`，`Thm311Rest.lean:173–182`）
```lean
structure BiCoricKummer (L : LogThetaLattice D) where
  cor : ℤ → FMuStrip D                      -- F^{⊢×μ}_△(n,◦D^⊢_△) coric strip
  kum : ∀ n m, (L.H (n,m)).Fmu.Iso (cor n)  -- Kummer isomorphisms
  env : ℤ → FMuStrip D                      -- environment strip
  envIso : ∀ n, (cor n).Iso (env n)         -- natural isomorphisms
```
- `ofLattice`（L190）：每个 lattice 都有 bi-coric Kummer data（tautological）；
- 定理：`horizCor_bijective`、`kum_comm`、`biCoric_square`（L196–255）；这些是 **prime-strip 同构**，不是 κ-coric 函数，也没有算术赋值。

### 2.2 `MonoThetaKummer`（`Iut.LogLink.MonoThetaKummer`，`Thm311Rest.lean:270–285`）
```lean
structure MonoThetaKummer where
  envF : ℤ×ℤ → ∀ w ∈ D.VBad, MonoThetaEnv
  envD : ℤ → ∀ w ∈ D.VBad, MonoThetaEnv
  inF / inD : inputs of cyclotomic rigidity
  kum : MonoThetaEnv.Iso (envF …) (envD …)
  perm : MonoThetaEnv.Iso (envD n) (envD (n+1))
```
- `Compatible`（L297）是假设字段；`const`（L305）给非空实例；
- 它与 `EtaleTheta.MonoThetaEnv`/`CycRigidity`（[EtTh] Cor 2.19(i) 的 mono-theta 环境版本）相连，但**不是** IUT I Example 5.1(v) 的 κ-coric/pim κ-sol 层。

### 2.3 `Thm311iii`（L565–604）/`thm311iii_model`（L608）
仅 (a)–(d) 的 **同构/双射/刚性**陈述：`a_full`、`a_kummer`、`a_biCoric`、`b_env`、`c_cyc`、`cd_stable`、`cd_labels`、`d_fmod`。**无 degree、无截面、无 κ-coric 函数。**

## 3. 为什么它不能作 Face5SectionData 的截面候选

Face5 所需的 `Face5SectionData`（见 `coord/FACE5-ATTACK.md` §3 / `FACE5-SECTION-VERDICT.md`）：
- `degNorm : ℝ`（hull 差丛的归一化度）；
- `archTerm : ℝ`（所选截面的 arch 贡献）；
- `section_nonzero : Prop`；`deg_identity`；`hullBundleDeg = hullLogVol`；
- 以及整性/`arch` 预算。

κ-coric 路线**没有任何一个字段可用**：
1. κ-coric functions 不是线丛的截面，也没有局部 `ord_v` 值（IUT I Example 5.1(v) 的 κ-coric 数据在 lana 中完全缺失）；
2. `π_1^{κ-sol}(D^⊛)` 与 cyclotomic rigidity 同属缺失层；`EtaleTheta.Env.CycRigidity` 只覆盖 [EtTh] 的 mono-theta 环境版本，不是 IUT I 的 κ-coric 版本；
3. 若要在 Lean 中使用 κ-coric 作为截面，必须先形式化 IUT I Example 5.1(v)（κ-coric functions、π₁^{κ-sol}、cyclotomic rigidity）+ 其 degree/arch 计数——这是 **Layer B 的大缺口**，不是 face5 的 shortcut；任何直接把 κ-coric 当“已有截面”的写法都是 fake/assumed，违反 gate。

## 4. 已有 degree 定理检查（③）

| 对象 | 源 | 是否有 degree |
|---|---|---|
| `BiCoricKummer` | `Thm311Rest.lean:173` | **无**（只有 iso 数据） |
| `MonoThetaKummer` | `:270` | **无**（env 数据/输入） |
| `Thm311iii` | `:565` | **无**（(a)–(d) iso 陈述） |
| value-group BPS `rlfData`/`PF` | `:523`/`Wall/BPS.lean:210` | 有 `PF`/`Iso` 唯一性；**不是** κ-coric 度 |
| pilot degree（`degTheta`/`degreeNorm_*`） | `Wall/Pilots.lean:167`、`Frobenioid/Wall.lean` | 有 Θ/q-pilot degree；**不是** κ-coric |
| `Arakelov` 线丛 degree | `Arakelov/LineBundle.lean:101` | 有一般线丛度；κ-coric 未连接到任何 bundle |

**结论：无 κ-coric degree 定理；κ-coric 与 Arakelov line bundle/degNorm 没有任何现成连接。**

## 5. 对 face5 的判定

**候选 3 不成立**：κ-coric 不是“已有但未用”的截面，而是根树**明确未形式化**的层。
- 不能提供 `Face5SectionData` 的任何字段；
- 不能给 degree；不能给逐位赋值/arch 范数；
- 若 face5 依赖 κ-coric，则它需要先补 IUT I Example 5.1(v) 的 κ-coric 形式化（Layer B），这不是“换说法”，而是一个 **新增的大形式化任务**，并且不能从 lana 现成定理得到。

**建议**：face5 若继续，唯一诚实路线仍是 `FACE5-SECTION-VERDICT.md` 所述——构造 hull 差丛的**具体整性截面 + arch 界**；κ-coric 路线在根树中**不可用**，不得作为候选引用。

## 6. 源索引（根树）

| 内容 | 源 |
|---|---|
| “κ-coric functions … not formalised” | `Iut/LogLink/Thm311Rest.lean:94–114`（引文在 L108–109） |
| `BiCoricKummer` structure / namespace / ofLattice | `Iut/LogLink/Thm311Rest.lean:173,184,190` |
| `MonoThetaKummer` structure / Compatible / const | `:270,287,297,305` |
| `Thm311iii` / `thm311iii_model` | `:565,608` |
| [EtTh] mono-theta 环境 cyclotomic rigidity（非 κ-coric 版本） | `Iut/EtaleTheta/Env/CycRigidity.lean:502` 等 |
| Arakelov degree/degNorm（未连接 κ-coric） | `Iut/Arakelov/LineBundle.lean:101,105` |