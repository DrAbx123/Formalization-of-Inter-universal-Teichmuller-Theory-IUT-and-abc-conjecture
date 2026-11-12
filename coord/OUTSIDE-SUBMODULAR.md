# OUTSIDE-SUBMODULAR — c1/S1487 局部 log-volume 的次模性检验

日期：2026-11-13；qpilot（A1086）。**仅 Python**；数据 `coord/ub_curves_9999.jsonl`（N≤9999，ℓ=5，admissible 12,354）。

## 1. 集合函数（place 集合 S）

每个 bad place p 有 c1 e-exact 局部量 `V_p=H_p`, `gap_p=Ind2_p`, `A_p=v_p logp/(2ℓ)`。定义：

```
f_L(S) = Σ_{p∈S}(V_p+gap_p)                       （局部 log-volume proxy）
f_N(S) = f_L(S) − (sF−1)Σ_{p∈S}A_p                （净变体 margin）
f_D(S) = max(0, −f_N(S))                           （deficit）
f_maxV(S)=max_{p∈S}V_p, f_maxGap(S)=max_{p∈S}gap_p, f_ratio(S)=f_L(S)/((sF−1)ΣA_p)
```
空集函数值取 0；对每曲线的所有 disjoint A,B 检验 submod（fA+fB≥fA∪B+f∅）与 supermod（≤）。

## 2. 结果（12,354 条 admissible）

| 函数 | all-submod | all-supermod | 结论 |
|---|---:|---:|---|
| f_L | **12,354** | **12,354** | 逐位可加，等式（平凡） |
| f_N | **12,354** | **12,354** | 逐位可加，等式 |
| f_D=max(0,−f_N) | **12,354** | **12,351** | **submodular**（3 条 super 反例） |
| f_maxV | **12,354** | 356 | submodular；一般不 super |
| f_maxGap | **12,354** | 3,512 | submodular；一般不 super |
| f_ratio | **12,354** | 3,512 | 在可定义处 submodular |

## 3. 分组下界（用 f_D 的 submodularity）

`f_D(∅)=0`，且 f_D submodular ⇒ 对任意划分 `{G_1,...,G_k}`：
```
f_D(∪ G_i) ≤ Σ_i f_D(G_i)
```
又 `f_D(total)=max(0,−f_N(total))`，故
```
f_N(total) ≥ −f_D(total) ≥ −Σ_i f_D(G_i)
```
如果每个组 `f_D(G_i)=0`（即 `Σ_{p∈G_i}(V_p+gap_p) ≥ (sF−1)Σ_{p∈G_i}A_p`），则 total 的 f_D=0，
即 **全局变体 `V+gap ≥ (sF−1)A` 成立**。

这正是**分组充分条件**；parity 只是其中一种划分，**任何**满足组内非负的划分都可以（最细到 place）。
若不是每组为0，则得到误差版：`f_N(total) ≥ −Σ_i f_D(G_i)`（C=Σ组 deficit）。

### 3.1 与 parity 的关系
parity 划分（v odd/even）在本数据全 12,354 成立（A1055/A1050）；由 f_D submod，这已足够推出 total；不需要 parity 的特殊结构。若换成 singleton 划分，仅在 3 条高 v 曲线失败（858k2/7014g1/8778s5），但合并后仍成立。

## 4. S1487 与真实区域集合

- S1487 是具体单/双 place 的 scalar equality 数据；没有可供子模检验的**区域集合族**；
- c1 数据只给逐 place 的 `V_p, gap_p, A_p`，故 f_L/f_N 本质可加，次模/超模都退化为等式；
- `f_D` 的非平凡 submodularity 来自 `max(0,−N)` 的结构（max of modular），不是实际 hull 区域并/交的几何次模性；
- 若要对 actual `localQrootLogVolume`/`componentVol` 的区域集合作真正子模检验，需要实际 C3/hull 区域数据；当前树/数据没有。

## 5. 结论

1. c1 的 `V/gap` 逐 place 可加：`f_L,f_N` both sub/super（等式）；
2. **deficit `f_D=max(0,−f_N)` 在本数据上严格 submodular（12,354/12,354）**，给出分组下界 `f_N(total) ≥ −Σ f_D(G_i)`；
3. 若所有组 `f_D=0`，则全局 variant 成立；parity 分组不是必需，任何划分都行（最细 place，失败高 v 曲线合并）；
4. 这是 **c1 MODEL** 的代数结构，不是 actual hull log-volume 的几何子模性证明；后者仍需实际区域数据/源引理。

## 文件
- `coord/outside_submodular.csv`（函数 × all-sub/all-super 统计）
- `coord/outside_submodular_summary.json`
- 本文件 `coord/OUTSIDE-SUBMODULAR.md`