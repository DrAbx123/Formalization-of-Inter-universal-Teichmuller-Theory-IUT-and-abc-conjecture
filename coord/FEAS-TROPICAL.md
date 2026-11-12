# FEAS-TROPICAL — tropical/离散凸可行性分析

日期：2026-11-13；qpilot（A1093）。**仅 Python**；数据 N≤9999 admissible 12,354；未跑 Lean。

## 1. 集合函数

对 bad place 集合 S：
```
f_L(S)=Σ_{p∈S}(V_p+gap_p)
f_N(S)=f_L(S)−(sF−1)Σ_{p∈S}A_p
f_D(S)=max(0,−f_N(S))
```

## 2. 判定 A/B/C（本报告定义）

- **A**：目标就是某个**已证**离散凸不等式（Lovász/M-凸/L-凸）的直接实例；
- **B**：目标可由「已证不等式 + 一个具体结构引理」推出；
- **C**：目标不能由这些结构推出（或需要额外分析命题）。

## 3. 数值/结构结果

| 函数 | 结构 | sub/super | 凸性 | 数值证据 |
|---|---|---|---|---|
| f_L | modular（可加） | 全 sub=全 super（等号） | Lovász 线性；M/L 凸平凡 | 12,354/12,354；0/179,970 Lovász 违例 |
| f_N | modular | 全 sub=全 super | 同上 | 0/179,970 |
| f_D=max(0,−f_N) | **disjoint-subadditive**（A1086） | **非全局 submodular** | Lovász 型凸性**不成立** | **6/179,970** Lovász 凸性违例 |

（Lovász screening：每曲线随机 x,y∈[0,1]^m 与 λ=.25/.5/.75，共179,970 个测试；f_L/f_N 0违例；f_D 6违例。）

## 4. 为什么不能直接套 Lovász/M-凸

- f_L,f_N 是**可加（modular）**函数；Lovász 扩展是线性，M/L 凸性平凡成立，但**这不能推出 `f_N(total)≥0`**：modular 函数的线性项符号可正可负；
- f_D 只在 disjoint A,B 上满足 subadditivity（A1086），但**不满足全 submodularity**；Lovász 扩展凸性需要全 submodular，6 个数值违例已足够否定；
- 因此 exact target 不是 Lovász/M-凸/L-凸的直接实例。

## 5. 判定

- **exact target（N≥0）**：**C**。没有已证离散凸不等式直接蕴含它；
- **分组/误差版**：**B**。若实际 log-volume 函数 f 具备（a）全局 submodularity 或 L-凸性，且（b）每个分组 G 有 f_D(G)=0，则
  ```
  f_D(total) ≤ Σ f_D(G_i) = 0  ⇒  f_N(total) ≥ 0
  ```
  这是 B 型：需要一个实际几何/区域函数的 submodularity 结构引理 + 分组零 deficit；c1 proxy 只支持 disjoint subadditivity，不是全局 submodular；
- 若只想利用 **modular f_L/f_N**，目标变成纯线性不等式，不属于离散凸分析（A 不成立）；
- **C 的精确边界**：需要 actual hull log-volume 的全局 submodular/L-凸结构，而当前 c1 数据没有（f_D 已有反例）。

## 6. 所需结构（若要把判定从 C/B 提升）

1. 实际区域函数 `f(S)=logVol(∪_{p∈S} region_p)`（或 hull）的**全局 submodularity**，不是仅 disjoint subadditivity；
2. 或 L-凸/M-凸的 exchange 公理在 actual region 数据上成立；
3. 对 grouped sufficient condition，需要分组 `f_D(G)=0`（组内 `V+gap≥(sF−1)A`）；
4. 对 exact target 还需把 `f_N(total)≥0` 与这些凸性结构桥接；当前没有。

## 7. 结论

| 目标版本 | 判定 | 依据 |
|---|---|---|
| exact N≥0 | **C** | 无已证离散凸不等式蕴含；modular 平凡、f_D 非全 submodular |
| grouped f_D(G)=0 ⇒ N≥0 | **B** | 需要 actual global submodularity/L-凸 + 分组零 deficit |
| Lovász 扩展凸性本身 | 仅 f_L/f_N（trivial linear）；f_D 不满足 | 0/179,970 vs 6/179,970 |

**判定：exact = C；grouped/error = B（条件性）。** 数值不支持 f_D 的全局 Lovász 凸性；唯一的凸性结构是 modular f_L/f_N（平凡），不足以推出目标。

## 文件
- `coord/feas_tropical.csv`（函数 × 结构 × Lovász 数值）
- 本文件 `coord/FEAS-TROPICAL.md`