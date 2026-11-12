# PER-CAPSULE-CHECK — per-capsule 充分条件数值验证

日期：2026-11-12；qpilot（A1009）。**仅 Python**；输入 `coord/c1_local_terms_e_exact.jsonl`（精确 e=2ℓ + T/nC）。

## 1. 归一化（abc `DECOMP-NORMALIZATION.md` + lana 源）

- `A := absLogQ = logQ/(2ℓ)`：**无 1/nC**（LeftHandSide:81-88；logQ 只含 place weight，sum weight=1）；
- `V=logVol(hull(vcI))=(1/nC)Σ_iΣ_v hullPacket_i(v)`（VcI:741-744）；
- `gap=(1/nC)Σ_iΣ_v gapHullAt_i(v)`（Gap:895-898, 957-961）；
- `rhs`/`R` 的 1/nC 来自 `processionVol=(1/nC)Σ_i globalVol`（LogVolume:200-209）；label 权重在 `packetWeight`（LogVolume:130-150）；
- **唯一正确展开**：`M = A + (1/nC)Σ_i H_i = (1/nC)Σ_i (A + H_i)`，A 只计一次；
- 充分条件：`∀ i, 0 ≤ A + H_i`；
- 逐位 q-side：`T_p=(sF−1) A_p`，`A_p=weight_p·ord_p(q)logp/(2ℓ)`；per-capsule 展开中 q 侧 T 带 **1/nC**（T/nC per capsule；不除 T 会重复 nC 次，见 abc §5）。

**数据公式**：e=2ℓ=10（坏乘法位，ℓ∤v_p(q)）；`H_p=Σ_{j=1..nC}(1−1/e)logp=nC·(1−1/(2ℓ))logp`；`Ind2_p=Σ_j frac(j²v_p(q)/(2ℓ))logp`；p=2,3 wild 保留原 H×nC；p=ℓ 剔除。`A=nC·(Σ_p T_p)/(sF−1)`（因输入的 T_p 已含 T/nC；nC=2, sF=2.5）。

## 2. 计算设定与模型限制

c1 计算器是**单 label、uniform capsule 模型**：没有非平凡 label packet 的逐 capsule 区分，只有 `j=1,2` 两个局部 j 项。因此做两种检查：

1. **uniform capsule（与 M 恒等式一致）**：所有 capsule 局部项相同，取 `H_i = M − A`（i=1,2）；则 `A+H_i = M`。
2. **strict j-split**：把 hull/gap 的 j 项分给 capsule i=j：
```
local_i = arch_i + Σ_p [ (1−1/e)logp + frac(i² v_p(q)/(2ℓ))logp ]   (i=1,2)
H_i = local_i − T/nC   (T/nC 为 per-capsule q-side；T = Σ_p T_p 已是 T_global/nC)
A + H_i = A + local_i − T
```
其中 `arch_1=arch_defect(2)=0.1732868`, `arch_2=arch_defect(3)=0.3972567`。

## 3. 结果（admissible 2604）

### 3.1 uniform capsule（主恒等式）
| 量 | value |
|---|---|
| 样本 | 2604 admissible × 2 capsules = 5208 个值 |
| min | **5.301454** |
| max | 20.660750 |
| median | 15.137997 |
| <0 | **0** |
| 分位 1%/5%/25%/50%/75%/95%/99% | 7.192 / 10.237 / 13.680 / 15.136 / 16.313 / 17.952 / 19.160 |

### 3.2 strict j-split（更强/更严格）
| capsule | min | max | median | <0 | q01/q05/q25/q50/q75/q95/q99 |
|---|---|---|---|---|---|
| i=1 | **2.514418** | 11.291823 | 7.158463 | **0** | 3.535/4.791/6.461/7.155/7.852/9.085/9.843 |
| i=2 | **3.030275** | 13.664374 | 9.059027 | **0** | 4.299/6.050/8.124/9.059/10.035/11.532/12.462 |

**admissible 2604 条：两种定义下所有 per-capsule 值均 ≥0，无 <0 项。** 因此数值上支持充分条件 `∀i, 0≤A+H_i`（在 c1 模型与上述 split 下）。

## 4. 858k2（p=13, v=21）

数据：`A=5.626183`；`Σ H=11.376356`；`Σ Ind2=2.481422`；`Σ T=4.219637`（T_global/nC）；`M=9.923412`。

| 定义 | i=1 | i=2 |
|---|---|---|
| uniform `A+H_i=M` | **9.923412** | **9.923412** |
| strict j-split | **7.621659** | **9.334482** |

858k2 在两种 per-capsule 定义下均为正（最小 7.62），不再是负项；在 T/nC 归一化下其 per-capsule 充分条件成立。

## 5. 结论与 caveat

1. 按 abc 归一化（A 无 1/nC；V/gap/rhs 带 procession 1/nC；T/nC per capsule），对 admissible 2604 条、两种合理的 per-capsule 定义，**所有 A+H_i ≥0**：uniform min=5.301；strict j-split min=2.514（i=1）/3.030（i=2）。
2. 858k2 的 per-capsule 值为正：uniform 9.923；j-split 7.622/9.334。
3. 因此数值支持 per-capsule 充分条件；若该条件可证（`∀i, 0≤A+H_i`），则 `M≥0`（abc Lean 草案 `M_nonneg_of_perCapsule`）。
4. **caveat**：c1 是 MODEL-PAPER，单 label/uniform capsule；真正的 label packet 权重与非平凡 capsule 差异未进入数据。strict j-split 只是把 j=1,2 局部项分给两个 capsule 的模型选择，不是 lana 的精确 label packet。
5. 未做 Lean 编译；数值结论不是证明。

## 文件
- `coord/per_capsule_check.csv`（4154 行：N,label,admissible,A,M,uniform1/2,jsplit1/2）
- 本文件 `coord/PER-CAPSULE-CHECK.md`