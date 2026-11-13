# Cor 3.12 体积下界 → log q / theta 比较：精确路径（2026-11-14）

## 0. 精确外部陈述（Dupuy–Hilado，arXiv:2004.13228 / ar5iv HTML 已 fetch）
Mochizuki 不等式（Cor 3.12）为
```
  −deg_hat(P_q)  ≤  −deg_hat_lgp(P_hull(U_Θ))        (1.1)
  U_Θ = Ind2·(Ind1·(O_L(−P_Θ))^{Ind3})                (1.2)
```
其中 `deg_hat`/`deg_hat_lgp` 通过 log-volume `lnν` 对应；Dupuy–Hilado 明确：
- `lnν_L(hull(U_Θ)) = −deg_hat_lgp(P_hull(U_Θ))`；
- **log-volume 不是体积的对数，而是归一化 p-adic/arch Haar 测度对数的加权平均**：
  `lnν_{L_p}(A_p) = E( ln μ_v(A_v) / dim(L_v) )`（对随机样本空间/位置元组取期望，再对 p 求和）。

## 1. 我们已有的体积下界（green）
`Mzk1RouteC0RootQLatticeActual`（olean True，11:49:40Z DONE）：
- `c0QHat_eq_q`：`qhat_b = α_b^(2l) = algebraMap(q)`；
- `c0Alpha_norm_le_one`；`c0Alpha_pow_sub_one_mem`；
- `c0QLattice ⊆ c0HLattice`（单块）；`c0ProductQ ⊆ c0ProductH`（product）；
- `c0ProductHaar_mono : μ(c0ProductQ) ≤ μ(c0ProductH)`；
- `c0Remainder_nonneg : 0 ≤ (2l−1)·Σ_b d_b·(−log‖α_b‖)`（显式余量）。

即 **体积下界已经在 root 层被证明**（且显式余量 ≥0，无比较假设）。

## 2. 缺口：把集合/测度比较翻译成 log q 与 theta 读数
需要三条识别（均为可执行任务，不是新假设）：
1. **q 侧**：`log μ(c0ProductQ)`（按 Dupuy–Hilado 的归一化：除以维数、p-平均）应等于 q-pilot 的 `−deg_hat(P_q)`，即 native q readout 的归一化形式；
2. **theta 侧**：`hull(U_Θ)` 在 `Ind1/Ind2/Ind3` 下的像的实际 Haar 测度（或以 `qVFamTensorPlaces` 的 tensor 测度），对应 `−deg_hat_lgp(P_hull(U_Θ))`；native 侧为 `nativeThetaReadout`；
3. **归一化/procession**：Dupuy–Hilado 的 `E(ln μ/dim)` 平均值与我们的 `nativeTensorLogVolume`、`p2WeightedDetLog`、procession 平均的对应；有限/坏位块、arch 位置的权重；以及 product(∏) 与 tensor(⊗) 载体的桥（P3 `p2NativeProductBlockMissing`）。

## 3. 路线
- 用 green 的 `c0ProductHaar_mono`（`log μ(Q) ≤ log μ(H)`）；
- 用 det-Haar 缩放律（qpilot 的 class-B 外部输入，正在被 TauCeti port 替代）把每块 `log μ(qhat_b·O_b)` 化为 `d_b·log‖qhat_b‖ + log μ(O_b)`；
- 用 Dupuy–Hilado 的归一化公式把 `log μ(Q)`/`log μ(H)` 化为 `−deg_hat(P_q)`/`−deg_hat_lgp(P_hull(UΘ))`（除维数+p-平均、Ind/procession 平均）；
- 得 `nativeQReadout ≤ nativeThetaReadout`（或 `Paper312Statement`），**无需 `thetaR13Defect=0`**。

## 4. 文献结论
- Dupuy–Hilado 给出 (1.1)(1.2) 的精确陈述和 initial theta data 可计算性；**明确 log-volume 是归一化平均，不是 log 体积**——这直接指导我们修正 native readout 的归一化。
- Zenodo 的 'Forensic Diagnosis' 等文只是分析/争议，不可作为证明输入。
- 没有任何外部定理能直接给出 (1.1) 的证明；路径必须自己走：root 格包含（已证）+ 归一化识别（待做）。
