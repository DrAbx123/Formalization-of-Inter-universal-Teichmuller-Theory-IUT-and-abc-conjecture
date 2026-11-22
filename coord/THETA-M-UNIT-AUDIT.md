# THETA-M 单位/尺度对账（david, 2026-11-17）——给 kurt/Lead 的精确展开

## 1. exact 定义

- `qVFamTensorCoefficient T b = ((qVFamily T b).order : ℝ)`（QVFamTensorCoefficientActual:76-77）；`qVFamily T b` 是 **F-位** `(nativeBadLift T).lift b` 上的 clause-B q 参数（QPilotZeroLocusDivisorActual:55-62）。`FinitePlaceQCandidate.order/exponent` = 该 completion 归一化赋值的指数（uniformizer↦1，LocalQParameter:67-80）⇒ `c_norm = ord_P(q)`（F_P 层，**不是** order/e，也非 K_w 层）。
- `actualRootCoeff b = c_norm/(2l)`（PaperLevelXiFTargetActual:67）。
- `ksThetaCoeff j = gaussExponent j · actualRootCoeff`（KSide:76）；`ksThetaHullLog b = arithmeticTupleNormalizedLogVolume (K=K_w tensor) μ (ksThetaHull b)`（KSide:135-139）。
- `arithmeticTupleNormalizedLogVolume = (1/[K_w:Q_p])·(log μS − log μ(reference))`（FinitePlaceNormalizedUnitScalingLogVolume:92-98）——**除以 [K_w:Q_p]=e_w f_w**。
- `lamWeight b = [Fmod_b:Q_p] = e_b f_b`；`dModF = [Fmod:Q]`；`thetaLamWeight b = lamWeight b/dModF`（KSide:191-203）。
- `MpaperB b = (1/[F:Q])·Σ_{P|b} f_P·c_P·log p_P /(2l)`（fiber 和；Mzk1ULOrdFiberTowerActual）+ `M_paper_v2 = Σ_b MpaperB b`。

## 2. θ 的逐 b 尺度（精确展开）

theta 区域由 q^{c_norm/(2l)} 在 K_w 的 log-shell 上缩放；`arithmeticTupleNormalizedLogVolume` 除 [K_w:Q_p]=e_w f_w，且 q 在 K_w 的 `log q_w = f_w log p` ⇒
  θ_b^{(norm)} = −(c_norm/(2l))·(f_w log p)/(e_w f_w) = −(c_norm/(2l))·log p / e_w。
其中 c_norm=ord_P(q)（F_P 层）。于是
  θ_λ b = (λ_b/d_mod)·θ_b = −(e_b f_b/d_mod)·(ord_P/(2l))·logp/e_w。

## 3. 与 MpaperB 的比较

MpaperB = (1/[F:Q])·Σ_{P|b} f_P·ord_P·logp/(2l) = (1/d_mod)·(1/[F:Fmod])·Σ_{P|b} f_P ord_P·logp/(2l)（用 [F:Q]=[F:Fmod][Fmod:Q]）。
θ_λ b 与 MpaperB 的比 = (e_b f_b e_w^{-1}·d_mod? )/(Σ_{P|b} f_P ord_P/[F:Fmod])·ord_P … 不是常数：
- 若坏位 away from l（K_w/F_P 无分歧，e_{w|P}=1）、且 F/Fmod 无分歧（e_{P|b}=1, Σ f_P = f_b[F:Fmod]）⇒ θ_λ b 系数 = f_b/(d_mod e_b)·ord_P，MpaperB 系数 = (1/(2l d_mod))·(f_b[F:Fmod]/[F:Fmod])ord_P = f_b ord_P/(2l d_mod) ⇒ 相等（除 e_b=1 时）。
- 一般情况 θ_λ b 与 MpaperB 差 `e_{w|P} f_b e_b` 类因子；**θ 用单选定 lift，M 是全 F-fiber 平均**，两者无统一常数等式。
⇒ kurt 的担忧成立：当前定义下 θ_λ ≈ −(factor)·M_b，factor 一般 ≠1；**不能断言 −M ≤ θ_λ**（若 θ 更负则方向反）。

## 4. 修复选项（给 Lead/kurt 裁）

1. **θ 系数改为 c_norm/(e_w·2l)** 或把 c_norm 定义为 Fmod 层 `ord_b`（=ord_P/e_{P|b}）：消去 e_w 因子，但 f_b 与 fiber 平均仍不匹配（θ 单 lift vs M 全 fiber）。
2. **F-side θ hull**（λ 权 + 每 F-位/全 fiber 求和）：使 θ_λ 与 MpaperB 同 fiber 结构；这是 (B) 的完整做法（kurt 的 F-side 重建）。
3. **J1-M 质量路线**：不依赖 θ_λ 的 log-shell 单位，直接用 Kummer 质量 `(1/2l)log|q|=log|r|` + 区域包含给出 `-M≤θ`（kurt 正解）；当前 θ 定义只用于 H_pkt upper（C3），不强行承担 C2 lower。

结论：**C2 lower 不应从当前 θ_λ（K-side selected lift）取 -M≤θ**；C3 upper 的 θ≤H_pkt 用 λ 权，H_pkt 与 θ 同域/同尺度即可（已核）。θ 的 coefficient 若保留 c_norm/(2l)，必须同时按 e_w 归一（选项 1）才能与 paper H_pkt 的 λ 权一致；或走选项 2/3。