# OUR-N5-NUMERIC — CTheta/hscalar 数值核对与 N5Weak 差距

日期：2026-11-13；qpilot（A1043）。**仅 Python**；只读 Lean 定义，不编译。

## 1. 读到的定义

- `S3034PacketScalarBoundActual.S3034Hscalar`：定义为 `S3025MissingThetaUpperScalar`，其 iff 形式为
  `-actualC3LogShellTensorLogVolume ≤ CThetaPaper ℓ logQ ... * paperQAbsLog ℓ logQ`；
- `S3016CThetaUpperActual.S3016CThetaUpperInterface.upper`：`thetaSigned ≤ cthetaPaper * |stepVLogMagnitude|`（**上界方向**）；
- `CThetaPaper`（S2715）：`((ℓ+1)/4 / paperQAbsLog) * cThetaBracket − 1`，`paperQAbsLog=logQ/(2ℓ)`；
- `cThetaBracket`（S2691:103）：`(1+12 dmod/ℓ)(log dFpd+log fFpd)+10(eStar*ℓ+etaPrm) − (1/6)(1−12/ℓ²)logQ`；
- `actualC3LogShellTensorLogVolume`（C3LogShellTensorPacketActual:107）：C3 张量 log-shell 区域的实际 Haar log-volume；
- `N5Weak`（Mzk1N5WeakSkeletonActual:31）：`-A - C ≤ rhs`；`N5Weak 0` 即 `-A ≤ rhs`；`M=A+rhs`；
- S3018 公式：`actualC3LogShellTensorLogVolume = profileArithmeticDegree (local haarLogVolume actualC3LogShell)`，本身不是上界。

## 2. 与 c1 数据对齐的尝试

用 `coord/c1_local_terms_e_exact.jsonl` 的 admissible 2604 条（ℓ=5）构造 **proxy**：
```
A_proxy = Σ_{p>3,p≠ℓ} v_p logp/(2ℓ)     （= absLogQ）
V_proxy = arch + H_tame                    （c1 hull volume proxy）
gap_proxy = Ind2；M_proxy = V+gap−T；rhs_proxy = M−A
```

| 量 | min | median | max |
|---|---:|---:|---:|
| A_proxy | 0.194591 | 0.828677 | 5.626183 |
| V_proxy | 4.481057 | 12.010887 | 13.955158 |
| M_proxy | 5.016183 | 14.852725 | 20.375478 |
| rhs_proxy | 4.011957 | 13.816080 | 18.859236 |

- `M_proxy ≥ 0`：2604/2604；因此 **N5Weak0 proxy（−A≤rhs）全成立**；
- `V_proxy>0`，故 `−V_proxy<0`。若 `CThetaPaper≥0`，S3034 的上界 `−V≤CThetaPaper·A` **自动成立**（LHS 负，RHS 非负），不提供 N5Weak 所需正下界；
- 若 `CThetaPaper<0`，RHS 为负，S3034 上界可以非平凡；但 `CThetaPaper` 的符号依赖 dmod/dFpd/fFpd/eStar/eta，当前数据没有这些量；
- S3045 已给出实际 `CThetaPaper<0` 的具体例子（dmod=0 等），所以不能假设 CThetaPaper≥0。

## 3. 不能直接数值比较的原因（缺失量）

| 缺失量 | 用途 | 现状 |
|---|---|---|
| 实际 `actualC3LogShellTensorLogVolume` / `actualC3LogShell` 局部 Haar 体积 + `profileArithmeticDegree` 权重 | S3034 的 V_C3 | c1 的 `V_proxy` 是 `logVol(hull(vcI))`，不是 C3 tensor log-shell；S3018 只给 formula，无数值 |
| `dmod, dFpd, fFpd, eStar, etaPrm` | 计算 `CThetaPaper` | 不在 c1/S1487；dFpd 是 Gaussian different 的 norm，fFpd 是 ABC support ideal 的 abs norm；需 actual S2990/S2752 数据 |
| 实际 `logQ` 或 `A=absLogQ`（C3 侧） | hscalar RHS | c1 的 A 是局部 q-pilot 的模型，不等于 C3 侧的 paper logQ；S3016 的 StepV=global q-pilot 识别尚未证 |
| 实际 `rhs`（thetaSigned / −|logTheta|） | N5Weak 的下界 | c1 `M_proxy= A+rhs_proxy` 是 MODEL；实际 theta hull 的 rhs 未给 |
| S3016 identification `S3016StepVQPilot = S3016WeightedGlobalQPilot` | 把 C3 与 q-pilot 对齐 | 是 interface 字段/target，未证明；不能数值代入 |

## 4. 方向上能说什么

1. **S3034Hscalar 是上界**：`−V_C3 ≤ CThetaPaper·A`；N5Weak0 需要的是 `−A ≤ rhs`（等价 `M≥0`）。上界不能推出下界；S3016 的 `thetaSigned ≤ cThetaPaper*|stepVLog|` 也是上界方向。
2. 在 c1 proxy 中 `M_proxy≥0` 全成立，故 **N5Weak0 的 proxy 数值成立**；但这只是 MODEL，不是 actual C3/theta hull 的 N5Weak。
3. 若 `CThetaPaper≥0`，S3034 上界因 `−V_C3<0` 自动成立（只要 V>0），因此该上界**不检验 N5Weak**；真正的缺口是实际 theta-hull 的**下界/符号**与 C3 体积数值。
4. 若 `CThetaPaper<0`，上界非平凡，但 S3045 表明存在负值情形；需要实际参数才能判断。

## 5. 若要数值测试 N5Weak 需要补的量

1. `actualC3LogShellTensorLogVolume` 的数值（C3 tensor 局部 Haar 体积 + profile 权重）；
2. `CThetaPaper` 的五个参数（dmod,dFpd,fFpd,eStar,etaPrm）的实际数值；
3. actual `rhs = -|logTheta|`（thetaSigned）或 `M_actual=A+rhs`；
4. S3016 的 `stepVLogMagnitude=globalLogMagnitude` 识别（或独立算 C3 侧 A）；
5. 若要走 S3034：还需 `actualC3LogShellTensorLogVolume` 的精确局部体积；若要走 N5Weak：需要 theta-hull 的**下界**（不是 S3034 的上界）。

## 6. 结论

**当前 c1 数据只能给出 proxy：A/V/M/rhs 与 N5Weak0 proxy 全正，但不能计算 actual `−V_C3` 与 `CThetaPaper·A`。**
S3034/S3016 都是上界方向，不能替代 N5Weak 的下界；需补 actual C3 体积、CThetaPaper 五参数、actual theta rhs（及 S3016 识别）才能做真实数值测试。

## 文件
- `coord/our_n5_numeric.csv`（2604 admissible：N,label,A,V,gap,T,M,rhs,minusV,n5_margin）
- 本文件 `coord/OUR-N5-NUMERIC.md`