# david lane 显式参数清单审计（2026-11-17 恢复）

所有 h 参数一律记**待消义务**，不计中间节点闭合。

## A. C4/hstepVIII 链
| 参数 | 出现处 | 等价未证对象 | owner | 真实构造计划 |
|---|---|---|---|---|
| `hstepVIII` | Mzk1UCC4PaperActual.uc_c4_actual_paper_letters / uc_c4_of_paperConstants | paper Step(viii) 不等式的实际证明（含 θ≤H_pkt 的 λ 权版本） | david+kurt | 用 kurt `hstepVIII_of_paperLetters_gen` + david λ 字母（HlogKLambdaData/HsQrawLambdaData）实例化；V=urPacketV_K_M、Q=qPilotMagnitudePaper_v2、M=M_paper_v2 |
| `hP5` | Mzk1UCC4PaperActual / Mzk1URC2AssemblyActual | `-M_paper_v2 ≤ θ`（C2 lower） | kurt | J1 theta-source hull 新对象：qRootLattice⊆thetaSourceHull（per-fiber mass = -M_b，用 fiber_sum_ef + MpaperB_eq_ordB）+ thetaSourceHull⊆packetHull；现行 θ 不承担 |
| `htheta` | 同上 | `θ ≤ H_pkt`（C2 upper） | kurt | λ 权 hull：`ksThetaHullLogRoot_lam_le_ucWeightedHpkt_lam`（adapter），V 需与 θ 同尺度（V_M 的 ksThetaHullLog≤V_M 仍待重证） |
| `hC4` | andrew d4_of_c4_qscale | `c_l Q ≤ A`（C4 boxed） | andrew/david | 由 uc_c4_actual_paper_letters 的 hstepVIII+hP5+htheta 消去 M 得到；Q 用 v2=Q_all |
| `S_ar` 实际值 | uc_c4_actual_paper_letters | `logDifferentF + logConductorFActual`（F 版） | sophie | `SAr_tripodal` 已换 canonical logConductorFActual；`log_rootDiscr_eq_add` + absolute conductor 数据 |

## B. hlogK / hsQ（C3-upper 字母，关键路径）
| 参数 | 出现处 | 等价未证对象 | owner | 构造函数 |
|---|---|---|---|---|
| `hlogdK_λ` | Mzk1ULHlogKHSULambdaStatementsActual.HlogKLambdaData | `Σ_b w_b D_b ≤ S_ar+2log l+21`（paper L1425） | david | D_b=log dK 的 per-b 分解待定义（K-side per-place log different）；SerreWild count 端 + tower 恒等式；21 常数已有（DiscrAssembly 21） |
| `hsQraw_λ` | HsQrawLambdaData | `(Σ w)·log s≤ ≤ 2d_mod S_ar+5+log l`（L1572） | david | sQOf + absolute `localConductorData` per-place 界 + `paperLstarLogs` bound（hprime_paperConstants）；需先定义 log s≤=Σ log p over dst |
| `hprime` | Mzk1ULHpktActual.ul_hpaper_of_stepVIII | `paperLstarLogs ≤ (4/3)paperEar` | andrew | 已证薄实例 `hprime_paperLstarLogs_le`（hprime_paperConstants + etaPrm） |
| `hconst` | 同上 | `2log l+56 ≤ (4/9)E_ar` | andrew | `ul_hconst_of_paperConstants`（已备） |

## C. ord/mass 子链（J1-M）
| 参数 | 出现处 | 等价未证对象 | owner | 构造 |
|---|---|---|---|---|
| `ord_algebraMap_eq_e_mul_ord` | Mzk1ULOrdTowerActual | `ord_P(algebraMap q)=e_P·ord_b(q)` 主理想版 | david | `Ideal.map_span`+`Ideal.map_pow`+`ramificationIdx'_eq_normalizedFactors_count`+`localOrderAt_map_pow`；已写，待编译 |
| `MpaperB_eq_ordB` | Mzk1ULThetaMassTelescopeActual | `MpaperB b = (1/2l)(1/[Fmod:Q])ord_b logp` | david | 输入 `Σ_{P|b}f_P c_P=[F:Fmod]ord_b`（ord tower 结论）+ `hlog`（同 p 的 log）；fiber_sum_ef + finrank 塔 |
| `fiber_sum_ef` | Mzk1ULFiberSumActual | `Σ e_P f_P=[F:Fmod]` | david | Mathlib `Ideal.sum_ramification_inertia`（binder 已 probe 确认）；待编译 |
| `thetaMWeight` | Mzk1ULThetaMWeightActual | θ_M 权重 1/(λ_b e_P)，d_mod 在分母 | david | DONE 00:48:22（乘法恒等式已证） |
| `V_M` 重证 | Mzk1ULThetaMWeightActual.urPacketV_K_M | `ksThetaHullLog≤V_M` 与 `hVB: V_M≤B` | david+kurt | 由 V=urPacketV_K 的逐项等式 + 除 eFiber 单调性；需与 kurt 的 hperB 同批 |

## D. hcond / Legendre
| 参数 | 出现处 | 等价未证对象 | owner | 构造 |
|---|---|---|---|---|
| `perPlace_bound` | Mzk1ULHcondChainActual.LegendreTpdSupport | `log f_Ftpd ≤ log N_D(λ)+log2Const`（同域逐位） | david+sophie | Legendre 相等（tripodalFieldOf=FtpdLam=Q(λ)）+ support 包含（16λ²(1−λ)² ⇒ bad ⊆ {λ bad}∪{2}）+ truncation 逐位 |
| `tpd_subset`/`q_subset_point` | LegendreSupportIncl | support 包含数据 | david | Legendre 判别式 + q-support 定义；`tpd_subset_point_of` DONE |
| Legendre 4 声明 | Mzk1ULLegendreTwoTorsionActual | 2-torsion 桥接（正/反向） | david | add_self_of_Y_eq/ne + some_ne_zero + 二次多项式；待编译 |

## E. Q/M 口径
- Q=`qPilotMagnitudePaper_v2`（1/[F:Q]+f_P 权，DONE 21:55:33）；M=`M_paper_v2`=Q/(2l)；per-b 分解 `M_paper_v2_eq_sum_MpaperB`/Qb 两件（david，待编译）。
- `actualQPilotMagnitudeClassical`/`qPilotMagnitudePaper` 标 LEGACY（审计 §4：与 v2 差 f/e 因子）。
- J1-M 目标 `-M_paper_v2≤θ_λ`；`urPacketV_K_M`/`thetaMWeight_mul_thetaLamWeight` 已给 d_mod 在分母的权重；V_M 的 KSide hull 不等式待重证。