# EXTERNAL-PORT-REGISTRY（canonical 外部移植归属；owner: qpilot）

更新: 2026-11-10 18:52。registry frozen 14041（tauceti_belyi_core canonical root 已登记，见 §2 表与 §11/§12）。任何 stream 只从本 registry 的 canonical 路径 import，
不再各自 port 同一外部模块（尤其 FLT RiemannRochRows/SerrePairing/SmoothProperCurveFiniteMapData/
CechSectionsOfDivisor）。重复件由 owner 通知停用。

## 1. 源资产（只读克隆，Apache-2.0，attribution 保留在 ported 文件头）
- FLT: https://github.com/anthropics/fermats-last-theorem @ 6e837e75（lean 4.33.1 / mathlib db584cd6）
  本地: tmp/external/flt-lean
- TauCeti: 本地 tmp/TauCeti（Apache-2.0，lean 4.36.0-rc1 / mathlib 2cabef97）

## 2. Canonical ported 目录（按目标闭包）
| 目标 | canonical 目录 | 来源 | 闭包 | 状态 |
|---|---|---|---|---|
| FLT SerrePairing bijective/flip + weilDualityAdelic + cechRiemannRoch + SmoothProperCurveFiniteMapData | tmp/external/ported/flt_core | flt, xif_quickport targets: P2M/Sol/S_AlgebraicCurve_serrePairing_bijective_and_flip_bijective.lean; P2M/Sol/S_AlgebraicCurve_weilDualityAdelic_of_isAlgClosed.lean; P2M/Sol/S_AlgebraicCurve_cechRiemannRoch_of_genusReached.lean; Definitions/Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData.lean | 234 files | ported，feeder 喂编译中 |
| FLT canonical divisor / Kaehler / RR-space / transcendental layer | tmp/external/ported/flt_test | flt, targets: P2M/Sol/S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean; S_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_isCurveOver_of_essFiniteType.lean; Definitions/Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData.lean | 224 files | 编译中（Kaher/transcendental 层已 EXIT=0） |
| TauCeti RiemannRoch（Pencil/Genus/Basic）+ Differential/CanonicalDivisor + WeilDivisor/Scheme/SerreDuality + Belyi/Basic | tmp/external/ported/tauceti_rr | tauceti, targets: TauCeti/FieldTheory/FunctionField/RiemannRoch/{Pencil,Genus,Basic}.lean; TauCeti/FieldTheory/FunctionField/Differential/CanonicalDivisor.lean; TauCeti/AlgebraicGeometry/WeilDivisor/Scheme/SerreDuality.lean; TauCeti/FieldTheory/FunctionField/Belyi/Basic.lean | 263 files | ported，feeder 喂编译中 |
| TauCeti CriticalValues + Belyi + AbcConjecture（Belyification + final abc form） | tmp/external/ported/tauceti_belyi_core | tauceti, targets: TauCeti/Algebra/Polynomial/{CriticalValues,Belyi}.lean; TauCeti/NumberTheory/AbcConjecture.lean | 6 files | ported CITABLE（3 modules：CriticalValues 13 decls / Belyi 13 / AbcConjecture 8；checker probe_ok；sha 6D3B5143…/9948742A…/B6336589…） |
| TauCeti 旧全量闭包（legacy；新目标用 tauceti_rr） | tmp/external/ported/tauceti2 | Lead 早期 264-file 闭包 | 264 files | 60+ OK / 46 missing-dep 待喂 |
| FLT 旧 flat/th 闭包（legacy；目标用 flt_core/flt_test） | tmp/external/ported/{flt,flt_th} | 早期 port | 19/239 files | 部分编译 |

## 3. 已提升的一等适配层（checker CITABLE；import 直接引用这些）
| 文件 | 声明 | checker |
|---|---|---|
| tmp/sheaf/xif/paper/AG00MathlibAuditActual.lean | AGCapability/AGMathlibCapabilities + 14 行能力矩阵 rfl 事实 | CITABLE 13 decls probe_ok |
| tmp/sheaf/xif/paper/AG00bFLTAssetAuditActual.lean | FLTAssets（模块→AG 层映射）+ rfl 事实 | EXIT0 |
| tmp/sheaf/xif/paper/AG01CurveFoundationsActual.lean | S3133CurveOver（IsProper+Smooth+SmoothOfRelativeDimension 1+GeometricallyConnected over Spec k）+ 4 projection 定理 | CITABLE 5 decls probe_ok |
| tmp/sheaf/xif/paper/AG02GenusActual.lean | S3133GenusInterface / S3133Genus / S3133GenusCohomologyTarget | CITABLE 4 decls probe_ok |
| tmp/sheaf/xif/paper/AG_FLT_Def_AlgebraicCurve_DivisorClassGroup.lean | AlgebraicCurve.Place/Divisor/degree/degZero/IsPrincipal/principal/Pic/Pic0（72 decls；Apache-2.0 attribution） | CITABLE 72 decls probe_ok |
| tmp/sheaf/xif/paper/AG_FLT_Def_AlgebraicCurve_Repartitions.lean | repartitions 基础（依赖 DivisorClassGroup） | EXIT0 |
| tmp/sheaf/xif/paper/AG_FLT_Def_AlgebraicCurve_AdelicIndex.lean | AlgebraicCurve.LSpace/ell/adeleBdd/adeleSpace/globalSub（68 decls） | CITABLE 68 decls probe_ok |
| tmp/sheaf/xif/paper/AG_FLT_Def_AlgebraicGeometry_CoherentBaseChange.lean | CoherentBaseChange | EXIT0 |
| tmp/sheaf/xif/paper/AG_FLT_PromotionActual.lean | promotion_place_deg_nonneg, promotion_degree_add/zero, promotion_mem_degZero_iff, promotion_isPrincipal_iff_mem, promotion_ell_nonneg, promotion_lSpace_mono, promotion_adeleBdd_mono | CITABLE 8 decls probe_ok |
| tmp/sheaf/xif/paper/AG_FLT_Def_AlgebraicCurve_CechSectionsOfDivisor.lean | lSpaceOn/cechDiff/cechH0/cechH1/H1（改编，CANONICAL Cech 适配；入队待看门狗；stepxi AG05 依赖它） | 待编译 |

## 4. 去重决定
- 停用/勿引用: tmp/external/ported/stepxiAGRRFinishActual（stepxi 自 port 的 FLT RR/Serde 闭包）→ 改用 flt_core（绿后 AG_FLT promotion）。
- 其他 stream 的 flt_rr_serre 等若与本 registry 目标重叠，以 flt_core/flt_test/tauceti_rr 为准。
- CechSectionsOfDivisor 唯一 canonical 适配 = tmp/sheaf/xif/paper/AG_FLT_Def_AlgebraicCurve_CechSectionsOfDivisor.lean（另 port 副本仅作调试，不作为 import 目标）。
- 提升层命名: AG_FLT_*（FLT 来源）/ AG_TAUCETI_*（TauCeti 来源，绿后建）。import 路径: tmp.sheaf.xif.paper.<文件名去 .lean>。

## 5. 状态与下一步（每批更新）
- 2026-11-10 06:35: flt_core 234 files ported+fed；tauceti_rr 263 ported+fed 24；flt_test 23 OK；tauceti2 63 OK/49 missing-dep 重试中。
- 下一步: flt_core/tauceti_rr 首个目标文件绿 -> 建 AG_FLT_RiemannRochPromotionActual / AG_TAUCETI_RiemannRochPromotionActual（re-export 主 RR、SerdeDuality、Belyi Existence、FiniteMapData 声明）+ probe；每声明报告"是否无 sorry 完整证明"（检查 adapted/ported 源文件无 sorry，probe trio）。

## 6. 追加（2026-11-10 07:05）
- FiniteMapData canonical import = tmp.external.ported.flt_th.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData（EXIT=0，Apache-2.0 header）。直接 import 该模块即可；另有 AG_FLT_FiniteMapDataPromotionActual 包装尝试因 SchemeHomOver binder 的 parser 报错未成，不作为 canonical（勿引用）。
- RR/Serde promotion canonical = tmp/sheaf/xif/paper/AG_FLT_RiemannRochPromotionActual.lean（checker CITABLE 8 decls probe_ok；六行 RR 陈述 + 两个完整归约证明，ported flt/flt_th 子树 sorry/axiom grep = 0）。
- Cech canonical = AG_FLT_CechPromotionActual（checker CITABLE 5 decls）+ AG_FLT_CechSectionsActual + AG_FLT_TwoChartCechActual（均 EXIT=0）。

## 7. 追加（2026-11-10 07:15）
- Canonical divisor / genus canonical import = tmp/sheaf/xif/paper/AG_FLT_CanonicalDivisorPromotionActual.lean
  （checker CITABLE 3 decls probe_ok；imports flt_test canonical divisor + two Theorems；Apache-2.0）。
  Decls: promotion_canonicalDivisorOf (def), promotion_canonicalDivisorOf_apply (COMPLETE proof),
  promotion_canonicalClass (def), promotion_genus (def),
  promotion_ell_canonicalDivisor_eq_genus_of_riemannRoch (COMPLETE proof, conditional on RR rows + constants base),
  promotion_degree_canonicalDivisor_eq_of_riemannRoch (COMPLETE proof, same conditions).
- Port-root duplicate warning: flt_core and flt_test both define AlgebraicCurve.Divisor.* — a promotion file must
  import from ONE root only (clash observed: "environment already contains AlgebraicCurve.Divisor.degree").
  Canonical root choice for divisor/canonical/RR rows: flt_test (its Theorems are green); flt_core for Cech/IsCurveOver.
  Consumers: import promotion modules (not raw roots) to avoid clashes.

## 8. 追加（2026-11-10 08:00）
- Serre pairing canonical import = tmp/sheaf/xif/paper/AG_FLT_SerrePairingPromotionActual.lean
  （checker CITABLE 2 decls probe_ok）。Decls: promotion_ResidueTheorem (statement row Prop),
  promotion_serrePairing (ported def, conditional hRT; section instances: HasCanonicalLocalResidueKStar,
  HasCanonicalDivisor, DCoordGenerates, Nontrivial Omega, HasPrincipalDivisors),
  promotion_serrePairing_apply_mk (COMPLETE proof). Source module flt_core SerrePairing EXIT=0, sorry=0.
- 目标 S_* 证明文件（serrePairing_bijective_and_flip_bijective / weilDualityAdelic_of_isAlgClosed /
  cechRiemannRoch_of_genusReached / flt_test hasCanonicalDivisor_of_isCurveOver）在 watchdog 并行编译下
  出现环境失败，非规则可修：INTERNAL PANIC: out of memory（90-500KB 大文件）;
  failed to read Mathlib .../Matrix/Permanent.olean.private、RingTheory/Smooth/Quotient.olean、
  RingTheory/Valuation/LocalSubring.olean（pinned Mathlib 构建缺 private/部分 olean）。
  需要 Lead 安排低并发串行编译这些大文件或修复 Mathlib 构建；不宣称这些证明已编译。
- 可直接引用的 canonical import：AG_FLT_RiemannRochPromotionActual（RR rows + 2 完整归约）、
  AG_FLT_CanonicalDivisorPromotionActual（canonical divisor + ell=genus, deg=2g-2 两个完整定理）、
  AG_FLT_CechPromotionActual（Cech H0/H1）、AG_FLT_SerrePairingPromotionActual（Serre pairing）、
  tmp.external.ported.flt_th.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData。

## 9. 注记（2026-11-10 08:10，Lead 决策）
- FLT big S_* 证明文件（serrePairing_bijective…/weilDualityAdelic…/cechRiemannRoch…/hasCanonicalDivisor…）
  在并行 watchdog 下的失败 = **environment-blocked (OOM under parallel), deferred serial recompile**。
  Lead 实测 Matrix/Permanent.olean.private、RingTheory/Smooth/Quotient.olean、RingTheory/Valuation/LocalSubring.olean
  均存在且完好——是并行读写/OOM 的瞬时环境问题，不是缺文件。处理：暂停后/队列清空时串行低并发重编
  （一次一个 big S_*，单独 job，不占 watchdog 并行）。这些是 ported 资产、**不是 gate 行**；
  gate 按 self-write-only（与 stage4 plan 一致）；不计入 gate/registry 失败。

## 10. 追加（2026-11-10 08:15）：串行低并发重编结果
- SERIAL GREEN: tmp/external/ported/flt_test/P2M/Sol/S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean
  单独 pwsh 前台串行 lake env lean -R D:/lean -o <olean> <file> EXIT=0
  （log tmp/serial_compile_S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean.log）。
  证明 Lead 判断：OOM/private-olean 是并行环境问题；串行可过。该文件是 ported 资产，不是 gate 行。
- 其余三个（serrePairing_bijective_and_flip_bijective / weilDualityAdelic_of_isAlgClosed / cechRiemannRoch_of_genusReached）
  串行首轮 EXIT=1 仅因缺失 flt_core Theorems 依赖 olean（finite_H1_and_exists_linearEquiv_dual_H1_omegaSpace /
  functionFieldRiemannRoch_of_isAlgClosed / finiteDimensional_lSpace）。已启动后台串行 job
  （order: tmp/serial_closure_order.txt，86 files topo + 3 targets）低并发逐个重编闭包；
  进展写 tmp/serial_compile_summary.txt / tmp/serial_compile_*.log。未完成前不宣称它们已绿。

## 11. 追加（2026-11-10 18:40）：TauCeti Belyi/abc canonical ports（checker-CITABLE）
- CANONICAL ROOT: tmp/external/ported/tauceti_belyi_core（quickport closure 6 files, Apache-2.0 attribution）
- Module paths: tmp.external.ported.tauceti_belyi_core.TauCeti.Algebra.Polynomial.CriticalValues（CITABLE 13 decls;
  sha256 6D3B5143...299F）; ...Belyi（CITABLE 13; sha256 9948742A...CAD0）; ...NumberTheory.AbcConjecture
  （CITABLE 8; sha256 B6336589...08EC）。
- Drift fixes: rootSet_map_eq adaptation lemma (pinned Mathlib lacks rootSet_map) + Belyi call-site patch;
  CriticalValues criticalValues_map proof replaced by rootSet_map_eq rewriting. sorry/axiom grep = 0 in all three.
- Consumers: mainline AbcStatementAlignmentActual (LeanFormal.IUT.ABCConjecture <-> TauCeti.AbcConjecture);
  Belyification assets (belyiPolynomial, rootSet_derivative_belyiPolynomial_subset,
  exists_polynomial_aeval_mem_criticalValues_subset) for Mzk1 Lemma 2.2/2.4/GeometricCore.

## 12. 追加（2026-11-10 18:52，mainline）：tauceti_belyi_core canonical root 确认 + 消费者
- CANONICAL ROOT 确认: tmp/external/ported/tauceti_belyi_core（§2 表已登记；§11 三模块 checker-CITABLE 经 mainline 复核：CriticalValues 13 decls、Belyi 13、AbcConjecture 8，均 probe_ok/olean_fresh）。
- 消费者（已落地）: tmp/sheaf/xif/paper/AbcStatementAlignmentActual.lean（checker CITABLE 4 decls probe_ok；证明 LeanFormal.IUT.ABCConjecture <-> TauCeti.AbcConjecture；import tmp.external.ported.tauceti_belyi_core.TauCeti.NumberTheory.AbcConjecture）。
- 消费者（可引用，未开始）: Belyi belyiPolynomial / rootSet_derivative_belyiPolynomial_subset / criticalValues_belyiPolynomial_subset / exists_polynomial_(eval|aeval)_mem_criticalValues_subset 供 Mzk1 Lemma 2.2/2.4/GeometricCore Belyification；CriticalValues 供 critical values 有限性/映射。
- Ported assets NON-GATE（不入 gate 计数）；registry FROZEN 14041；无 registry edits。import 路径统一用 tmp.external.ported.tauceti_belyi_core.TauCeti.*。

## 13. 追加（2026-11-10 19:30，mainline）：flt_test duplicate 修正 + rename-map 规则
- flt_test 副本 Def_ModularCurve_CharLFrobeniusGeomLevel 携带 modularFunctionFieldC 变体的 AddMonoidHom.domRestrict（3 处：1280/1297/1314），此前 patch 只覆盖 flt_core/flt_th 副本；已机械替换为 .comp (...).subtype，serial + official watchdog EXIT=0（18:43:00，src 66789）。
- 官方 results log EXIT=0: flt_test/Theorems/Thm_AlgebraicCurve_Place_mem_of_ord_nonneg（1020）、Place_ord_nonneg_of_mem（1006）、Place_mem_iff_ord_nonneg（1024）、Definitions/Def_ModularCurve_CharLFrobeniusGeomLevel（66789）；pending: Place_exists_restrict_eq（P2M Sol dep olean 在编）。quarantine 已清；queue 67 / lean ~22 / ALL_BLOCKED none。
- NEW rename-map 规则（port_rename_map 待加）: `.domRestrict (Divisor.degZero (K := K) (F := modularFunctionFieldC K N))` -> `.comp (...).subtype`（已应用于 flt_test 与先前各 root）。
- 全部 ported assets NON-GATE；pins 14041/23066/18800；registry frozen。
