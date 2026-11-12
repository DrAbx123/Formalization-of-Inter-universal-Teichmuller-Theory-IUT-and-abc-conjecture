# AG-INFRA-PLAN — [Mzk1] GeometricCore 最小 AG 基础设施（qpilot, 2026-11-10）

## 目标陈述（[Mzk1] Thm 2.5 GeometricCore，精确形式，供 AG 层使用）
设 k 为域（目标情形 k = Qbar），X 为光滑、proper、几何连通、相对维数 1 的 k-曲线，
T ⊂ X(kbar) 有限且 |T| >= 2g+1（g = genus(X)）。则存在有限态射 psi : X -> P^1_k 使得
psi(T) ⊂ {0}、psi 在 0 上非分歧、且 psi^* O(1) ≅ O(Σ_{t∈T} [t]) 作为除子线丛。
Lean 陈述层由 AG01CurveFoundationsActual.S3133CurveOver 承载（Smooth+IsProper+
GeometricallyConnected+SmoothOfRelativeDimension 1，全部 Mathlib 现有 predicate），
除子/线丛层由 AG_FLT_Def_AlgebraicCurve_DivisorClassGroup（Apache-2.0 改编）承载。

## 已核实 Mathlib 能力矩阵（AG00MathlibAuditActual，CITABLE）
HAS: Scheme/Spec/ProjectiveSpectrum; IsProper(Morphisms/Proper.lean:42);
Smooth(Morphisms/Smooth.lean:62); SmoothOfRelativeDimension(Smooth.lean:135);
GeometricallyConnected(Geometrically/Connected.lean:40)（注：lattice 早期审计漏记此项，已更正）;
FunctionField; OrderOfVanishing; RationalMap; 抽象层上同调
Mathlib/CategoryTheory/Sites/SheafCohomology/{Basic,Cech,MayerVietoris}.lean（早期审计漏记）。
MISSING: line bundle/invertible sheaf; coherent cohomology H^0/H^1; Riemann-Roch; Serre duality;
curve genus（AG00 audit 14 行矩阵，kernel rfl 检查）。

## 外部现成资产（STEP 0 结果，不重造）
- FLT 仓库 anthropics/fermats-last-theorem（Apache-2.0，本地 tmp/external/flt-lean）:
  Def_AlgebraicCurve_DivisorClassGroup（Place/Divisor/degree/degZero/IsPrincipal/Pic/Pic0，
  已改编并 CITABLE）、Repartitions、AdelicIndex（LSpace/ell/adeleBdd/adeleSpace，
  已改编并 CITABLE）、CechSectionsOfDivisor、SerrePairing、RiemannRochRows、
  SmoothProperCurveBase/FiniteMapData。版本差: FLT lean v4.33.1/mathlib db584cd6 vs
  我们 v4.32.2/905b9581；已发现机械漂移 AddMonoidHom.domRestrict（改编时改为 mk' 组合）
  与 zero_le'/count_associates_factors_eq 弃用别名（已入 port_rename_map.txt）。
- TauCeti 仓库（Apache-2.0，本地 tmp/TauCeti，Lean v4.36.0-rc1）：函数域/RR/除子/微分/
  Belyi 更大闭包，Lead 已 port 264 文件到 tmp/external/ported/tauceti2（不重复 port）。
- Mathlib 上游 PR: #36218 已合并（exact sequences），#41621 R-R draft（chi(O(D))=deg+chi(O_X)），
  #43392 层模上同调 API（可变现目标，不阻塞当前改编路线）。

## 构建顺序（每层真实 Lean，禁止 axiom/sorry/假定义）
1. AG00/AG00b/AG01/AG02 — DONE + checker CITABLE（能力矩阵、曲线 predicate、genus 数据接口）。
2. AG_FLT 改编层 — DivisorClassGroup/Repartitions/AdelicIndex/CoherentBaseChange DONE
   EXIT=0（前三个 checker CITABLE）；TwoChartCech/CechSectionsOfDivisor 已入队待看门狗。
3. Cech H0/H1 + Serre pairing + RR rows（FLT 改编：SerdePairing/RiemannRochRows/AdelicIndex 已具备）。
4. 线丛与 H^0(Omega) -> genus 定义（AG02 的 S3133GenusCohomologyTarget 为命名目标）。
5. basepoint-free 线性系统 + pencil -> 到 P^1 的态射（FLT basepoint/pencil 闭包已分析：
   3 目标 224 文件闭包 -> ported tmp/external/ported/flt_test，topo order 已入队）。
6. GeometricCore 陈述组装（SmoothProperCurveBase/FiniteMapData 改编后）。

## 风险/工作量
- 第 2-3 层机械改编已打通（失败根因多数为 olean 输出目录缺失，非 Lean 错误；
  port 工具已加预建目录规则）。
- 第 5 层（RR + basepoint-free -> P^1）是数学大头；优先使用 FLT/TauCeti 已证闭包，
  我们只做 import 改写与接口裁剪；不做整仓搬运。
- 第 6 层依赖第 5 层完成；但 GeometricCore 陈述可先以 S3133CurveOver + 目标 Prop 命名，
  不宣称已证。

## STEP 0（每批第一行）
2026-11-10: deep search 'Scheme.*Proper|LineBundle|Cartier|Cohomology|RiemannRoch|Serre|RatFunc'
-> FLT 本地 1450 lean + TauCeti + Mathlib SheafCohomology -> reuse (见
coord/PRIOR-ART-INDEX.md 对应小节)。
