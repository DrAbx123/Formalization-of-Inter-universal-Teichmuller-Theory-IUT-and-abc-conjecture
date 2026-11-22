/- B3 (grace) S1: SYMMETRIC two-chart Cech covers.
   DECISION (per Lead): use the symmetric cover (A1 = R2 n, common A01 = Overlap0 n,
   rho1 = chartInf -> OverlapInf -> (overlapRingEquiv) Overlap0) instead of the degenerate U0/U0
   cover; cross terms become genuine transition units in Overlap0.
   Reuse: overlapRingEquiv (OverlapActual) + cover API (AG_FLT_TwoChartCechActual). No sorry. -/
import tmp.sheaf.xif.paper.AG_FLT_TwoChartCechActual
import tmp.sheaf.xif.paper.Mzk1G1FermatOverlapActual
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1B3CoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual

/-- ChartInfRing n → Overlap0 n：先局部化到 OverlapInf，再经 overlapRingEquiv 回到 Overlap0。 -/
noncomputable def chartInfToOverlap0Alg (n : Nat) : ChartInfRing n →ₐ[ℚ] Overlap0 n where
  toRingHom := (overlapRingEquiv n).symm.toRingHom.comp
    (IsScalarTower.toAlgHom ℚ (ChartInfRing n) (OverlapInf n)).toRingHom
  commutes' r := by
    have h : ((overlapRingEquiv n).symm.toRingHom.comp
        (IsScalarTower.toAlgHom ℚ (ChartInfRing n) (OverlapInf n)).toRingHom).comp
        (algebraMap ℚ (ChartInfRing n)) = algebraMap ℚ (Overlap0 n) := RingHom.ext_rat _ _
    exact RingHom.congr_fun h r

/-- Y_n 的对称两图 Cech cover。 -/
noncomputable def fermatCover (n : Nat) : TwoChartCech.Cover ℚ where
  A0 := Chart0Ring n
  A1 := ChartInfRing n
  A01 := Overlap0 n
  ρ0 := IsScalarTower.toAlgHom ℚ (Chart0Ring n) (Overlap0 n)
  ρ1 := chartInfToOverlap0Alg n

/-- P¹ 的 overlap 环：ℚ[λ,λ⁻¹]。 -/
abbrev P1Overlap : Type := Localization.Away (Polynomial.X : Polynomial ℚ)

/-- P¹ 的两图 Cech cover：A0 = ℚ[λ]、A1 = ℚ[t]、A01 = ℚ[λ,λ⁻¹]，t ↦ λ⁻¹。 -/
noncomputable def p1Cover : TwoChartCech.Cover ℚ where
  A0 := Polynomial ℚ
  A1 := Polynomial ℚ
  A01 := P1Overlap
  ρ0 := (IsScalarTower.toAlgHom ℚ (Polynomial ℚ) P1Overlap : Polynomial ℚ →ₐ[ℚ] P1Overlap)
  ρ1 := (Polynomial.aeval (IsLocalization.Away.invSelf (S := P1Overlap)
    (Polynomial.X : Polynomial ℚ)) : Polynomial ℚ →ₐ[ℚ] P1Overlap)

/-- P¹ 上 O(1) 的过渡单元 = λ。 -/
noncomputable def p1O1Unit : P1Overlapˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := P1Overlap)
    (Polynomial.X : Polynomial ℚ)).unit

#print axioms chartInfToOverlap0Alg
#print axioms fermatCover
#print axioms p1Cover
#print axioms p1O1Unit

end LeanFormal.IUT.XiFPaper.Mzk1G1B3CoverActual