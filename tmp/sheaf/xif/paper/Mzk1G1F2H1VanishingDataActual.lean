/- R4 / F2.1: explicit packing of the H1-vanishing / Weil-duality prerequisites.

  Donors (sophie, coord/R4-H1-VANISHING-DATA-DOC.md; oleans OK):
  `tmp.external.ported.flt.Definitions.Def_AlgebraicCurve_{AdelicIndex, RiemannRochRows,
  WeilOfKaehler, SerrePairing, CanonicalDivisor, LocalResidue}`:
  `ConstantsAreBase` (:48), `indexOfSpecialty` (:139), `residuePairing` (:345),
  `RiemannIndexFormula` (:22), `WeilDualityAdelic` (:28), `WeilDuality` (:34),
  `WeilDuality_of_riemannIndex_of_adelic` (:59), `ResidueTheorem` (WeilOfKaehler:110),
  `serrePairing` (SerrePairing:229), `HasCanonicalDivisor` (CanonicalDivisor:17).
  NOTE: `ResidueTheorem K F` and `HasWeilCanonicalDivisor` need the
  `[HasCanonicalDivisor (K := K) (F := F)]` section hypothesis, hence it is an explicit
  structure parameter below. No sorry/axiom. -/
import tmp.external.ported.flt.Definitions.Def_AlgebraicCurve_AdelicIndex
import tmp.external.ported.flt.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import tmp.external.ported.flt.Definitions.Def_AlgebraicCurve_RiemannRochRows
import tmp.external.ported.flt.Definitions.Def_AlgebraicCurve_LocalResidue
import tmp.external.ported.flt.Definitions.Def_AlgebraicCurve_SerrePairing
import tmp.external.ported.flt.Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2H1VanishingDataActual
open AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
  [Nontrivial (KaehlerDifferential K F)]

/-- **H¹ 消失的显式前提打包**（A3EvalData 的上同调输入；不重建 Serre 对偶）。 -/
structure A3H1VanishingData (K F : Type*) [Field K] [Field F] [Algebra K F]
    [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates] [Nontrivial (KaehlerDifferential K F)] where
  W : Divisor K F
  D : Divisor K F
  x : Place K F
  hPD : HasPrincipalDivisors K F
  hWD : HasWeilCanonicalDivisor (K := K) (F := F)
  hRank : WeilDifferentialRankOne (K := K) (F := F)
  hDual : WeilDuality K F
  hDualAdelic : WeilDualityAdelic K F
  hRT : ResidueTheorem K F
  hC : ConstantsAreBase K F
  hdeg : Divisor.degree (W - (D - Finsupp.single x 1)) < 0

theorem A3H1VanishingData.degree_neg {K F : Type*} [Field K] [Field F] [Algebra K F]
    [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates] [Nontrivial (KaehlerDifferential K F)]
    (P : A3H1VanishingData K F) :
    Divisor.degree (P.W - (P.D - Finsupp.single P.x 1)) < 0 := P.hdeg

/-- **R4 pack（sophie 文档接口）**：H¹ 消失的 paper inputs。 -/
structure H1VanishingData (K F : Type*) [Field K] [Field F] [Algebra K F]
    [HasPrincipalDivisors K F] [HasCanonicalLocalResidueKStar K F]
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates] [Nontrivial (KaehlerDifferential K F)] where
  constantsAreBase : ConstantsAreBase K F
  residueTheorem : ResidueTheorem K F
  weilDualityAdelic : WeilDualityAdelic K F
  h1_vanish : ∀ D : Divisor K F, indexOfSpecialty D = 0

/-- R4 的 Riemann-index 特化：由 `RiemannIndexFormula` donor 与 H¹ 消失得。 -/
theorem H1VanishingData.indexFormula {K F : Type*} [Field K] [Field F] [Algebra K F]
    [HasCanonicalLocalResidueKStar K F]
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates] [Nontrivial (KaehlerDifferential K F)]
    [IsCurveOver K F]
    (hD : H1VanishingData K F) (hRI : RiemannIndexFormula K F) (D : Divisor K F) :
    (indexOfSpecialty D : ℤ) = (ell D : ℤ) - (Divisor.degree D + 1 - (genus K F : ℤ)) := by
  simpa [hD.h1_vanish D] using hRI D

#print axioms A3H1VanishingData.degree_neg
#print axioms H1VanishingData.indexFormula

end LeanFormal.IUT.XiFPaper.Mzk1G1F2H1VanishingDataActual