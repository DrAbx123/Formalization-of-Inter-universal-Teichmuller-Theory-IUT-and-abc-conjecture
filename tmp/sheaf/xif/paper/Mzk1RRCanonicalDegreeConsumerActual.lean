import tmp.sheaf.xif.paper.Mzk1GeomCoreRRCanonicalDegreeActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D RR canonical degree green consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1RRCanonicalDegreeConsumerActual

open AlgebraicCurve
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreRRCanonicalDegreeActual

universe u v

theorem rrCanonicalDegreeConsumer_canonical {K F : Type*} [Field K] [Field F] [Algebra K F]
    [HasCanonicalLocalResidueKStar K F] [IsCurveOver K F]
    [HasCanonicalDivisor (K := K) (F := F)]
    [∀ (v : Place K F), v.DCoordGenerates] [Nonempty (Place K F)]
    [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    (hsup : ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0), ∃ φ : Module.Dual K (adeleSpace K F),
      φ ≠ 0 ∧ φ ∈ omegaSpace (canonicalDivisorOf hω) ∧
      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω)
    (hC : ConstantsAreBase K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    Divisor.degree (canonicalDivisorOf hω) = 2 * (genus K F : ℤ) - 2 :=
  canonical_degree_eq_two_genus_sub_two h hsup hC hω

def rrCanonicalDegreeConsumerRows : List (String × String × String) :=
  [ ("canonical degree = 2g-2", "PROVED (named inputs)", "rrCanonicalDegreeConsumer_canonical") ]

theorem rrCanonicalDegreeConsumerRows_length : rrCanonicalDegreeConsumerRows.length = 1 := rfl

#check rrCanonicalDegreeConsumer_canonical
#check rrCanonicalDegreeConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1RRCanonicalDegreeConsumerActual
end