import tmp.sheaf.xif.paper.Mzk1P8FromP6IVActual
import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC
import tmp.sheaf.xif.paper.Mzk1P8GlobalFreyCriterionActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P8FromP6IVInequalityActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual
open LeanFormal.IUT.XiFPaper.Mzk1P8FromP6IVActual
open LeanFormal.IUT.XiFPaper.Mzk1P8GlobalFreyCriterionActual

/-- Actual P6 IV height/weight inequality input: the additive height bound
produced by the accepted P6 IV/display assembly. -/
def P8P6IVInequalityInput : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A : ℝ,
    ∀ a b c : ℕ, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + ε) * arithmeticWeight (abcRationalPoint a c) + A

/-- Actual conversion of the P6 IV inequality input to ABC. -/
theorem abcConjecture_of_p6IVInequality
    (h : P8P6IVInequalityInput) : ABCConjecture :=
  (abcConjecture_iff_abcArithmeticWeightHeightBound).mpr h

/-- Actual P8 uniform height bound derived from the P6 IV inequality input. -/
theorem p8UniformHeightBound_of_p6IVInequality
    (h : P8P6IVInequalityInput) : P8UniformHeightBound :=
  p8_finalCriterion.mpr (abcConjecture_of_p6IVInequality h)

/-- Actual consumer assembled from P8FromP6IVData and the P6 IV inequality. -/
theorem p8FromP6IVInequality_consumer
    (A : ActualThm110Data) (c : ℝ) (D : P8FromP6IVData A c)
    (h : P8P6IVInequalityInput) : ABCConjecture :=
  abcConjecture_of_p6IVInequality h

/-- Combined actual consumer: P6/IV display slack + P6 IV inequality. -/
theorem p8FromP6IVInequality_combined
    (A : ActualThm110Data) (c : ℝ) (D : P8FromP6IVData A c)
    (hCor312 : thm110Lhs A.toTerms ≤ thm110Mid A.toTerms + thm110Cor312Gap A.toTerms)
    (h : P8P6IVInequalityInput) :
    thm110Lhs (p8ActualDisplayTerms A) ≤ thm110Rhs (p8ActualDisplayTerms A) ∧
      ABCConjecture :=
  ⟨p8FromP6IV_displaySlack A hCor312, p8FromP6IVInequality_consumer A c D h⟩

end LeanFormal.IUT.XiFPaper.Mzk1P8FromP6IVInequalityActual
end
