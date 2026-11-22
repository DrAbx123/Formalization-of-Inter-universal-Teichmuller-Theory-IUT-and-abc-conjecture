import tmp.sheaf.xif.paper.S1987D5LargeImageFiveActual
import tmp.sheaf.xif.paper.S1924ZeroCriterionActual
import tmp.sheaf.xif.paper.S1907SerreLargeImageActual
import tmp.sheaf.xif.paper.S1366PrePsiSeparabilityFix

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1894D5LargeImageActual
open LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual
open LeanFormal.IUT.XiFPaper.S1924ZeroCriterionActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.InitialThetaSource.TorsionCarrierReduction
open LeanFormal.IUT.XiFPaper.S1366PrePsiSeparabilityFix

namespace LeanFormal.IUT.XiFPaper.S1988TorsionMinimalPackageActual

/-- The minimal actual package for the D5 torsion clause at l: rank-two
freeness of E'[l] plus the basis-free large-image input. -/
def S1988Minimal (l : PrimeGeFive) : Prop :=
  S1725RankTwoBasisGap l ∧ S1894LargeImageInput l

theorem S1988Minimal_iff_exactMissing (l : PrimeGeFive) :
    S1988Minimal l ↔ S1894ExactMissing l := Iff.rfl

theorem S1988Minimal_iff_imageContainsSL2 (l : PrimeGeFive) :
    S1988Minimal l ↔ S1725ImageContainsSL2 l :=
  (S1988Minimal_iff_exactMissing l).trans (S1894ExactMissing_iff_image l)

/-- From the minimal package, the actual D5 clause. -/
theorem S1988Clause_of_minimal (l : PrimeGeFive)
    (h : S1988Minimal l) : Nonempty (SourceTorsionClause.{0, 0, 0} l) :=
  ⟨S1894SourceTorsionClause_of_basis_free l h.1 h.2⟩

/-- At l = 5 the rank-two half is actual, so the minimal package has a
single remaining input: the basis-free large-image condition. -/
theorem S1988Minimal_five_iff_largeImage :
    S1988Minimal S1987Five ↔ S1987D5LargeImageFive :=
  ⟨fun h => h.2, fun h => ⟨S1982RankTwoBasisGap_five, h⟩⟩

theorem S1988RankTwo_five_actual : S1725RankTwoBasisGap S1987Five :=
  S1982RankTwoBasisGap_five

/-- The actual l = 5 torsion clause from the single remaining large-image
input. -/
noncomputable def S1988Clause_five_of_largeImage
    (h : S1987D5LargeImageFive) : SourceTorsionClause.{0, 0, 0} S1987Five :=
  S1987SourceTorsionClause h

/-- For general l, rank-two freeness follows from the generic odd
pre-Psi separability input (still a named source input, not proved here). -/
theorem S1988RankTwo_of_genericSeparable
    (h : S1366GenericOddPreΨSeparableInput) (l : PrimeGeFive) :
    S1725RankTwoBasisGap l :=
  S1924S1906BasisGap_of_genericSeparable h l

/-- The exact large-image input at l = 5 is the frozen Serre statement. -/
theorem S1988LargeImage_five_iff_serre :
    S1987D5LargeImageFive ↔
      SerreStyleLargeImageStatement (F := S1720Field) S1720Curve S1987Five :=
  S1987D5LargeImageFive_iff_serre

/-- S1907 records that the large-image statement is absent from the tree
and from Mathlib; this is the exact missing input, not a formal consequence. -/
theorem S1988LargeImage_missing_is_exact :
    S1987D5LargeImageFive ↔ S1982D5ExactFirstMissing :=
  Iff.rfl

#check S1988Minimal
#check S1988Clause_of_minimal
#check S1988Clause_five_of_largeImage
#check S1988RankTwo_five_actual
#print axioms S1988Clause_of_minimal
#print axioms S1988Clause_five_of_largeImage
end LeanFormal.IUT.XiFPaper.S1988TorsionMinimalPackageActual
end