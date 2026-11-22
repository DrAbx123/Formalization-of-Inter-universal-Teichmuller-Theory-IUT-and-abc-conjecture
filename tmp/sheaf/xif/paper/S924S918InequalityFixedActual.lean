import tmp.sheaf.xif.paper.S914PaperLVExInstantiationActual
import tmp.sheaf.xif.paper.S921RQpilotPaperRegionPositivityActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S924S918InequalityFixedActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S914PaperLVExInstantiationActual
open LeanFormal.IUT.XiFPaper.S921RQpilotPaperRegionPositivityActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]

/-- Positivity of R from the S921 interior condition; no coefficient equality. -/
theorem s924R_measure_pos_of_interior
    (h : S921RInteriorNonempty (l := l) T b) :
    0 < mu (s914R (l := l) T b) :=
  s921R_measure_pos_of_interior (l := l) T b mu h

/-- Exact finiteness input for S; no equality route and no scaling data. -/
def S924SHullFinite : Prop :=
  mu (s914S (l := l) T b) < ⊤

/-- Inequality V(R) <= V(S), using only S914 R subset S and S921 positivity.
Finiteness of S is the exact remaining input. -/
theorem s924V_R_le_V_S_of_interior_finite
    (hint : S921RInteriorNonempty (l := l) T b)
    (hfin : S924SHullFinite (l := l) T b mu) :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (s914R (l := l) T b) ≤
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (s914S (l := l) T b) :=
  s914MuLogComparison (l := l) T b mu
    (s924R_measure_pos_of_interior (l := l) T b mu hint) hfin

/-- Inequality-only package: R subset S, R positive, S finite, hence
V(R) <= V(S).  No equality is stated. -/
theorem s924InequalityPackage
    (hint : S921RInteriorNonempty (l := l) T b)
    (hfin : S924SHullFinite (l := l) T b mu) :
    s914R (l := l) T b ⊆ s914S (l := l) T b ∧
      0 < mu (s914R (l := l) T b) ∧
      mu (s914S (l := l) T b) < ⊤ ∧
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
          (s914R (l := l) T b) ≤
        arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
          (s914S (l := l) T b) :=
  ⟨s914R_subset_S (l := l) T b, s924R_measure_pos_of_interior (l := l) T b mu hint,
    hfin, s924V_R_le_V_S_of_interior_finite (l := l) T b mu hint hfin⟩

/-- Exact minimal remaining analytic input: S finiteness. -/
def S924FiniteSHullRequired : Prop :=
  S924SHullFinite (l := l) T b mu

end LeanFormal.IUT.XiFPaper.S924S918InequalityFixedActual

end
