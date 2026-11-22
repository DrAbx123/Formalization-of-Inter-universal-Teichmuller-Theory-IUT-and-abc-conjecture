import tmp.sheaf.xif.paper.Mzk1B5FullProductFormulaCountActual
import tmp.sheaf.xif.paper.Mzk1P2DetWeightedNonnegActual
import Mathlib.Tactic

/-! # P2: principal product-formula cancellation form

Combines the proven principal integral arch=count formula with the R1.3
weighted determinant form.  The arch/finite identification to the root
coefficient family is kept as an explicit compatibility hypothesis.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P2ProductFormulaCancelActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1B5FullProductFormulaCountActual
open LeanFormal.IUT.XiFPaper.Mzk1P2DetWeightedNonnegActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable {K : Type} [Field K] [NumberField K]

/-- Principal integral arch=count, re-exported for P2 consumers. -/
theorem principal_arch_eq_count
    (x : NumberField.RingOfIntegers K) (hx : x ≠ 0) :
    (∑ w : NumberField.InfinitePlace K, (w.mult : Real) * Real.log (w (x : K))) =
      ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        ((Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span {x})).factors : Real) *
          Real.log (Ideal.absNorm v.asIdeal : Real) :=
  Mzk1B5FullProductFormulaCountActual.arch_log_eq_count_sum K x hx

/-- Algebra: arch = weighted implies p2RExact = -arch once the R1.3 weighted
form is known. -/
theorem p2RExact_eq_neg_arch_of_arch_eq_weighted
    (arch : Real)
    (harch : arch = p2WeightedDetLog T) :
    p2R13Exact T = -arch := by
  rw [p2R13Exact_eq_neg_p2WeightedDetLog T, harch]

/-- Cancellation form: if a tensor arch value equals the weighted determinant
log, then the product-formula residual for that arch value is zero. -/
theorem arch_sub_weighted_eq_zero_of_eq
    (arch : Real)
    (harch : arch = p2WeightedDetLog T) :
    arch - p2WeightedDetLog T = 0 := by
  rw [harch]
  ring

/-- Exact compatibility missing: the actual archimedean tensor log of the root
coefficient family is not yet identified with p2WeightedDetLog.  No such
identification is assumed; the theorems above are conditional on it. -/
def p2ArchWeightAlignmentMissing : List String :=
  [ "actual archimedean tensor log on RootExtensionProductCarrier T",
    "identification with p2WeightedDetLog T",
    "sign/weight convention of s1915LocalDegree vs archDetMetricWeight" ]

theorem p2ArchWeightAlignmentMissing_length :
    p2ArchWeightAlignmentMissing.length = 3 := rfl

#check principal_arch_eq_count
#check p2RExact_eq_neg_arch_of_arch_eq_weighted
#check arch_sub_weighted_eq_zero_of_eq
#check p2ArchWeightAlignmentMissing
end LeanFormal.IUT.XiFPaper.Mzk1P2ProductFormulaCancelActual
end
