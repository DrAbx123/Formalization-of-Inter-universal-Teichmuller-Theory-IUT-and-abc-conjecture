import tmp.sheaf.xif.paper.Mzk1P2DetWeightedNonnegActual
import tmp.sheaf.xif.paper.Mzk1Ob33ArchMetricActual
import Mathlib.Tactic

/-! # P2: arch weight alignment

The actual archimedean metric satisfies
  archDetMetricWeight f = - C_K * archimedeanLogNorm f
(Ob33ArchMetricActual).  The R1.3 mass difference satisfies
  p2R13Exact = - p2WeightedDetLog.

Thus, exactly when the global archimedean log norm equals the P2 weighted
determinant log, the actual arch metric equals C_K * p2R13Exact and is
nonnegative.  The log-norm identification is kept as an explicit missing
hypothesis; it is not assumed globally.
-/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P2ArchWeightAlignmentActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P2DetWeightedNonnegActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33ArchMetricActual
open LeanFormal.IUT.XiFPaper.Mzk1NormArchCKActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Actual arch metric sign identity, re-exported for the P2 coefficient field. -/
theorem p2ArchMetric_eq_neg_archCK_mul_archLog
    (f : (T.arithmetic.K)ˣ) :
    archDetMetricWeight (F := T.arithmetic.K) f =
      - archCK (T.arithmetic.K) *
        archimedeanLogNorm (F := T.arithmetic.K) (f : T.arithmetic.K) :=
  archDetMetricWeight_eq_neg_archimedeanLogNorm (F := T.arithmetic.K) f

/-- Sign/weight alignment: if the global arch log equals the P2 weighted
determinant log, then the actual arch metric is C_K times the R1.3 mass
difference. -/
theorem p2ArchMetric_eq_archCK_mul_p2R13Exact_of_logNorm_eq
    (f : (T.arithmetic.K)ˣ)
    (hlog : archimedeanLogNorm (F := T.arithmetic.K) (f : T.arithmetic.K) =
      p2WeightedDetLog T) :
    archDetMetricWeight (F := T.arithmetic.K) f =
      archCK (T.arithmetic.K) * p2R13Exact T := by
  rw [p2ArchMetric_eq_neg_archCK_mul_archLog T f, hlog,
    p2R13Exact_eq_neg_p2WeightedDetLog T]
  ring

/-- Conditional nonnegativity of the actual arch metric from the P2 R1.3
nonnegativity and the explicit log-norm alignment. -/
theorem p2ArchMetric_nonneg_of_logNorm_eq
    (f : (T.arithmetic.K)ˣ)
    (hlog : archimedeanLogNorm (F := T.arithmetic.K) (f : T.arithmetic.K) =
      p2WeightedDetLog T) :
    0 ≤ archDetMetricWeight (F := T.arithmetic.K) f := by
  rw [p2ArchMetric_eq_archCK_mul_p2R13Exact_of_logNorm_eq T f hlog]
  exact mul_nonneg (archCK_pos (K := T.arithmetic.K)).le (p2R13Exact_nonneg T)

/-- Exact missing arch alignment datum: a global element whose archimedean log
norm is the P2 weighted determinant log. -/
def p2ArchWeightAlignmentMissing : List String :=
  [ "global element f with archimedeanLogNorm f = p2WeightedDetLog T",
    "identification of the P2 root coefficient family with that global element",
    "sign convention: archDetMetricWeight = -C_K * archimedeanLogNorm" ]

theorem p2ArchWeightAlignmentMissing_length :
    p2ArchWeightAlignmentMissing.length = 3 := rfl

#check p2ArchMetric_eq_neg_archCK_mul_archLog
#check p2ArchMetric_eq_archCK_mul_p2R13Exact_of_logNorm_eq
#check p2ArchMetric_nonneg_of_logNorm_eq
#check p2ArchWeightAlignmentMissing
end LeanFormal.IUT.XiFPaper.Mzk1P2ArchWeightAlignmentActual
end
