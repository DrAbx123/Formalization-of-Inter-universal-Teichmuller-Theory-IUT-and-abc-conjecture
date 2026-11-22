import tmp.sheaf.xif.paper.Mzk1P2ArchWeightAlignmentActual
import tmp.sheaf.xif.paper.Mzk1B5FullProductFormulaCountActual
import Mathlib.Tactic

/-! # P2: exact arch-log source criterion

The actual arch metric is -C_K * archimedeanLogNorm.  The R1.3 mass difference
is -p2WeightedDetLog.  Hence the actual arch metric equals C_K * p2R13Exact
exactly when the global arch log equals p2WeightedDetLog.
-/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P2ArchLogSourceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P2ArchWeightAlignmentActual
open LeanFormal.IUT.XiFPaper.Mzk1P2DetWeightedNonnegActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33ArchMetricActual
open LeanFormal.IUT.XiFPaper.Mzk1NormArchCKActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Actual arch metric is nonnegative iff the global arch log is nonpositive. -/
theorem p2ArchMetric_nonneg_iff_archLog_nonpos
    (f : (T.arithmetic.K)ˣ) :
    0 ≤ archDetMetricWeight (F := T.arithmetic.K) f ↔
      archimedeanLogNorm (F := T.arithmetic.K) (f : T.arithmetic.K) ≤ 0 := by
  rw [p2ArchMetric_eq_neg_archCK_mul_archLog T f]
  have hCK : 0 < archCK (T.arithmetic.K) := archCK_pos (K := T.arithmetic.K)
  constructor
  · intro h
    by_contra hL
    push_neg at hL
    have hpos : 0 < archCK (T.arithmetic.K) *
        archimedeanLogNorm (F := T.arithmetic.K) (f : T.arithmetic.K) :=
      mul_pos hCK hL
    nlinarith
  · intro hL
    have h' : -archCK (T.arithmetic.K) *
        archimedeanLogNorm (F := T.arithmetic.K) (f : T.arithmetic.K) =
        archCK (T.arithmetic.K) *
          (-archimedeanLogNorm (F := T.arithmetic.K) (f : T.arithmetic.K)) := by
      ring
    rw [h']
    exact mul_nonneg hCK.le (neg_nonneg.mpr hL)

/-- Exact source criterion: actual arch metric = C_K * p2R13Exact iff global
arch log equals p2WeightedDetLog. -/
theorem p2ArchMetric_eq_archCK_mul_p2R13Exact_iff
    (f : (T.arithmetic.K)ˣ) :
    archDetMetricWeight (F := T.arithmetic.K) f =
        archCK (T.arithmetic.K) * p2R13Exact T ↔
      archimedeanLogNorm (F := T.arithmetic.K) (f : T.arithmetic.K) =
        p2WeightedDetLog T := by
  have hCK : (0 : Real) < archCK (T.arithmetic.K) := archCK_pos (K := T.arithmetic.K)
  constructor
  · intro h
    rw [p2ArchMetric_eq_neg_archCK_mul_archLog T f] at h
    rw [p2R13Exact_eq_neg_p2WeightedDetLog T] at h
    have hcancel : -archimedeanLogNorm (F := T.arithmetic.K) (f : T.arithmetic.K) =
        -p2WeightedDetLog T := by
      apply mul_left_cancel₀ hCK.ne'
      calc
        archCK (T.arithmetic.K) *
            (-archimedeanLogNorm (F := T.arithmetic.K) (f : T.arithmetic.K)) =
            -archCK (T.arithmetic.K) *
              archimedeanLogNorm (F := T.arithmetic.K) (f : T.arithmetic.K) := by ring
        _ = archCK (T.arithmetic.K) * (-p2WeightedDetLog T) := h
    linarith
  · intro h
    rw [p2ArchMetric_eq_neg_archCK_mul_archLog T f, h,
      p2R13Exact_eq_neg_p2WeightedDetLog T]
    ring

/-- The remaining source identification as a single explicit Prop. -/
def P2ArchLogSourceIdentification (f : (T.arithmetic.K)ˣ) : Prop :=
  archimedeanLogNorm (F := T.arithmetic.K) (f : T.arithmetic.K) = p2WeightedDetLog T

/-- Exact missing list: source element and its root-family identification. -/
def p2ArchLogSourceMissing : List String :=
  [ "global element f : K^x whose archimedeanLogNorm equals p2WeightedDetLog T",
    "identification of the P2 root coefficient family with f",
    "actual global-to-root place compatibility" ]

theorem p2ArchLogSourceMissing_length : p2ArchLogSourceMissing.length = 3 := rfl

#check p2ArchMetric_nonneg_iff_archLog_nonpos
#check p2ArchMetric_eq_archCK_mul_p2R13Exact_iff
#check P2ArchLogSourceIdentification
#check p2ArchLogSourceMissing
end LeanFormal.IUT.XiFPaper.Mzk1P2ArchLogSourceActual
end
