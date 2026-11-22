/- U-R C2 hP5 (P) lambda-weighted lower bound (kurt).

Uses the per-b lower bound from Mzk1URThetaKLowerActual.ksThetaHullLog_lower and the
paper lambda/d_mod weights from Mzk1URThetaKSideActual:
  -(sum_b thetaLamWeight_b * urCeilC_b * log p_b) <= ksThetaHullLogRoot_lam.

THIS FILE ONLY uses maxHeartbeats 1000000 (paper-level elaboration budget); RC registry: kurt-adapters-20261117 (1M heartbeats; Lead-approved list).
-/
import tmp.sheaf.xif.paper.Mzk1URThetaKLowerCoreActual
import tmp.sheaf.xif.paper.Mzk1URThetaKLowerBoundActual
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaKHP5LamActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerCoreActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerBoundActual
open MeasureTheory

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (ksBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (ksBlock T b)]

/-- Per-b lambda-weighted lower bound. -/
theorem ksThetaHullLog_lower_weighted (b : Bad (nativePlaceSelection T)) :
    -(thetaLamWeight T b * ((urCeilC (l := l) T b) * Real.log
        ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ))) ≤
      thetaLamWeight T b * ksThetaHullLog (l := l) T b := by
  have h := ksThetaHullLog_lower (l := l) T b
  have hw : 0 ≤ thetaLamWeight T b := thetaLamWeight_nonneg T b
  have hm := mul_le_mul_of_nonneg_left h hw
  unfold ksThetaHullLog
  calc -(thetaLamWeight T b * ((urCeilC (l := l) T b) * Real.log
        ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ)))
      = thetaLamWeight T b * (-((urCeilC (l := l) T b) * Real.log
        ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ))) := by ring
    _ ≤ thetaLamWeight T b * arithmeticTupleNormalizedLogVolume (ksPlaces T b) ksTuple
          MeasureTheory.Measure.addHaar (ksThetaHull (l := l) T b) := hm

/-- Lambda-weighted theta hull lower bound (paper H_pkt weight family). -/
theorem ksThetaHullLogRoot_lam_lower :
    -(∑ b : Bad (nativePlaceSelection T),
      thetaLamWeight T b * ((urCeilC (l := l) T b) * Real.log
        ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ))) ≤
      ksThetaHullLogRoot_lam (l := l) T := by
  have h := Finset.sum_le_sum
    (s := (Finset.univ : Finset (Bad (nativePlaceSelection T))))
    (f := fun b => -(thetaLamWeight T b * ((urCeilC (l := l) T b) * Real.log
      ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ))))
    (g := fun b => thetaLamWeight T b * ksThetaHullLog (l := l) T b)
    (fun b _ => ksThetaHullLog_lower_weighted (l := l) T b)
  unfold ksThetaHullLogRoot_lam
  rw [← Finset.sum_neg_distrib]
  exact h

#print axioms ksThetaHullLog_lower_weighted
#print axioms ksThetaHullLogRoot_lam_lower

end LeanFormal.IUT.XiFPaper.Mzk1URThetaKHP5LamActual
end