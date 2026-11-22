/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # A669 B2: normalization split of s1902LogVolume (mainline) -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1CorrectedLogLawB2Actual

open scoped ENNReal
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- B2 (raw): real log of a scalar-multiplied Haar measure value splits. -/
theorem log_smul_measure_apply
    (c : ENNReal) (mu : Measure (S1902Carrier T)) (S : Set (S1902Carrier T))
    (hc0 : c ≠ 0) (hcT : c ≠ ⊤) (hS0 : mu S ≠ 0) (hST : mu S ≠ ⊤) :
    Real.log (((c • mu) S).toReal) =
      Real.log c.toReal + Real.log (mu S).toReal := by
  have hsm : ((c • mu) S) = c * mu S := by
    rw [Measure.smul_apply, smul_eq_mul]
  rw [hsm, ENNReal.toReal_mul, Real.log_mul
    (ENNReal.toReal_ne_zero.mpr ⟨hc0, hcT⟩)
    (ENNReal.toReal_ne_zero.mpr ⟨hS0, hST⟩)]

/-- B2: `s1902NormalizedHaar` log splits into scale + product Haar logs. -/
theorem s1902_log_split (S : Set (S1902Carrier T))
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T ≠ ⊤)
    (hS0 : rootExtensionProductHaar T S ≠ 0) (hST : rootExtensionProductHaar T S ≠ ⊤) :
    Real.log ((s1902NormalizedHaar T S).toReal) =
      Real.log (s1902HaarScale T).toReal +
        Real.log ((rootExtensionProductHaar T S).toReal) := by
  unfold s1902NormalizedHaar
  exact log_smul_measure_apply T (s1902HaarScale T) (rootExtensionProductHaar T) S
    hc0 hcT hS0 hST

end LeanFormal.IUT.XiFPaper.Mzk1CorrectedLogLawB2Actual

end