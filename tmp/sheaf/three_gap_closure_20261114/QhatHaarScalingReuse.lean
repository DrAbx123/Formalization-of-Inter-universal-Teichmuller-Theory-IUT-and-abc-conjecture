import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeActual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual

/-!
# The qhat Haar scaling from the existing root-field modulus theorem

Owner: root, single-thread review 2026-11-14.
Consumer: Mzk1P0QThetaReadoutCorrespondenceActual.qhatHaarScaling.
The consumer is being edited by its existing owner, so this file proves its
literal pointwise conclusion without importing or modifying that file.
No Class-B scalar-scaling hypothesis is introduced.
-/

noncomputable section
open scoped Pointwise

namespace LeanFormal.IUT.ThreeGapClosure20261114

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarFactorActual
open LeanFormal.IUT.XiFPaper.S865RootHaarFactorNormPowActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open MeasureTheory

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem qhat_haar_scaling_actual (b : Bad (nativePlaceSelection T)) :
    rootExtensionHaar T b (c0QLattice T b) =
      ENNReal.ofReal (‖c0QHat T b‖ ^ s1915LocalDegree T b) *
        rootExtensionHaar T b (rootExtensionUnitBall T b) := by
  have hq : c0QHat T b ≠ 0 :=
    pow_ne_zero _ (c0Alpha_ne_zero T b)
  let lam : (rootNormedExtension T b)ˣ := Units.mk0 (c0QHat T b) hq
  have hset : c0QLattice T b = lam • rootExtensionUnitBall T b := by
    change (fun y => c0QHat T b * y) '' rootExtensionUnitBall T b =
      (fun y => (lam : rootNormedExtension T b) * y) '' rootExtensionUnitBall T b
    rfl
  have hfactor :
      rootHaarFactor T b lam =
        ENNReal.ofReal (‖c0QHat T b‖ ^ s1915LocalDegree T b) := by
    simpa only [lam, Units.val_mk0, s1915LocalDegree] using
      rootHaarFactor_normPow_actual T b lam
  have hratio :
      ENNReal.ofReal (‖c0QHat T b‖ ^ s1915LocalDegree T b) =
        rootExtensionHaar T b (lam • rootExtensionUnitBall T b) /
          rootExtensionHaar T b (rootExtensionUnitBall T b) :=
    hfactor.symm.trans (rootHaarFactor_eq_ratio T b lam)
  rw [hset, hratio,
    ENNReal.div_mul_cancel
      (rootExtensionUnitBall_measure_pos T b).ne'
      (rootExtensionUnitBall_measure_lt_top T b).ne]

omit [Fintype (Bad (nativePlaceSelection T))] in
theorem local_degree_pos (b : Bad (nativePlaceSelection T)) :
    0 < s1915LocalDegree T b := by
  unfold s1915LocalDegree
  exact Module.finrank_pos

theorem qhat_lattice_measure_pos (b : Bad (nativePlaceSelection T)) :
    0 < rootExtensionHaar T b (c0QLattice T b) := by
  have hq : c0QHat T b ≠ 0 := pow_ne_zero _ (c0Alpha_ne_zero T b)
  rw [qhat_haar_scaling_actual T b]
  exact ENNReal.mul_pos
    (ENNReal.ofReal_pos.mpr (pow_pos (norm_pos_iff.mpr hq) _)).ne'
    (rootExtensionUnitBall_measure_pos T b).ne'

theorem qhat_lattice_measure_lt_top (b : Bad (nativePlaceSelection T)) :
    rootExtensionHaar T b (c0QLattice T b) < ⊤ := by
  rw [qhat_haar_scaling_actual T b]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (rootExtensionUnitBall_measure_lt_top T b)

/-- The literal local readout conclusion, with degree and mass side conditions
also discharged on the actual objects. -/
theorem qhat_signed_readout_eq_log_norm (b : Bad (nativePlaceSelection T)) :
    (1 / (s1915LocalDegree T b : ℝ)) *
        (Real.log (rootExtensionHaar T b (c0QLattice T b)).toReal -
          Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal) =
      Real.log ‖c0QHat T b‖ := by
  have hq : c0QHat T b ≠ 0 := pow_ne_zero _ (c0Alpha_ne_zero T b)
  have hqpos : 0 < ‖c0QHat T b‖ := norm_pos_iff.mpr hq
  have hOpos : 0 < (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal :=
    ENNReal.toReal_pos (rootExtensionUnitBall_measure_pos T b).ne'
      (rootExtensionUnitBall_measure_lt_top T b).ne
  have hlog : Real.log (rootExtensionHaar T b (c0QLattice T b)).toReal =
      (s1915LocalDegree T b : ℝ) * Real.log ‖c0QHat T b‖ +
        Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal := by
    rw [qhat_haar_scaling_actual T b, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (le_of_lt (pow_pos hqpos _)),
      Real.log_mul (pow_pos hqpos _).ne' hOpos.ne', Real.log_pow]
  have hdne : (s1915LocalDegree T b : ℝ) ≠ 0 := by
    exact_mod_cast (local_degree_pos T b).ne'
  rw [hlog]
  field_simp [hdne]
  ring

#print axioms qhat_haar_scaling_actual
#print axioms local_degree_pos
#print axioms qhat_lattice_measure_pos
#print axioms qhat_lattice_measure_lt_top
#print axioms qhat_signed_readout_eq_log_norm

end LeanFormal.IUT.ThreeGapClosure20261114
