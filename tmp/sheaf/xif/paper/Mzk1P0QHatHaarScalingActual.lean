/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.three_gap_closure_20261114.QhatHaarScalingReuse
import Mathlib.Tactic
/-! # Re-export of the official root qhat Haar scaling -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0QHatHaarScalingActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
theorem qhatHaarScaling_unconditional {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData l)
    [Fintype (Bad (nativePlaceSelection T))]
    (b : Bad (nativePlaceSelection T)) :
    rootExtensionHaar T b (c0QLattice T b) =
      ENNReal.ofReal (‖c0QHat T b‖ ^ s1915LocalDegree T b) *
        rootExtensionHaar T b (rootExtensionUnitBall T b) :=
  LeanFormal.IUT.ThreeGapClosure20261114.qhat_haar_scaling_actual T b
theorem local_degree_pos {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData l)
    [Fintype (Bad (nativePlaceSelection T))]
    (b : Bad (nativePlaceSelection T)) : 0 < s1915LocalDegree T b :=
  LeanFormal.IUT.ThreeGapClosure20261114.local_degree_pos T b
theorem qhat_lattice_measure_pos {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData l)
    [Fintype (Bad (nativePlaceSelection T))]
    (b : Bad (nativePlaceSelection T)) :
    0 < rootExtensionHaar T b (c0QLattice T b) :=
  LeanFormal.IUT.ThreeGapClosure20261114.qhat_lattice_measure_pos T b
theorem qhat_lattice_measure_lt_top {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData l)
    [Fintype (Bad (nativePlaceSelection T))]
    (b : Bad (nativePlaceSelection T)) :
    rootExtensionHaar T b (c0QLattice T b) < ⊤ :=
  LeanFormal.IUT.ThreeGapClosure20261114.qhat_lattice_measure_lt_top T b
theorem qhat_signed_readout_eq_log_norm {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData l)
    [Fintype (Bad (nativePlaceSelection T))]
    (b : Bad (nativePlaceSelection T)) :
    (1 / (s1915LocalDegree T b : ℝ)) *
        (Real.log (rootExtensionHaar T b (c0QLattice T b)).toReal -
          Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal) =
      Real.log ‖c0QHat T b‖ :=
  LeanFormal.IUT.ThreeGapClosure20261114.qhat_signed_readout_eq_log_norm T b
end LeanFormal.IUT.XiFPaper.Mzk1P0QHatHaarScalingActual
end