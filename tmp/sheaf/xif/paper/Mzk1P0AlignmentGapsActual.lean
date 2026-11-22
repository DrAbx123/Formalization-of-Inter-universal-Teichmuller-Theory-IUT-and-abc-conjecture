/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0NativeReadoutActual
import tmp.sheaf.xif.paper.Mzk1P0NativeComparisonActual
import tmp.sheaf.xif.paper.Mzk1P2QNativeSourceArrowActual
import tmp.sheaf.n8.closure.C10BridgeProof
import tmp.sheaf.n8.closure.NativeInput
import Mathlib.Tactic
/-! # P0.5b: alignment gaps — q (T→I donors) and theta (Haar normalization factor) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0AlignmentGapsActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C10BridgeProof
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeReadoutActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeComparisonActual
open LeanFormal.IUT.XiFPaper.Mzk1P2QNativeSourceArrowActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
universe u ua upi umon ui
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
/-- Native q readout is exactly minus the P2 native q magnitude. -/
theorem nativeQReadout_eq_neg_p2NativeQMagnitude :
    nativeQReadout T b = -p2NativeQMagnitude T b := by
  unfold nativeQReadout p2NativeQMagnitude localLogMagnitude localSignedLog
  rw [abs_of_neg (Real.log_neg (qNorm_pos _) (qNorm_lt_one _))]
/-- Convergence with abc P2: if the P2 native-q/root-qhat reading gap holds, then
the native q readout is minus the root qhat log norm. -/
theorem nativeQReadout_eq_neg_rootQhatMagnitude_of_P2Gap
    (h : P2QNativeReadingGap T) :
    nativeQReadout T b = -p2RootQhatMagnitude T b := by
  rw [nativeQReadout_eq_neg_p2NativeQMagnitude, h b]
/-- Exact missing q-alignment datum: a native lattice over T plus the C10 donors. -/
def NativeLatticeMissing : Prop := Nonempty (NativeLattice T)
def rows : List String :=
  ["q: T→I requires NativeLattice T + NativeOriginalInputDonors (no constructor from T)",
   "q: C10 donor path gives OriginalInput from N8NativeInput, not from bare T",
   "P2: P2QNativeReadingGap links native q readout to root qhat magnitude"]
theorem rows_length : rows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P0AlignmentGapsActual
end