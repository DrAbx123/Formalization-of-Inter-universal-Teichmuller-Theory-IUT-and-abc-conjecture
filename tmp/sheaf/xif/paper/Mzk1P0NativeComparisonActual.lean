/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0NativeReadoutActual
import tmp.sheaf.xif.paper.Mzk1S3137LReadoutActual
import tmp.sheaf.xif.paper.S1391C3LSourcePilotActual
import Mathlib.Tactic
/-! # P0.5: native comparison and L-side transfer (conditional, exact missing recorded) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0NativeComparisonActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeReadoutActual
open LeanFormal.IUT.XiFPaper.Mzk1S3137LReadoutActual
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
universe ua upi umon ui
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
/-- Native q≤theta target on the actual native core. -/
def NativeComparison : Prop := nativeQReadout T b ≤ nativeThetaReadout T b
/-- Single sufficient condition: nonnegative theta readout (q readout is ≤ 0). -/
theorem nativeComparison_of_theta_nonneg
    (h : 0 ≤ nativeThetaReadout T b) : NativeComparison T b :=
  le_trans (nativeQReadout_nonpos T b) h
variable {I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7)}
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
noncomputable def LQRead : Real :=
  qPilotLogVolumeReadingL (actualSourcePilotRegionDataL (I := I) place)
noncomputable def LThetaRead : Real :=
  thetaPilotHullLogVolumeRealL (actualSourcePilotRegionDataL (I := I) place)
def LComparison : Prop := LQRead (I := I) place ≤ LThetaRead (I := I) place
/-- If L-side q/theta scalars align with the native readouts, native comparison transfers. -/
theorem LComparison_of_nativeComparison
    (hq : LQRead (I := I) place = nativeQReadout T b)
    (hθ : LThetaRead (I := I) place = nativeThetaReadout T b)
    (h : NativeComparison T b) : LComparison (I := I) place := by
  unfold LComparison
  rw [hq, hθ]
  exact h
theorem LComparison_of_theta_nonneg
    (h : 0 ≤ LThetaRead (I := I) place) : LComparison (I := I) place :=
  le_trans (qPilotLogVolumeReadingL_nonpos _) h
def alignmentRows : List String :=
  ["q alignment missing: T->I native OriginalInput donor / place binding",
   "theta alignment missing: L Haar region vs native tensor Haar normalization",
   "sufficient: theta readout >= 0",
   "native->L transfer: explicit hq/hθ equalities"]
theorem alignmentRows_length : alignmentRows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P0NativeComparisonActual
end