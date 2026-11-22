/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.Mzk1P0NativeReadoutActual
import tmp.sheaf.xif.paper.Mzk1Ob33DetLineFromBadPrimeSourceActual
import Mathlib.Tactic
/-! # P0.6: explicit paper-line-bundle donor using q = qVFamily -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0NativeQDonorActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeReadoutActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33DetLineFromBadPrimeSourceActual
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
/-- Explicit q donor: the actual bad-prime line-bundle source plus the native qVFamily q. -/
structure NativeQDonor where
  source : PaperQPilotLineBundleSource (A := T.arithmetic)
  source_eq : source = badPrimeSource T
  q : FinitePlaceQCandidate (qVFamTensorPlace T b)
  q_eq : q = qVFamily T b
  qUnit : (Completion (qVFamTensorPlace T b))ˣ
  qUnit_eq : qUnit = Units.mk0 q.q q.q_ne_zero
noncomputable def actualNativeQDonor : NativeQDonor (T := T) (b := b) where
  source := badPrimeSource T
  source_eq := rfl
  q := qVFamily T b
  q_eq := rfl
  qUnit := Units.mk0 (qVFamily T b).q (qVFamily T b).q_ne_zero
  qUnit_eq := rfl
/-- q readout computed from the donor's explicit q. -/
noncomputable def donorQReadout : Real :=
  -|Real.log ‖(actualNativeQDonor (T := T) (b := b)).q.q‖|
/-- By construction, the donor q readout is the native q readout (no choice equality). -/
theorem donorQReadout_eq_native :
    donorQReadout (T := T) (b := b) = nativeQReadout T b := rfl
/-- The donor's line-bundle source is the actual bad-prime source. -/
theorem donor_source_eq :
    (actualNativeQDonor (T := T) (b := b)).source = badPrimeSource T := rfl
/-- The donor q is exactly qVFamily. -/
theorem donor_q_eq :
    (actualNativeQDonor (T := T) (b := b)).q = qVFamily T b := rfl
def rows : List String :=
  ["NativeQDonor: badPrimeSource + qVFamily q, no concreteQCandidate",
   "donorQReadout = nativeQReadout by rfl",
   "old concreteQCandidate/concreteC3Donor unchanged (historical)",
   "consumer switch: use donor.source / donor.q instead of concrete donor q"]
theorem rows_length : rows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P0NativeQDonorActual
end