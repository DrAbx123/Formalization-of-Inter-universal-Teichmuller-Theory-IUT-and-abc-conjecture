/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1S3137ThetaRawEqActual
import Mathlib.Tactic

/-! # P6-D5: S3137 block log-p factor sign (single cluster) -/
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1S3137ThetaRawEqActual
open MeasureTheory
open scoped Pointwise ENNReal
namespace LeanFormal.IUT.XiFPaper.Mzk1S3137ThetaBlockFactorNonposActual
variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance blockFactorMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance blockFactorBorelSpace :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

theorem thetaBlockLogFactor_nonpos : thetaBlockLogFactor C3 ≤ 0 := by
  unfold thetaBlockLogFactor
  have hp : (0:Real) ≤ Real.log (C3.p : Real) := by
    apply Real.log_nonneg
    exact_mod_cast (Nat.Prime.one_lt (Fact.out : Nat.Prime C3.p)).le
  have hdim : (0:Real) ≤ (c3TensorBlockDimension C3 : Real) := Nat.cast_nonneg _
  nlinarith

def blockFactorRows : List (String × String × String) :=
  [ ("thetaBlockLogFactor_nonpos", "block log-p factor <= 0", "PROVED") ]
theorem blockFactorRows_length : blockFactorRows.length = 1 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1S3137ThetaBlockFactorNonposActual
