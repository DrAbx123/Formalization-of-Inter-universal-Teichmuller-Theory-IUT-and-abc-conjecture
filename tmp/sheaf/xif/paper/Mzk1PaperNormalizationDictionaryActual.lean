/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import Mathlib.Tactic
/-! # GAP/interface: paper normalization dictionary raw Haar -> paper V -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1PaperNormalizationDictionaryActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open MeasureTheory
universe u
variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
structure PaperNormalizationData where
  rawLog : Real
  paperLog : Real
  blockDim : Nat
  blockDim_pos : 0 < blockDim
  shift : Real
  normalization_eq : rawLog = paperLog + (blockDim : Real) * shift
theorem paperLog_eq_raw_sub (D : PaperNormalizationData) :
    D.paperLog = D.rawLog - (D.blockDim : Real) * D.shift := by
  linarith [D.normalization_eq]
def PaperNormalizationDataRequired : Prop := Nonempty (PaperNormalizationData)
def rows : List String := ["rawLog", "paperLog", "blockDim+pos", "shift", "normalization_eq (NAMED)"]
theorem rows_length : rows.length = 5 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1PaperNormalizationDictionaryActual
end