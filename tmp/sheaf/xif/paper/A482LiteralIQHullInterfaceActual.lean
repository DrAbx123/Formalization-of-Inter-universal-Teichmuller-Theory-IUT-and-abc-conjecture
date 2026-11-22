/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.A482LiteralCarrierAxiomsActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction

/-! # A482: IQ hull log-volume interface on the literal carrier -/

namespace LeanFormal.IUT.XiFPaper.LiteralCarrierAxiomsActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.GlobalIQHullInterfaceActual
open MeasureTheory

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [forall i, Fintype (C3.tensorPlaceIndex i)]

/-- The literal carrier carries an `IQHullLogVolumeInterface`: its image and hull are the
scaled unit region, and the log-volume is the product Haar log-volume.  The paper-level
Theta-pilot image comparison is a separate rung; this instance records the carrier/hull
axioms (finiteness, normalization) on the literal ambient. -/
noncomputable def literalIQHullInterface (j : Nat) (lam : GlobalIQAmbient C3 j) :
    IQHullLogVolumeInterface (GlobalIQAmbient C3 j) where
  imageSet := literalIQHull C3 j lam
  hull := literalIQHull C3 j lam
  imageSet_subset_hull := by
    intro x hx
    exact hx
  logVolume := globalIQLogVolume C3 j
  logVolume_mono := globalIQLogVolume_mono C3 j
  unitRegion := globalIQUnitRegion C3 j
  scaleShift := literalIQScale C3 j lam
  hull_subset_scaleShift := by
    intro x hx
    exact hx
  unitRegion_logVolume_lt_top := (literalCarrierAxioms_holds C3 j).unitRegion_logVolume_lt_top
  scaleShift_unitRegion_logVolume_le := 
    le_of_eq ((literalCarrierAxioms_holds C3 j).scaleShift_unitRegion_logVolume_eq lam)

theorem literalIQHullInterface_logVolume (j : Nat) (lam : GlobalIQAmbient C3 j) :
    (literalIQHullInterface C3 j lam).logVolume = globalIQLogVolume C3 j := rfl

end LeanFormal.IUT.XiFPaper.LiteralCarrierAxiomsActual
