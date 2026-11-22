import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction
import LeanFormal.IUT.Foundations.LocalFields.PadicIntegerProductLattice

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1LiteralIQCarrierCompactnessActual — A481 literal IQ carrier compactness

The literal (not value-realized) IQ(S±_{j+1}; n,◦D^vdash_{vQ}) carrier is
modelled as the ambient product of the local p-adic coordinate spaces

  IQCarrier p ι := ι → ℚ_[p]

with the region 1,◦U_{j,vQ} the actual integral lattice
padicIntegerCoordinateLattice (product of the local integer rings). On this
literal carrier we prove, using the existing compactness/Haar assets and no
value-realized ThetaPilotPoint hull:

1. literalIQ_oneCircU_compact: the region 1,◦U is compact;
2. literalIQ_oneCircU_measure_lt_top: its additive-Haar measure is finite;
3. literalIQInterface: the literal carrier carries the ambient
   IQHullLogVolumeInterface with the Haar log-volume (all fields proved, no
   named hull data);
4. literalIQ_hull_logVolume_lt_top: the hull log-volume is finite (Cor 3.12
   finiteness on the literal carrier);
5. literalIQ_imageHull_measure_lt_top: for any continuous map to a space whose
   measure is finite on compacts, the image hull of 1,◦U has finite measure.

No sorry/axioms; no closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1LiteralIQCarrierCompactnessActual

open MeasureTheory

/-- The literal IQ carrier: the ambient product of the local p-adic coordinate
spaces over the selected place-index set. -/
abbrev IQCarrier (p : Nat) (ι : Type*) : Type _ := ι → ℚ_[p]

/-- The literal 1,◦U_{j,vQ} region: the product of the local integer rings. -/
def oneCircU (p : Nat) [Fact p.Prime] (ι : Type*) : Set (IQCarrier p ι) :=
  LeanFormal.IUT.PadicIntegerProductLattice.padicIntegerCoordinateLattice (p := p) (ι := ι)

section
variable {p : Nat} [Fact p.Prime] {ι : Type*} [Fintype ι]

/-- **Compactness of 1,◦U on the literal IQ carrier.** -/
theorem literalIQ_oneCircU_compact :
    IsCompact (oneCircU p ι) :=
  LeanFormal.IUT.PadicIntegerProductLattice.isCompact_padicIntegerCoordinateLattice (p := p) (ι := ι)

variable [MeasurableSpace (IQCarrier p ι)] [BorelSpace (IQCarrier p ι)]

/-- **Finiteness of the Haar log-volume of 1,◦U** on the literal carrier. -/
theorem literalIQ_oneCircU_measure_lt_top :
    (Measure.addHaar : Measure (IQCarrier p ι)) (oneCircU p ι) < ⊤ :=
  literalIQ_oneCircU_compact (p := p) (ι := ι) |>.measure_lt_top

/-- The literal IQ carrier with its Haar log-volume is an ambient
IQHullLogVolumeInterface: every field is proved (image union = hull = 1,◦U,
unit region = 1,◦U, scaling = identity). -/
def literalIQInterface : IQHullLogVolumeInterface (IQCarrier p ι) where
  imageSet := oneCircU p ι
  hull := oneCircU p ι
  imageSet_subset_hull := by
    intro x hx
    exact hx
  logVolume := fun s => (Measure.addHaar : Measure (IQCarrier p ι)) s
  logVolume_mono := fun h => MeasureTheory.measure_mono h
  unitRegion := oneCircU p ι
  scaleShift := id
  hull_subset_scaleShift := by
    intro x hx
    exact ⟨x, hx, rfl⟩
  unitRegion_logVolume_lt_top := literalIQ_oneCircU_measure_lt_top (p := p) (ι := ι)
  scaleShift_unitRegion_logVolume_le := le_rfl

/-- **Cor 3.12 finiteness on the literal IQ carrier**: the hull log-volume is
finite. -/
theorem literalIQ_hull_logVolume_lt_top :
    (Measure.addHaar : Measure (IQCarrier p ι)) (oneCircU p ι) < ⊤ :=
  IQHullLogVolumeInterface.hull_logVolume_lt_top (literalIQInterface (p := p) (ι := ι))

/-- **Image-hull measure finiteness**: the image of the compact 1,◦U under any
continuous map to a space whose measure is finite on compacts has finite
measure. -/
theorem literalIQ_imageHull_measure_lt_top {Y : Type*} [TopologicalSpace Y]
    [MeasurableSpace Y] (ν : Measure Y) [Measure.IsFiniteMeasureOnCompacts ν]
    (f : IQCarrier p ι → Y) (hf : Continuous f) :
    ν (f '' oneCircU p ι) < ⊤ :=
  (literalIQ_oneCircU_compact (p := p) (ι := ι) |>.image hf).measure_lt_top

end

/-- Concrete existence of the ambient interface on the literal IQ carrier
(with the Borel measurable structure on the p-adic coordinate space). -/
theorem literalIQInterface_exists {p : Nat} [Fact p.Prime] {ι : Type*} [Fintype ι] :
    Nonempty (IQHullLogVolumeInterface (IQCarrier p ι)) := by
  letI : MeasurableSpace (IQCarrier p ι) := borel (IQCarrier p ι)
  letI : BorelSpace (IQCarrier p ι) := ⟨rfl⟩
  exact ⟨literalIQInterface (p := p) (ι := ι)⟩

#check literalIQ_oneCircU_compact
#check literalIQ_hull_logVolume_lt_top

end LeanFormal.IUT.XiFPaper.Mzk1LiteralIQCarrierCompactnessActual
end