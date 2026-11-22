import tmp.sheaf.xif.paper.S2723GlobalIQHullActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1NormalizedComparisonRegionActual — IUT IV comparison region on the literal carrier

Real object, not a Prop placeholder: the normalized comparison region
`O ∪ {point}` on the literal global IQ carrier.  `O = globalIQUnitRegion` is the
tensor integral/log-shell region built from the actual finite-place family
`globalIQPlaces` (finite places of the literal carrier); no value model, no Prop
field.  The file proves the region is exactly the core
`normalizedComparisonRegion` of the global IQ hull interface (where scaleShift is
identity), has the point as a member, and has finite Haar log-volume. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1NormalizedComparisonRegionActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.S2723GlobalIQHullActual
open MeasureTheory

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [∀ i, Fintype (C3.tensorPlaceIndex i)]

/-- The literal IUT IV normalized comparison region data: the point together with
the finite-place unit region.  The data field is a point of the actual global IQ
ambient; the region is derived below, with no Prop content in the structure. -/
structure NormalizedComparisonRegion (j : Nat) where
  point : GlobalIQAmbient (C3 := C3) j

namespace NormalizedComparisonRegion

variable {j : Nat} (R : NormalizedComparisonRegion C3 j)

/-- The actual comparison region: the finite-place unit region `O` together with
the named point. -/
def region : Set (GlobalIQAmbient (C3 := C3) j) :=
  globalIQUnitRegion (C3 := C3) j ∪ {R.point}

theorem point_mem : R.point ∈ R.region :=
  Set.mem_union_right _ (Set.mem_singleton _)

theorem unitRegion_subset :
    globalIQUnitRegion (C3 := C3) j ⊆ R.region :=
  Set.subset_union_left

end NormalizedComparisonRegion

/-- The default literal comparison region at the identity log-shell point. -/
def normalizedComparisonRegionDefault (j : Nat) :
    NormalizedComparisonRegion C3 j :=
  ⟨globalIQLogShellPoint (C3 := C3) j⟩

/-- The constructed region is exactly the core `normalizedComparisonRegion` of the
global IQ hull interface at the same point (scaleShift is identity there). -/
theorem normalizedComparisonRegionDefault_region_eq_core (j : Nat) :
    (normalizedComparisonRegionDefault (C3 := C3) j).region =
      normalizedComparisonRegion
        (globalIQHullInterface (C3 := C3) j)
        (fun _ _ _ => globalIQLogShellPoint (C3 := C3) j) 0 0 0 := by
  simp [NormalizedComparisonRegion.region, normalizedComparisonRegion,
    globalIQHullInterface]

/-- The literal comparison region has finite Haar log-volume. -/
theorem normalizedComparisonRegionDefault_logVolume_lt_top (j : Nat) :
    globalIQLogVolume (C3 := C3) j
      (normalizedComparisonRegionDefault (C3 := C3) j).region < ⊤ := by
  refine lt_of_le_of_lt
    (globalIQLogVolume_mono (C3 := C3) j
      (NormalizedComparisonRegion.unitRegion_subset
        (normalizedComparisonRegionDefault (C3 := C3) j)))
    (globalIQUnitRegion_logVolume_lt_top (C3 := C3) j)

end LeanFormal.IUT.XiFPaper.Mzk1NormalizedComparisonRegionActual

end
