import tmp.sheaf.n8.closure.SourceThetaToIQ
import tmp.sheaf.n8.closure.C6ActualIQData
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Actual `1,circ U` Theta-hull identification

Self-contained file connecting the actual C6 IQ carrier to the paper-level
`1,circ U` hull surface:

* actual `IQHullLogVolumeInterface` over `C6IQCarrier C3.tensorPlaces
  C3.tensorTuple`;
* actual source theta image `image C3 D n`;
* actual C6 canonical hull and actual C6 Haar log-volume;
* actual finite procession `SignedLabel l.value` with normalized weights;
* actual weighted `ENNReal` procession average;
* actual hull log-volume `interface.logVolume interface.hull` (finite).

## Exact missing fields (not assumed)

* `image_subset_hull`: source theta image lies in the C6 canonical hull (C7
  theta-containment donor).
* `imageSet_compact`, `hull_compact`: compactness for a `1,circ` topology;
  the actual C6 block here carries only its measurable/Borel structure.
* `unitRegion_logShell`: the paper's ring-of-integers/log-shell unit region,
  not the C6 R1 canonical-hull placeholder.
* `unitRegion_normalization`: `logVolume O = 1` for the paper's normalized
  Haar volume; C6 proves only finiteness.
* `paper_logVolume_normalization`: the procession-normalized signed
  `-|log Theta|`, not merely the C6 Haar log-volume.
* `literal_IQ_identification`: the C6 tensor block equals the literal
  `IQ(S+_{j+1}; n,circ D^vdash_{vQ})` carrier.

No `PUnit`, `True`, `sorry`, or axiom. No inhabitant of the complete
identification structure is asserted; actual interface/data are constructed,
and the missing paper-level propositions are exact fields.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT
namespace XiFPaperThetaHullIdentification

open scoped BigOperators
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- The zero signed label, used only for nonemptiness of the finite procession. -/
def zeroSignedLabel (l : PrimeGeFive) : SignedLabel l.value :=
  ⟨0, by
    have hle : (0 : Int) ≤ (lStar l.value : Int) :=
      by exact_mod_cast (Nat.zero_le (lStar l.value))
    exact ⟨neg_nonpos.mpr hle, hle⟩⟩

/-- The actual finite signed-label procession with normalized weights. -/
structure FiniteProcession (l : PrimeGeFive) where
  weight : SignedLabel l.value → Real
  weight_pos : ∀ j : SignedLabel l.value, 0 < weight j
  weight_sum_one : (∑ j : SignedLabel l.value, weight j) = 1

namespace FiniteProcession

variable (P : FiniteProcession l)

theorem card_labels : Fintype.card (SignedLabel l.value) = l.value :=
  SignedLabel.card_signedLabel l

theorem labels_nonempty : Nonempty (SignedLabel l.value) :=
  ⟨zeroSignedLabel l⟩

theorem weight_nonneg (j : SignedLabel l.value) : 0 ≤ P.weight j :=
  le_of_lt (P.weight_pos j)

end FiniteProcession

/-- Canonical uniform procession. -/
noncomputable def canonicalProcession : FiniteProcession l where
  weight := fun _ => ((Fintype.card (SignedLabel l.value) : Real))⁻¹
  weight_pos := by
    intro j
    apply inv_pos.mpr
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨zeroSignedLabel l⟩)
  weight_sum_one := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [SignedLabel.card_signedLabel l]
    have hl : (l.value : Real) ≠ 0 := by
      have h5 : 5 ≤ l.value := l.ge_five
      exact_mod_cast (Nat.ne_of_gt (by omega : 0 < l.value))
    exact mul_inv_cancel₀ hl

/-- Weighted `ENNReal` average over the actual finite procession. -/
def processionAverage (P : FiniteProcession l)
    (f : SignedLabel l.value → ENNReal) : ENNReal :=
  ∑ j : SignedLabel l.value, ENNReal.ofReal (P.weight j) * f j

theorem processionAverage_nonneg (P : FiniteProcession l)
    (f : SignedLabel l.value → ENNReal) :
    0 ≤ processionAverage P f := by
  unfold processionAverage
  exact Finset.sum_nonneg (fun j _ => bot_le)

variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (D : SourceThetaIQInterface (I := I) C3)
variable (n : ThetaPilotCarrier l)
variable [MeasurableSpace (C6IQCarrier C3.tensorPlaces C3.tensorTuple)]
variable [BorelSpace (C6IQCarrier C3.tensorPlaces C3.tensorTuple)]
variable (mu : Measure (C6IQCarrier C3.tensorPlaces C3.tensorTuple))
variable [Measure.IsAddHaarMeasure mu]

abbrev IQX (C3 : SourcePilotRegionData (l := l) (V := V) I) : Type (max ua uv) :=
  C6IQCarrier C3.tensorPlaces C3.tensorTuple

/-- The actual C6 interface's hull equals the actual C6 canonical hull. -/
theorem actualC6_iqInterface_hull_eq :
    (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).iqInterface.hull =
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).hull := by
  dsimp [C6ActualIQData.actual]
  rw [arithmeticTupleIQHullLogVolumeInterface_hull]

/-- Actual interface with the source theta image, conditional exactly on the
C7 theta-containment donor. -/
def actualInterface
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (D : SourceThetaIQInterface (I := I) C3)
    (n : ThetaPilotCarrier l)
    [MeasurableSpace (C6IQCarrier C3.tensorPlaces C3.tensorTuple)]
    [BorelSpace (C6IQCarrier C3.tensorPlaces C3.tensorTuple)]
    (mu : Measure (C6IQCarrier C3.tensorPlaces C3.tensorTuple))
    [Measure.IsAddHaarMeasure mu]
    (hImage : image (I := I) C3 D n ⊆
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).hull) :
    IQHullLogVolumeInterface (IQX C3) :=
  let B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu
  have hh : B.iqInterface.hull = B.hull :=
    actualC6_iqInterface_hull_eq C3 mu
  { imageSet := image (I := I) C3 D n
    hull := B.hull
    imageSet_subset_hull := hImage
    logVolume := B.iqInterface.logVolume
    logVolume_mono := B.iqInterface.logVolume_mono
    unitRegion := B.iqInterface.unitRegion
    scaleShift := B.iqInterface.scaleShift
    hull_subset_scaleShift := by
      rw [← hh]
      exact B.iqInterface.hull_subset_scaleShift
    unitRegion_logVolume_lt_top := B.iqInterface.unitRegion_logVolume_lt_top
    scaleShift_unitRegion_logVolume_le := B.iqInterface.scaleShift_unitRegion_logVolume_le }

@[simp] theorem actualInterface_imageSet
    (hImage : image (I := I) C3 D n ⊆
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).hull) :
    (actualInterface C3 D n mu hImage).imageSet =
      image (I := I) C3 D n := rfl

@[simp] theorem actualInterface_hull
    (hImage : image (I := I) C3 D n ⊆
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).hull) :
    (actualInterface C3 D n mu hImage).hull =
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).hull := rfl

theorem actualInterface_hull_logVolume_lt_top
    (hImage : image (I := I) C3 D n ⊆
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).hull) :
    (actualInterface C3 D n mu hImage).logVolume
      (actualInterface C3 D n mu hImage).hull < ⊤ :=
  IQHullLogVolumeInterface.hull_logVolume_lt_top
    (actualInterface C3 D n mu hImage)

theorem actualInterface_imageSet_logVolume_le_hull
    (hImage : image (I := I) C3 D n ⊆
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).hull) :
    (actualInterface C3 D n mu hImage).logVolume
      (actualInterface C3 D n mu hImage).imageSet ≤
    (actualInterface C3 D n mu hImage).logVolume
      (actualInterface C3 D n mu hImage).hull :=
  IQHullLogVolumeInterface.imageSet_logVolume_le_hull
    (actualInterface C3 D n mu hImage)

/-- Actual hull log-volume of the interface. -/
def actualHullLogVolume (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (interface : IQHullLogVolumeInterface (IQX C3)) : ENNReal :=
  interface.logVolume interface.hull

theorem actualHullLogVolume_lt_top
    (interface : IQHullLogVolumeInterface (IQX C3)) :
    actualHullLogVolume C3 interface < ⊤ :=
  IQHullLogVolumeInterface.hull_logVolume_lt_top interface

theorem actualHullLogVolume_eq_interface
    (interface : IQHullLogVolumeInterface (IQX C3)) :
    actualHullLogVolume C3 interface = interface.logVolume interface.hull := rfl

/-- The actual identification surface: actual C6 interface/data plus exact
missing paper-level fields. -/
structure ThetaHullIdentificationActual
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (D : SourceThetaIQInterface (I := I) C3)
    (n : ThetaPilotCarrier l)
    [MeasurableSpace (C6IQCarrier C3.tensorPlaces C3.tensorTuple)]
    [BorelSpace (C6IQCarrier C3.tensorPlaces C3.tensorTuple)]
    (mu : Measure (C6IQCarrier C3.tensorPlaces C3.tensorTuple))
    [Measure.IsAddHaarMeasure mu] where
  image_subset_hull :
    image (I := I) C3 D n ⊆
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).hull
  interface : IQHullLogVolumeInterface (C6IQCarrier C3.tensorPlaces C3.tensorTuple)
  interface_imageSet_eq : interface.imageSet = image (I := I) C3 D n
  interface_hull_eq :
    interface.hull = (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).hull
  topology : TopologicalSpace (C6IQCarrier C3.tensorPlaces C3.tensorTuple)
  imageSet_compact : @IsCompact (C6IQCarrier C3.tensorPlaces C3.tensorTuple) topology
    interface.imageSet
  hull_compact : @IsCompact (C6IQCarrier C3.tensorPlaces C3.tensorTuple) topology
    interface.hull
  procession : FiniteProcession l
  hullLogVolume : ENNReal
  hullLogVolume_eq : hullLogVolume = interface.logVolume interface.hull
  processionAverageLogVolume : ENNReal
  unitRegion_logShell : Prop
  unitRegion_normalization : Prop
  paper_logVolume_normalization : Prop
  literal_IQ_identification : Prop

namespace ThetaHullIdentificationActual

variable {C3 : SourcePilotRegionData (l := l) (V := V) I}
variable {D : SourceThetaIQInterface (I := I) C3}
variable {n : ThetaPilotCarrier l}
variable [MeasurableSpace (C6IQCarrier C3.tensorPlaces C3.tensorTuple)]
variable [BorelSpace (C6IQCarrier C3.tensorPlaces C3.tensorTuple)]
variable {mu : Measure (C6IQCarrier C3.tensorPlaces C3.tensorTuple)}
variable [Measure.IsAddHaarMeasure mu]

theorem interface_image_subset_hull
    (T : ThetaHullIdentificationActual (I := I) C3 D n mu) :
    T.interface.imageSet ⊆ T.interface.hull :=
  T.interface.imageSet_subset_hull

theorem hullLogVolume_lt_top
    (T : ThetaHullIdentificationActual (I := I) C3 D n mu) :
    T.hullLogVolume < ⊤ := by
  rw [T.hullLogVolume_eq]
  exact IQHullLogVolumeInterface.hull_logVolume_lt_top T.interface

theorem imageSet_logVolume_le_hullLogVolume
    (T : ThetaHullIdentificationActual (I := I) C3 D n mu) :
    T.interface.logVolume T.interface.imageSet ≤ T.hullLogVolume := by
  rw [T.hullLogVolume_eq]
  exact IQHullLogVolumeInterface.imageSet_logVolume_le_hull T.interface

theorem procession_nonempty
    (T : ThetaHullIdentificationActual (I := I) C3 D n mu) :
    Nonempty (SignedLabel l.value) := by
  exact ⟨zeroSignedLabel l⟩

end ThetaHullIdentificationActual

end XiFPaperThetaHullIdentification
end LeanFormal.IUT

end
