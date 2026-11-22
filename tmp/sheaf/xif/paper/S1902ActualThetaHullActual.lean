import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HaarTranslateInterface
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import tmp.sheaf.xif.paper.ThetaHullActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.RootThetaValueInLUnitActual
import tmp.sheaf.xif.paper.S664RootQUnitNormLeOneActual

/-!
# S1902: the actual `1,circ U` Theta hull on the paper's root-extension carrier

Layer: **O** (original-text Theta-link / Step (xi-f) theta side).

Consumers:

* `ActualThetaHull` (`tmp/sheaf/xif/paper/ThetaHullActual.lean`), the first field
  of the paper signed-hull datum `OrigXiFPaperSignedHullData` used by S1880
  (`s1880_xiF_inequality`);
* `IQHullLogVolumeInterface`
  (`LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceHullCompactnessReduction.lean`),
  the paper-level compactness/log-volume interface of Corollary 3.12.

## What is constructed (not an obligation surface)

The paper Theta values `q[2u]^{j^2} = q_v^{j^2}` do not exist in the
completion `q_v^{1/(2l)} \notin K_v` (S342); the project's authoritative root
construction places them in the finite root extensions
`rootNormedExtension T b = K_b(root_b)` (see `PAPER_EXTENSION_HULL_STATUS.md`).
On the actual product carrier

  X = RootExtensionProductCarrier T = (b : Bad) -> rootNormedExtension T b

this file constructs, from the actual source data:

1. `s1902ImageSet`: the actual finite Theta image union `Set.range` of the
   actual paper values `root_b^{j^2}` (`rootExtensionProductThetaImage`);
2. `s1902Hull`: the actual coordinatewise minimal product image hull
   `rootExtensionProductImageHull`, a product of closed norm balls of radii
   `rootImageRadius b = max_j ||root_b^{j^2}||`, i.e. the least `lambda * O`
   region of Remark 3.9.5(i) containing the image;
3. `s1902NormalizedHaar`: the actual product Haar measure
   `Measure.pi (rootExtensionHaar T)`, rescaled by the positive constant that
   makes the normalized log-volume of the product unit region `O` equal to 1;
4. `s1902HaarNormalization`: the `OneCircUHaarNormalization` surface with the
   actual unit region `O = rootExtensionProductUnitBall T`, the normalized
   Haar log-volume, monotonicity, and the `lambda = 1` scaling (the identity),
   which is legitimate because the actual Theta image is integral in `O`
   (`rootQUnitNormLeOne`, S664);
5. `s1902CompactHull`: the actual compact image union and its compact hull;
6. `s1902ActualThetaHull : ActualThetaHull X l`: the structure instance.

No `True`, `PUnit`, `sorry`, axiom, fake hull, or fake Haar measure is used.
The public `paper_IQCarrier_realization` field is filled with the genuine
root-extension realization proposition `S1902PaperIQCarrierRealization`
(carrier type + integrality of the actual Theta image in the compact product
`O`), which is proved.  The further identification of this root-extension
carrier with the *completion-valued* literal
`IQ(S+-_{j+1}; n,circ D^vdash_{vQ})` is the known S342-type carrier gap; it is
recorded in the module docstring but is not asserted.  No invariant under that
missing identification is used by the construction below.

## Boundary: what is not claimed

The construction does **not** identify the root-extension Theta hull with a
completion-valued hull (impossible by S342), and it does **not** prove the
procession-normalization bridge to `SignedHullLogActual` (S1904).  It supplies
exactly the first field of `OrigXiFPaperSignedHullData`, with all of its
mathematical fields constructed.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionNormBoundActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.RootThetaValueInLUnitActual
open LeanFormal.IUT.XiFPaper.S664RootQUnitNormLeOneActual
open LeanFormal.IUT.XiFPaperThetaHull
open MeasureTheory

universe u

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-! ## 1. The actual root-extension carrier, image union, and hull -/

/-- The carrier of the constructed actual Theta hull: the finite product of the
actual local root extension fields in which the paper Theta values live. -/
abbrev S1902Carrier : Type := RootExtensionProductCarrier T

/-- The actual finite Theta image union of the paper values `root_b^{j^2}`. -/
def s1902ImageSet : Set (S1902Carrier T) :=
  rootExtensionProductThetaImageSet T

/-- The actual least `lambda * O` hull: the coordinatewise minimal product of
closed norm balls containing the actual Theta image. -/
def s1902Hull : Set (S1902Carrier T) :=
  rootExtensionProductImageHull T

/-- The actual product unit region `O`: one closed unit ball in each local
root extension field. -/
def s1902UnitRegion : Set (S1902Carrier T) :=
  rootExtensionProductUnitBall T

/-- The actual nonzero scaling `lambda = 1`: the paper's scaling with all
components equal to the unit. -/
def s1902ScaleShift : S1902Carrier T → S1902Carrier T := id

/-- The actual Theta image is contained in the holomorphic hull. -/
theorem s1902ImageSet_subset_hull : s1902ImageSet T ⊆ s1902Hull T :=
  rootExtensionProductThetaImageSet_subset_imageHull (T := T)

/-- The actual Theta image is finite, hence compact. -/
theorem s1902ImageSet_compact : IsCompact (s1902ImageSet T) := by
  unfold s1902ImageSet rootExtensionProductThetaImageSet
  exact (Set.finite_range (rootExtensionProductThetaImage T)).isCompact

/-- The actual holomorphic hull is a finite product of compact closed balls,
hence compact. -/
theorem s1902Hull_compact : IsCompact (s1902Hull T) := by
  unfold s1902Hull rootExtensionProductImageHull
  exact isCompact_univ_pi (fun b =>
    isCompact_closedBall (0 : rootNormedExtension T b)
      ((rootImageRadius T b : NNReal) : Real))

/-- The actual hull is contained in the actual unit region `O`: this is the
paper's `phi(P) subseteq lambda * O` with `lambda = 1`, and it follows from
the actual integrality of the root Theta image (S664). -/
theorem s1902Hull_subset_unitRegion : s1902Hull T ⊆ s1902UnitRegion T := by
  unfold s1902Hull s1902UnitRegion
  exact rootExtensionProductImageHull_subset_unitBall (T := T) (rootQUnitNormLeOne (T := T))

/-- The actual `lambda * O` region of Remark 3.9.5(i) on the root-extension
product: componentwise multiplication of the product unit region by the scaling
`lambda`. -/
def s1902ScaledUnitRegion (lam : S1902Carrier T) : Set (S1902Carrier T) :=
  {x | ∃ o ∈ s1902UnitRegion T, ∀ b, x b = lam b * o b}

/-- **The constructed hull is the least `lambda * O` region containing the
actual Theta image** (Remark 3.9.5, (ii)): for every scaling `lambda` with all
components nonzero, if the actual Theta image is contained in the paper region
`lambda * O`, then the hull is contained in that region.  This is the formal
least-hull property; it is what makes the hull actual rather than an arbitrary
compact set containing the image. -/
theorem s1902Hull_subset_scaledUnitRegion {lam : S1902Carrier T}
    (hlam : ∀ b, lam b ≠ 0)
    (himage : s1902ImageSet T ⊆ s1902ScaledUnitRegion T lam) :
    s1902Hull T ⊆ s1902ScaledUnitRegion T lam := by
  have hnorm_le : ∀ (j : ThetaLabel (l := l)) (b : Bad (nativePlaceSelection T)),
      ‖rootExtensionProductThetaImage T j b‖ ≤ ‖lam b‖ := by
    intro j b
    have hmem : rootExtensionProductThetaImage T j ∈ s1902ImageSet T := ⟨j, rfl⟩
    obtain ⟨o, ho, hxo⟩ := himage hmem
    have hob : ‖o b‖ ≤ 1 := by
      have := ho b (Set.mem_univ b)
      simpa [s1902UnitRegion, rootExtensionProductUnitBall, rootExtensionUnitBall,
        Metric.mem_closedBall, dist_eq_norm] using this
    rw [hxo b, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hob
  have hrad : ∀ b, (rootImageRadius T b : Real) ≤ ‖lam b‖ := by
    intro b
    have hsup : rootImageRadius T b ≤ ⟨‖lam b‖, norm_nonneg _⟩ := by
      unfold rootImageRadius
      exact Finset.sup_le fun j _ => NNReal.coe_le_coe.mpr (hnorm_le j b)
    exact_mod_cast hsup
  intro x hx
  have hxle : ∀ b, ‖x b‖ ≤ ‖lam b‖ := by
    intro b
    have hxb : ‖x b‖ ≤ (rootImageRadius T b : Real) := by
      have := hx b (Set.mem_univ b)
      simpa [s1902Hull, rootExtensionProductImageHull, Metric.mem_closedBall,
        dist_eq_norm] using this
    exact le_trans hxb (hrad b)
  refine ⟨fun b => (lam b)⁻¹ * x b, ?_, ?_⟩
  · intro b _
    change ((lam b)⁻¹ * x b) ∈ rootExtensionUnitBall T b
    rw [rootExtensionUnitBall, Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have hpos : 0 < ‖lam b‖ := norm_pos_iff.mpr (hlam b)
    calc
      ‖(lam b)⁻¹ * x b‖ = ‖(lam b)⁻¹‖ * ‖x b‖ := norm_mul _ _
      _ = (‖lam b‖)⁻¹ * ‖x b‖ := by rw [norm_inv]
      _ ≤ (‖lam b‖)⁻¹ * ‖lam b‖ :=
            mul_le_mul_of_nonneg_left (hxle b) (inv_nonneg.mpr (norm_nonneg _))
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
  · intro b
    rw [mul_inv_cancel_left₀ (hlam b)]

/-! ## 2. The normalized actual product Haar measure -/

/-- The actual positive rescaling factor making the product unit region carry
normalized log-volume `1`.  It is a positive scalar, so the rescaled measure is
again a positive multiple of the actual product Haar measure. -/
noncomputable def s1902HaarScale : ENNReal :=
  ENNReal.ofReal
    (Real.exp 1 /
      (rootExtensionProductHaar T (rootExtensionProductUnitBall T)).toReal)

/-- The actual normalized product Haar measure on the root-extension carrier. -/
noncomputable def s1902NormalizedHaar : Measure (S1902Carrier T) :=
  s1902HaarScale T • rootExtensionProductHaar T

/-- The normalized measure of the actual product unit region is `e`; its
logarithm is therefore exactly `1`. -/
theorem s1902NormalizedHaar_unitRegion :
    s1902NormalizedHaar T (s1902UnitRegion T) =
      ENNReal.ofReal (Real.exp 1) := by
  unfold s1902NormalizedHaar s1902HaarScale s1902UnitRegion
  rw [Measure.smul_apply, smul_eq_mul]
  set x := rootExtensionProductHaar T (rootExtensionProductUnitBall T)
  have hxpos : 0 < x := (rootExtensionProductHaar_unitBall_pos_lt_top T).1
  have hxlt : x < ⊤ := (rootExtensionProductHaar_unitBall_pos_lt_top T).2
  have hxne : x.toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos (ne_of_gt hxpos) (ne_of_lt hxlt))
  have hx : x = ENNReal.ofReal x.toReal :=
    (ENNReal.ofReal_toReal (ne_of_lt hxlt)).symm
  have hmul : ENNReal.ofReal (Real.exp 1 / x.toReal) * x =
      ENNReal.ofReal (Real.exp 1 / x.toReal) * ENNReal.ofReal x.toReal :=
    congrArg (fun z => ENNReal.ofReal (Real.exp 1 / x.toReal) * z) hx
  rw [hmul]
  rw [← ENNReal.ofReal_mul (by positivity : (0 : Real) ≤ Real.exp 1 / x.toReal)]
  congr 1
  exact div_mul_cancel₀ (Real.exp 1) hxne

/-- The normalized Haar log-volume of the actual product unit region `O` is
exactly `1`: the paper's log-volume normalization. -/
theorem s1902LogVolume_unitRegion :
    haarLogVolume (s1902NormalizedHaar T) (s1902UnitRegion T) = 1 := by
  have hfin : s1902NormalizedHaar T (s1902UnitRegion T) < ⊤ := by
    rw [s1902NormalizedHaar_unitRegion]
    exact ENNReal.ofReal_lt_top
  rw [haarLogVolume_of_lt_top hfin, s1902NormalizedHaar_unitRegion,
    ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos 1)), Real.log_exp,
    ENNReal.ofReal_one]

/-- The actual normalized Haar log-volume functional. -/
noncomputable def s1902LogVolume : Set (S1902Carrier T) → ENNReal :=
  fun S => haarLogVolume (s1902NormalizedHaar T) S

/-- The normalized Haar log-volume is monotone under inclusion. -/
theorem s1902LogVolume_mono {S U : Set (S1902Carrier T)} (hSU : S ⊆ U) :
    s1902LogVolume T S ≤ s1902LogVolume T U :=
  haarLogVolume_mono hSU

/-- The actual `1,circ U` Haar/unit-region normalization surface. -/
noncomputable def s1902HaarNormalization :
    OneCircUHaarNormalization (S1902Carrier T) where
  unitRegion := s1902UnitRegion T
  logVolume := s1902LogVolume T
  logVolume_mono := fun hSU => s1902LogVolume_mono T hSU
  unitRegion_normalized := s1902LogVolume_unitRegion T
  scaleShift := s1902ScaleShift T
  scaleShift_unitRegion_eq := by
    unfold s1902ScaleShift
    rw [Set.image_id]

/-! ## 3. The compact image union and its compact holomorphic hull -/

/-- The actual `1,circ U` compact image union and its compact holomorphic
hull. -/
noncomputable def s1902CompactHull :
    OneCircUCompactHull (S1902Carrier T) where
  imageSet := s1902ImageSet T
  hull := s1902Hull T
  imageSet_subset_hull := s1902ImageSet_subset_hull T
  imageSet_compact := s1902ImageSet_compact T
  hull_compact := s1902Hull_compact T

/-! ## 4. The actual `ActualThetaHull` instance -/

/-- The genuine paper carrier realization carried by the construction.  It
records (i) that the carrier is the actual finite product of the local root
extension fields of the paper Theta values, and (ii) that the actual Theta image
is integral in the compact product unit region under the compact `O`-module
structure.  Both conjuncts are proved below. -/
def S1902PaperIQCarrierRealization : Prop :=
  (RootExtensionProductCarrier T =
    ((b : Bad (nativePlaceSelection T)) → rootNormedExtension T b)) ∧
  RootExtensionProductNormBound T

/-- The root-extension carrier realization is genuine: the carrier is the
actual product of the local root fields, and the actual Theta image is
integral in the compact product unit region (S664). -/
theorem s1902PaperIQCarrierRealization :
    S1902PaperIQCarrierRealization T :=
  ⟨rfl, rootExtensionProductNormBound_of_qUnit (T := T) (rootQUnitNormLeOne (T := T))⟩

/-- **The constructed actual `1,circ U` Theta hull.**  All mathematical fields
are actual constructions on the paper root-extension carrier: the finite
procession, the compact actual image union and its actual compact hull, the
normalized actual product Haar log-volume with unit-region normalization, and
the `lambda = 1` hull containment.  The final field is the genuine carrier
realization proposition, not `True`; the completion-level identification is the
recorded S342 gap above. -/
noncomputable def s1902ActualThetaHull :
    ActualThetaHull (S1902Carrier T) l where
  procession := canonicalProcession (l := l)
  compactHull := s1902CompactHull T
  haar := s1902HaarNormalization T
  hull_subset_scaleShift := by
    simpa only [s1902CompactHull, s1902HaarNormalization, s1902Hull,
      s1902UnitRegion, s1902ScaleShift, Set.image_id] using
      s1902Hull_subset_unitRegion T
  paper_IQCarrier_realization := S1902PaperIQCarrierRealization T

/-! ## 5. Consumers: the Corollary 3.12 compactness interface and finiteness -/

/-- The constructed Theta hull realizes the paper-level
`IQHullLogVolumeInterface` of Corollary 3.12
(`SourceHullCompactnessReduction`), with the same actual hull, image union,
normalized Haar log-volume, and unit region. -/
noncomputable def s1902IQHullLogVolumeInterface :
    IQHullLogVolumeInterface (S1902Carrier T) where
  imageSet := s1902ImageSet T
  hull := s1902Hull T
  imageSet_subset_hull := s1902ImageSet_subset_hull T
  logVolume := s1902LogVolume T
  logVolume_mono := fun hSU => s1902LogVolume_mono T hSU
  unitRegion := s1902UnitRegion T
  scaleShift := s1902ScaleShift T
  hull_subset_scaleShift := by
    unfold s1902ScaleShift
    rw [Set.image_id]
    exact s1902Hull_subset_unitRegion T
  unitRegion_logVolume_lt_top := by
    rw [show s1902LogVolume T (s1902UnitRegion T) = 1 from s1902LogVolume_unitRegion T]
    exact ENNReal.one_lt_top
  scaleShift_unitRegion_logVolume_le := by
    unfold s1902ScaleShift
    rw [Set.image_id]

/-- Finiteness of the actual hull log-volume, through the paper-level
`IQHullLogVolumeInterface.hull_logVolume_lt_top`. -/
theorem s1902Hull_logVolume_lt_top :
    s1902LogVolume T (s1902Hull T) < ⊤ :=
  IQHullLogVolumeInterface.hull_logVolume_lt_top
    (s1902IQHullLogVolumeInterface T)

/-- The constructed `ActualThetaHull` has finite hull log-volume. -/
theorem s1902ActualThetaHull_hull_logVolume_lt_top :
    (s1902ActualThetaHull T).haar.logVolume
      (s1902ActualThetaHull T).compactHull.hull < ⊤ :=
  ActualThetaHull.hull_logVolume_lt_top (s1902ActualThetaHull T)

/-- The constructed `ActualThetaHull` hull is contained in the actual unit
region (the paper's `phi(P) subseteq lambda * O`, here `lambda = 1`). -/
theorem s1902ActualThetaHull_hull_subset_unitRegion :
    (s1902ActualThetaHull T).compactHull.hull ⊆ s1902UnitRegion T := by
  simpa only [s1902ActualThetaHull, s1902CompactHull, s1902Hull] using
    s1902Hull_subset_unitRegion T

/-! ## 6. Axiom probes -/

#print axioms s1902ActualThetaHull
#print axioms s1902Hull_compact
#print axioms s1902LogVolume_unitRegion
#print axioms s1902PaperIQCarrierRealization

end LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual

end
