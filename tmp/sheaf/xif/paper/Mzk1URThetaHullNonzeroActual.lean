/- U-R C2 theta-upper: T-side nonzero-label adapter file (kurt).

Lead-approved heartbeat budget: THIS FILE ONLY uses maxHeartbeats 1000000, for the
same elaboration reason as the existing paper file PaperLevelXiFTargetActual.lean
(line 25): synthesizing typeclass instances for qVFamTensorBlock /
ArithmeticTensorTupleBlock (MeasurableSpace, BorelSpace, Measure) needs large
definitional-equality checks whose default 200000-heartbeat budget is
insufficient. This is elaboration cost of the EXISTING paper objects, not a way
to bypass any error: every theorem below is fully proved and checked with
#print axioms (only propext, Classical.choice, Quot.sound).

Contents: the actual T-side theta coefficient family and the nonzero-label
route object (urNonzeroLabelHull etc.), plus the honest semantic observation that
the actual all-label theta hull equals O_hol (theta = 0). The theta-upper route
target htheta uses the NONZERO-label hull, not the theta=0 observation. -/
import tmp.sheaf.xif.paper.Mzk1URThetaHullGenericActual
import tmp.sheaf.xif.paper.SignedLabelOneActual
import tmp.sheaf.xif.paper.Mzk1UCC3ProducerActual
import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual
import tmp.sheaf.xif.paper.Mzk1URThetaHullTensorActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompactHullScaling
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaHullNonzeroActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaHullGenericActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaHullTensorActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaHullUpperActual
open LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The actual T-side theta coefficient family: label j coefficient
gaussExponent j * actualRootCoeff. -/
noncomputable abbrev urThetaFamily :
    SignedLabel l.value → qVFamTensorV → ℝ :=
  thetaCoefficientFamily (ι := qVFamTensorV) (l := l)
    (actualRootCoeff (l := l) T b ())

/-- Nonzero signed labels (paper theta labels are nonzero). -/
abbrev urNonzeroLabel : Type := {j : SignedLabel l.value // j.1 ≠ 0}

/-- The nonzero-label theta region. -/
noncomputable def urNonzeroLabelRegion (j : urNonzeroLabel (l := l)) :
    Set (qVFamTensorBlock T b) :=
  actualRootThetaRegion (l := l) T b j.1

/-- The nonzero-label theta image set. -/
noncomputable def urNonzeroLabelImageSet : Set (qVFamTensorBlock T b) :=
  ⋃ j : urNonzeroLabel (l := l), urNonzeroLabelRegion (l := l) T b j

/-- The nonzero-label theta hull (route target object). -/
noncomputable def urNonzeroLabelHull : Set (qVFamTensorBlock T b) :=
  closure (urNonzeroLabelImageSet (l := l) T b)

/-- The nonzero-label theta hull log volume. -/
noncomputable def urNonzeroLabelHullLog (b' : Bad (nativePlaceSelection T)) : ℝ :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b') qVFamTensorTuple
    Measure.addHaar (urNonzeroLabelHull (l := l) T b')

/-- The nonzero-label theta hull log root (route htheta left-hand side). -/
noncomputable def urNonzeroThetaHullLogRoot : ℝ :=
  ∑ b' : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b' * urNonzeroLabelHullLog (l := l) T b'

/-! ## Honest semantic observation: the actual (all-label) theta hull is O_hol -/

/-- Every actual root theta region is contained in O_hol. -/
theorem urRootThetaImageSet_subset_holomorphic :
    actualRootThetaImageSet (l := l) T b ⊆
      (arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :
        Set (qVFamTensorBlock T b)) := by
  have hfam : actualRootThetaImageSet (l := l) T b =
      (⋃ j : SignedLabel l.value,
        thetaTensorScaledRegion (qVFamTensorPlaces T b) qVFamTensorTuple
          (urThetaFamily (l := l) T b j)) := rfl
  rw [hfam]
  exact thetaImageSet_subset_holomorphic (qVFamTensorPlaces T b) qVFamTensorTuple
    (actualRootCoeff (l := l) T b ()) (urRootCoeff_nonneg (l := l) T b)

/-- The zero-label region is O_hol itself. -/
theorem urRootThetaRegion_zero :
    actualRootThetaRegion (l := l) T b (thetaZeroLabel (l := l)) =
      (arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :
        Set (qVFamTensorBlock T b)) := by
  have hreg : actualRootThetaRegion (l := l) T b (thetaZeroLabel (l := l)) =
      thetaTensorScaledRegion (qVFamTensorPlaces T b) qVFamTensorTuple
        (urThetaFamily (l := l) T b (thetaZeroLabel (l := l))) := rfl
  rw [hreg]
  exact thetaRegion_zero_eq_holomorphic (qVFamTensorPlaces T b) qVFamTensorTuple
    (actualRootCoeff (l := l) T b ())

/-- The holomorphic lattice carrier is closed (it is compact). -/
theorem urHolomorphic_closed :
    IsClosed ((arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b)
      qVFamTensorTuple : Set (qVFamTensorBlock T b))) := by
  rw [coefficient_arithmeticTupleHolomorphicLattice]
  exact (isCompact_arithmeticTupleCanonicalRegions (qVFamTensorPlaces T b)
    qVFamTensorTuple).2.isClosed

/-- The actual theta hull (over all SignedLabel, including 0) is O_hol. -/
theorem urRootThetaHull_eq_holomorphic :
    actualRootThetaHull (l := l) T b =
      (arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :
        Set (qVFamTensorBlock T b)) := by
  change closure (actualRootThetaImageSet (l := l) T b) = _
  have hclosed := urHolomorphic_closed (l := l) T b
  apply le_antisymm
  · exact (hclosed.closure_subset_iff).mpr
      (urRootThetaImageSet_subset_holomorphic (l := l) T b)
  · intro x hx
    apply subset_closure
    have hmem : actualRootThetaImageSet (l := l) T b =
        (⋃ j : SignedLabel l.value,
          thetaTensorScaledRegion (qVFamTensorPlaces T b) qVFamTensorTuple
            (urThetaFamily (l := l) T b j)) := rfl
    rw [hmem]
    refine Set.mem_iUnion.mpr ⟨thetaZeroLabel (l := l), ?_⟩
    rw [show thetaTensorScaledRegion (qVFamTensorPlaces T b) qVFamTensorTuple
        (urThetaFamily (l := l) T b (thetaZeroLabel (l := l))) =
        (arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :
          Set (qVFamTensorBlock T b)) from
      thetaRegion_zero_eq_holomorphic (qVFamTensorPlaces T b) qVFamTensorTuple
        (actualRootCoeff (l := l) T b ())]
    exact hx

/-- Honest semantic observation: the actual (all-label) theta hull is O_hol,
hence its normalized log-volume is zero; stated as the set identity so that the
numeric log-volume corollary can be derived in a file with the paper-level
heartbeat budget (PaperLevelXiFTargetActual sets 1000000 already). -/
theorem urActualLocalHullRegion_eq_holomorphic :
    actualLocalHullRegion (l := l) T b =
      (arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :
        Set (qVFamTensorBlock T b)) :=
  urRootThetaHull_eq_holomorphic (l := l) T b


/-! ## Label-1 ball: the nonzero-label hull is the closure of the label-1 region -/

/-- Monotonicity of the scaled theta region in the exponent vector. -/
theorem urThetaRegion_mono_local {a c : qVFamTensorV → ℝ} (h : ∀ i, a i ≤ c i) :
    thetaTensorScaledRegion (qVFamTensorPlaces T b) qVFamTensorTuple c ⊆
      thetaTensorScaledRegion (qVFamTensorPlaces T b) qVFamTensorTuple a := by
  intro x hx
  unfold thetaTensorScaledRegion at hx ⊢
  have hF : arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
      qVFamTensorTuple c ≤ arithmeticTupleFractionalLattice
      (qVFamTensorPlaces T b) qVFamTensorTuple a :=
    arithmeticTupleFractionalLattice_mono (places := qVFamTensorPlaces T b)
      (tuple := qVFamTensorTuple) h
  exact (Submodule.mul_le.mpr fun u hu v hv => Submodule.mul_mem_mul (hF hu) hv) hx

/-- The nonzero-label image set is the single label-1 theta region. -/
theorem urNonzeroLabelImageSet_eq_region_one :
    urNonzeroLabelImageSet (l := l) T b =
      actualRootThetaRegion (l := l) T b (oneLabel l) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
    have hsub := (urThetaRegion_mono_local (l := l) T b
      (a := fun _ => actualRootCoeff (l := l) T b ())
      (c := fun _ => ((gaussExponent j.1.1).toNat : ℝ) * actualRootCoeff (l := l) T b ())
      (fun i => by
        have hj1 : (1 : ℝ) ≤ ((gaussExponent j.1.1).toNat : ℝ) := by
          exact_mod_cast one_le_gaussExponent_of_ne_zero (l := l) (j := j.1) j.2
        have hc : 0 ≤ actualRootCoeff (l := l) T b () := urRootCoeff_nonneg (l := l) T b
        calc actualRootCoeff (l := l) T b ()
            = 1 * actualRootCoeff (l := l) T b () := (one_mul _).symm
          _ ≤ ((gaussExponent j.1.1).toNat : ℝ) * actualRootCoeff (l := l) T b () :=
              mul_le_mul_of_nonneg_right hj1 hc)) hj
    simpa [actualRootThetaRegion, gaussExponent_oneLabel] using hsub
  · intro x hx
    refine Set.mem_iUnion.mpr
      ⟨⟨oneLabel l, paperOneLabel_ne_zero (l := l)⟩, ?_⟩
    simpa [urNonzeroLabelRegion, urThetaFamily, thetaCoefficientFamily,
      gaussExponent_oneLabel] using hx

/-- The nonzero-label hull is the closure of the label-1 region. -/
theorem urNonzeroLabelHull_eq_closure_region_one :
    urNonzeroLabelHull (l := l) T b =
      closure (actualRootThetaRegion (l := l) T b (oneLabel l)) := by
  unfold urNonzeroLabelHull
  rw [urNonzeroLabelImageSet_eq_region_one (l := l) T b]


/-! ## C4 wiring: paper object name and the nz htheta upper bound -/

/-- The actual bad-place weight is nonnegative. -/
theorem urNativeBadLocalWeight_nonneg (b' : Bad (nativePlaceSelection T)) :
    0 ≤ nativeBadLocalWeight T b' := by
  rw [nativeBadLocalWeight_eq_inv (T := T) (b := b')]
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

/-- Paper-faithful theta hull log root (the nonzero-label object). -/
noncomputable abbrev paperThetaHullLogRoot : ℝ :=
  urNonzeroThetaHullLogRoot (l := l) T

/-- Alternative name of the paper-faithful theta hull log root. -/
noncomputable abbrev paperRootThetaHullLogRoot : ℝ :=
  urNonzeroThetaHullLogRoot (l := l) T

/-- **nz htheta (upper form)**: the nonzero-label theta hull log root is bounded
by the bad-weighted packet sum, from the per-bad-place pointwise bound. -/
theorem paperThetaHullLogRoot_le_ucWeightedHpkt
    (packetV : Bad (nativePlaceSelection T) → ℝ)
    (hperB : ∀ b' : Bad (nativePlaceSelection T),
      urNonzeroLabelHullLog (l := l) T b' ≤ packetV b') :
    paperThetaHullLogRoot (l := l) T ≤
      ucWeightedHpkt (nativeBadLocalWeight T) packetV := by
  unfold paperThetaHullLogRoot urNonzeroThetaHullLogRoot ucWeightedHpkt
  exact Finset.sum_le_sum
    (fun b' _ => mul_le_mul_of_nonneg_left (hperB b')
      (urNativeBadLocalWeight_nonneg (l := l) T b'))


/-- Weight-parameterized paper theta hull log root. -/
noncomputable def paperThetaHullLogRootWith
    (w : Bad (nativePlaceSelection T) → ℝ) : ℝ :=
  ∑ b' : Bad (nativePlaceSelection T),
    w b' * urNonzeroLabelHullLog (l := l) T b'

/-- Weight-parameterized nz htheta upper bound (any nonnegative weight family). -/
theorem paperThetaHullLogRootWith_le_ucWeightedHpkt
    (w : Bad (nativePlaceSelection T) → ℝ) (hw : ∀ b', 0 ≤ w b')
    (packetV : Bad (nativePlaceSelection T) → ℝ)
    (hperB : ∀ b' : Bad (nativePlaceSelection T),
      urNonzeroLabelHullLog (l := l) T b' ≤ packetV b') :
    paperThetaHullLogRootWith (l := l) T w ≤ ucWeightedHpkt w packetV := by
  unfold paperThetaHullLogRootWith ucWeightedHpkt
  exact Finset.sum_le_sum
    (fun b' _ => mul_le_mul_of_nonneg_left (hperB b') (hw b'))

#print axioms paperThetaHullLogRootWith_le_ucWeightedHpkt

#print axioms urNativeBadLocalWeight_nonneg
#print axioms paperThetaHullLogRoot_le_ucWeightedHpkt

#print axioms urThetaRegion_mono_local
#print axioms urNonzeroLabelImageSet_eq_region_one
#print axioms urNonzeroLabelHull_eq_closure_region_one

#print axioms urRootThetaImageSet_subset_holomorphic
#print axioms urRootThetaRegion_zero
#print axioms urHolomorphic_closed
#print axioms urRootThetaHull_eq_holomorphic
#print axioms urActualLocalHullRegion_eq_holomorphic

end LeanFormal.IUT.XiFPaper.Mzk1URThetaHullNonzeroActual
end