/- U-R actual packet instance (kurt, route section 9.3 first package).

For the actual source T this file selects the packet data (prime p, tuple, distinguished
slot), names the actual q-root lattice, theta source span, reference lattice and the
source-arrow action family, and proves the q-reading formula.  These are actual objects
built from the source data (chosen via the nonemptiness of the bad-prime set), NOT new
conditions.

The per-b containment ksThetaHull b <= packet hull is assembled in the next batch on top
of the DONE containments (pureGenerator translate subset possibleImages subset packetHull).

THIS FILE ONLY uses maxHeartbeats 1000000 (paper-level budget); RC registry.
-/
import tmp.sheaf.xif.paper.Mzk1URThetaKPacketActual
import tmp.sheaf.xif.paper.Mzk1URThetaKJ1SupportActual
import tmp.sheaf.xif.paper.Mzk1URThetaKLowerCoreActual
import tmp.sheaf.xif.paper.Mzk1URThetaKLowerBoundActual
import tmp.sheaf.xif.paper.ThetaTensorScaledImageActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.Mzk1URPacketActualInstanceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerCoreActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKPacketActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PhiActionFamilyActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKJ1SupportActual
open MeasureTheory

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (ArithmeticTensorTupleBlock (ksPlaces T b) ksTuple)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (ArithmeticTensorTupleBlock (ksPlaces T b) ksTuple)]
variable [DecidableEq qVFamTensorV]

/-- The selected bad place of the actual packet, from the source selection's
nonemptiness (source data, not a new condition). -/
noncomputable def urActualB : Bad (nativePlaceSelection T) :=
  ⟨Classical.choose (nativePlaceSelection T).V_mod_bad_nonempty,
    Classical.choose_spec (nativePlaceSelection T).V_mod_bad_nonempty⟩

/-- The actual packet prime p. -/
noncomputable def urPacketP : ℕ := qVFamTensorP T (urActualB T)

/-- The actual packet distinguished slot (the unique tensor factor). -/
def urPacketSlot : qVFamTensorV := ()

/-- The actual packet tuple (the unique tensor factor). -/
def urPacketTuple : qVFamTensorV → Unit := fun _ => ()

/-- The actual q normal form used for the q-reading. -/
noncomputable def urPacketQ :
    CommonPrimeCompletion (qVFamTensorPlaces T (urActualB T) () ()) :=
  qVFamNormalizedGenerator T (urActualB T)

/-- The actual q-reading formula: the local order of the q normal form equals the
normalized coefficient (the actual normalization identity). -/
theorem qReading_formula_actual :
    LocalFieldLogarithm.localNormOrder (p := qVFamTensorP T (urActualB T)) (urPacketQ T) =
      qVFamNormalizedCoefficient T (urActualB T) := by
  unfold urPacketQ LocalFieldLogarithm.localNormOrder
    QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient Real.logb
  ring

/-- The actual q-root principal lattice (q * O at the actual packet). -/
noncomputable def qRootLattice_actual :
    Submodule ℤ_[(completionRationalPrime (nativeBadToKPlace T (urActualB T))).val]
      (ksBlock T (urActualB T)) :=
  arithmeticTupleFractionalLattice (ksPlaces T (urActualB T)) ksTuple
      (fun _ => qVFamNormalizedCoefficient T (urActualB T)) *
    arithmeticTupleHolomorphicLattice (ksPlaces T (urActualB T)) ksTuple

/-- The actual theta source span (the nonzero-label K-side region image set). -/
noncomputable def thetaSourceSpan_actual : Set (ksBlock T (urActualB T)) :=
  ksThetaImageSet (l := l) T (urActualB T)

/-- The actual reference lattice (the holomorphic unit reference). -/
noncomputable def referenceLattice_actual :
    Submodule ℤ_[(completionRationalPrime (nativeBadToKPlace T (urActualB T))).val]
      (ksBlock T (urActualB T)) :=
  arithmeticTupleHolomorphicLattice (ksPlaces T (urActualB T)) ksTuple

/-- The actual source-arrow action family (p6Phi preserving the unit log lattice). -/
noncomputable def urPhi_actual :
    Set (ksBlock T (urActualB T) ≃ₗ[ℚ_[(completionRationalPrime (nativeBadToKPlace T (urActualB T))).val]]
      ksBlock T (urActualB T)) :=
  ksThetaPhi (l := l) T (urActualB T)

/-- The identity action belongs to the actual source-arrow family. -/
theorem urPhi_actual_id_mem :
    (LinearEquiv.refl ℚ_[(completionRationalPrime (nativeBadToKPlace T (urActualB T))).val]
      (ksBlock T (urActualB T))) ∈ urPhi_actual (l := l) T :=
  ksThetaPhi_id_mem (l := l) T (urActualB T)


/-! ## Actual theta region containment in the actual packet hull (route section 9.3) -/


/-- The product holomorphic hull is closed (intersection of closed coordinate regions). -/
theorem isClosed_productHull {J : Type} [Finite J] {E : J → Type}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[(completionRationalPrime (nativeBadToKPlace T (urActualB T))).val] (E j)]
    [∀ j, FiniteDimensional ℚ_[(completionRationalPrime (nativeBadToKPlace T (urActualB T))).val] (E j)]
    [∀ j, ProperSpace (E j)]
    (S : Set ((j : J) → E j)) : IsClosed (LocalFieldProductHull.hull S) := by
  have h : LocalFieldProductHull.hull S =
      ⋂ (lam : (j : J) → E j), ⋂ (_ : ∀ j, lam j ≠ 0),
        ⋂ (_ : S ⊆ LocalFieldProductHull.region lam), LocalFieldProductHull.region lam := by
    ext x
    simp [LeanFormal.IUT.LocalFieldProductHull.hull]
  rw [h]
  refine isClosed_iInter (fun lam => isClosed_iInter (fun _ => isClosed_iInter (fun _ => ?_)))
  have hreg : LocalFieldProductHull.region lam =
      ⋂ j : J, {x : (j : J) → E j | ‖x j‖ ≤ ‖lam j‖} := by
    ext x
    simp [LeanFormal.IUT.LocalFieldProductHull.region]
  rw [hreg]
  exact isClosed_iInter (fun j => isClosed_le (continuous_apply j).norm continuous_const)

/-- The actual packet hull is closed. -/
theorem isClosed_packetHull_actual (b : Bad (nativePlaceSelection T))
    {J : Type} [Finite J] {E : J → Type}
    [∀ j, NormedField (E j)]
    [∀ j, NormedAlgebra ℚ_[(completionRationalPrime (nativeBadToKPlace T (b))).val] (E j)]
    [∀ j, FiniteDimensional ℚ_[(completionRationalPrime (nativeBadToKPlace T (b))).val] (E j)]
    [∀ j, ProperSpace (E j)]
    (e : ksBlock T (b) ≃ₐ[ℚ_[(completionRationalPrime (nativeBadToKPlace T (b))).val]]
      ((j : J) → E j))
    (varpi : CommonPrimeCompletion (ksPlace T (b))) :
    IsClosed (ksThetaPacketHull (l := l) T (b) e varpi) := by
  have he : Continuous e.symm := e.symm.toLinearMap.continuous_of_finiteDimensional
  have hclosed := isClosed_productHull
    (e '' arithmeticTupleStepVPossibleImages (ksPlaces T (b)) ksTuple () varpi
      (ksThetaPhi (l := l) T (b)))
  -- image under e.symm equals preimage under e
  have himg : ksThetaPacketHull (l := l) T (b) e varpi =
      e ⁻¹' LocalFieldProductHull.hull
        (e '' arithmeticTupleStepVPossibleImages (ksPlaces T (b)) ksTuple () varpi
          (ksThetaPhi (l := l) T (b))) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e (e.symm x), by simpa using hx, by simp⟩
    · intro hy
      exact ⟨e y, hy.2, by simp⟩
  rw [himg]
  exact hclosed.preimage e.continuous


/-- Unit-index function identity for the pure generator of the ceiling datum. -/
theorem update_single_eq_localGenerator (b : Bad (nativePlaceSelection T)) :
    Function.update (1 : (i : qVFamTensorV) → CommonPrimeCompletion ((ksPlaces T (b)) i (ksTuple i))) ()
        ((Mzk1URThetaKLowerCoreActual.urCeilData T (b)).localGenerator ()) =
      (Mzk1URThetaKLowerCoreActual.urCeilData T (b)).localGenerator := by
  funext i
  rw [show i = () from Subsingleton.elim i ()]
  simp

set_option maxHeartbeats 4000000 in
/-- The actual nonzero-label theta image set lies in the actual possible images. -/
theorem thetaImageSet_subset_possibleImages_actual (b : Bad (nativePlaceSelection T)) :
    ksThetaImageSet (l := l) T (b) ⊆
      ksThetaPossibleImages (l := l) T (b) ((Mzk1URThetaKLowerCoreActual.urCeilData T (b)).localGenerator ()) := by
  have h1 : ksThetaImageSet (l := l) T (b) ⊆
      (thetaTensorScaledRegion (places := ksPlaces T (b)) (tuple := ksTuple)
        (fun _ => urCeilC (l := l) T (b)) : Set (ksBlock T (b))) :=
    ksThetaImageSet_subset_ceilRegion (l := l) T (b)
  have h2 : (thetaTensorScaledRegion (places := ksPlaces T (b)) (tuple := ksTuple)
        (fun _ => urCeilC (l := l) T (b)) : Set (ksBlock T (b))) =
      arithmeticTupleFractionalPureGenerator (ksPlaces T (b)) ksTuple
        (Mzk1URThetaKLowerCoreActual.urCeilData T (b)).localGenerator •
        arithmeticTupleCanonicalUnitReference (ksPlaces T (b)) ksTuple :=
    urCeilRegion_eq_smul (l := l) T (b)
  have h3 : (arithmeticTupleTprod (ksPlaces T (b)) ksTuple
        (Function.update (1 : (i : qVFamTensorV) →
          CommonPrimeCompletion ((ksPlaces T (b)) i (ksTuple i))) ()
          ((Mzk1URThetaKLowerCoreActual.urCeilData T (b)).localGenerator ()))) •
        arithmeticTupleCanonicalUnitReference (ksPlaces T (b)) ksTuple ⊆
      ksThetaPossibleImages (l := l) T (b) ((Mzk1URThetaKLowerCoreActual.urCeilData T (b)).localGenerator ()) :=
    pureGenerator_smul_subset_possibleImages (l := l) T (b)
      ((Mzk1URThetaKLowerCoreActual.urCeilData T (b)).localGenerator ())
  rw [update_single_eq_localGenerator (l := l) T (b)] at h3
  rw [show arithmeticTupleTprod (ksPlaces T (b)) ksTuple
        (Mzk1URThetaKLowerCoreActual.urCeilData T (b)).localGenerator =
      arithmeticTupleFractionalPureGenerator (ksPlaces T (b)) ksTuple
        (Mzk1URThetaKLowerCoreActual.urCeilData T (b)).localGenerator from rfl] at h3
  exact h1.trans (h2.trans_subset h3)

set_option maxHeartbeats 4000000 in
/-- The actual theta hull lies in the actual packet hull (nonzero-label hull). -/
theorem ksThetaHull_subset_packetHull_actual (b : Bad (nativePlaceSelection T))
    [MeasurableSpace (ksBlock T (b))] [BorelSpace (ksBlock T (b))]
    {J : Type} [Finite J] {E : J → Type}
    [∀ j, NormedField (E j)]
    [∀ j, NormedAlgebra ℚ_[(completionRationalPrime (nativeBadToKPlace T (b))).val] (E j)]
    [∀ j, FiniteDimensional ℚ_[(completionRationalPrime (nativeBadToKPlace T (b))).val] (E j)]
    [∀ j, ProperSpace (E j)]
    (e : ksBlock T (b) ≃ₐ[ℚ_[(completionRationalPrime (nativeBadToKPlace T (b))).val]]
      ((j : J) → E j)) :
    ksThetaHull (l := l) T (b) ⊆
      ksThetaPacketHull (l := l) T (b) e ((Mzk1URThetaKLowerCoreActual.urCeilData T (b)).localGenerator ()) := by
  unfold ksThetaHull
  refine closure_minimal ?_ (isClosed_packetHull_actual (l := l) T (b) e
    ((Mzk1URThetaKLowerCoreActual.urCeilData T (b)).localGenerator ()))
  exact (thetaImageSet_subset_possibleImages_actual (l := l) T (b)).trans
    (ksThetaPossibleImages_subset_packetHull (l := l) T (b) e
      ((Mzk1URThetaKLowerCoreActual.urCeilData T (b)).localGenerator ()))


/-- The ceiling datum's local generator is nonzero (reuse of the accepted data lemma). -/
theorem urCeilLocalGenerator_ne_zero (b : Bad (nativePlaceSelection T)) :
    (Mzk1URThetaKLowerCoreActual.urCeilData T b).localGenerator () ≠ 0 :=
  arithmeticTuplePureFractionalScalingData_localGenerator_ne_zero
    (data := Mzk1URThetaKLowerCoreActual.urCeilData T b) (i := ())

set_option maxHeartbeats 4000000 in
/-- Steps (v) upper bound: theta hull log volume is at most the actual packet value
urPacketV_K (L814 paper bound applied to the theta hull inside the endpoint container). -/
theorem ksThetaHullLog_le_urPacketV_K (b : Bad (nativePlaceSelection T))
    [DecidableEq qVFamTensorV]
    [MeasurableSpace (ksBlock T b)] [BorelSpace (ksBlock T b)]
    {J : Type} [Finite J] {E : J → Type}
    [∀ j, NormedField (E j)]
    [∀ j, NormedAlgebra ℚ_[(completionRationalPrime (nativeBadToKPlace T b)).val] (E j)]
    [∀ j, FiniteDimensional ℚ_[(completionRationalPrime (nativeBadToKPlace T b)).val] (E j)]
    [∀ j, ProperSpace (E j)]
    (e : ksBlock T b ≃ₐ[ℚ_[(completionRationalPrime (nativeBadToKPlace T b)).val]]
      ((j : J) → E j)) :
    ksThetaHullLog (l := l) T b ≤ urPacketV_K (l := l) T b := by
  set lam : ℝ := LocalFieldLogarithm.localNormOrder
    (p := (completionRationalPrime (nativeBadToKPlace T b)).val)
    ((Mzk1URThetaKLowerCoreActual.urCeilData T b).localGenerator ()) with hlam
  set d : qVFamTensorV → ℝ := fun i => LocalFieldLogarithm.localNormOrder
    (p := (completionRationalPrime (nativeBadToKPlace T b)).val)
    (arithmeticTupleLocalDifferent (ksPlaces T b) ksTuple i) with hd
  set m : ℤ := ⌊lam - ∑ i : qVFamTensorV, d i -
    ∑ i : qVFamTensorV, arithmeticTupleStepVA (ksPlaces T b) ksTuple i⌋ with hmdef
  have hm : (m : ℝ) ≤ lam - ∑ i : qVFamTensorV,
      (d i + arithmeticTupleStepVA (ksPlaces T b) ksTuple i) := by
    rw [hmdef]
    rw [Finset.sum_add_distrib, ← sub_sub]
    exact Int.floor_le _
  have hlamC : lam = ksCeilC (l := l) T b := by
    rw [hlam]
    letI : Fact (Nat.Prime ((completionRationalPrime (nativeBadToKPlace T b)).val)) :=
      completionRationalPrime_fact (nativeBadToKPlace T b)
    change LocalFieldLogarithm.localNormOrder
      (p := (completionRationalPrime (nativeBadToKPlace T b)).val)
      (urCeilGenerator (l := l) T b) = ksCeilC (l := l) T b
    rw [localNormOrder_eq_of_norm_eq_rpow (urCeilGenerator_norm (l := l) T b)]
    rfl
  have hdK : d = fun _ => ksDifferentOrder (l := l) T b := by
    funext i
    cases i
    rw [hd]
    rfl
  have hPhi : ∀ φ ∈ ksThetaPhi (l := l) T b,
      ∀ u ∈ arithmeticTupleUnitLogLattice (ksPlaces T b) ksTuple,
        φ u ∈ arithmeticTupleUnitLogLattice (ksPlaces T b) ksTuple :=
    fun φ hφ => hφ
  have hpossub := arithmeticTupleStepVPossibleImages_subset_endpoint (ksPlaces T b) ksTuple ()
    ((Mzk1URThetaKLowerCoreActual.urCeilData T b).localGenerator ())
    (urCeilLocalGenerator_ne_zero (l := l) T b)
    (ksThetaPhi (l := l) T b) hPhi m hm
  have hunit := isUnit_arithmeticTupleTprod (ksPlaces T b) ksTuple _
    (arithmeticTupleStepVEndpointGenerator_ne_zero (ksPlaces T b) ksTuple () m)
  have hpack : ksThetaPacketHull (l := l) T b e
      ((Mzk1URThetaKLowerCoreActual.urCeilData T b).localGenerator ()) ⊆
      arithmeticTupleTprod (ksPlaces T b) ksTuple
        (arithmeticTupleStepVEndpointGenerator (ksPlaces T b) ksTuple () m) •
        arithmeticTupleCanonicalUnitReference (ksPlaces T b) ksTuple :=
    arithmeticTupleHolomorphicHull_subset_smul (ksPlaces T b) ksTuple e hunit hpossub
  have hS : ksThetaHull (l := l) T b ⊆
      arithmeticTupleTprod (ksPlaces T b) ksTuple
        (arithmeticTupleStepVEndpointGenerator (ksPlaces T b) ksTuple () m) •
        arithmeticTupleCanonicalUnitReference (ksPlaces T b) ksTuple :=
    (ksThetaHull_subset_packetHull_actual (l := l) T b e).trans hpack
  have hSpos : 0 < MeasureTheory.Measure.addHaar (ksThetaHull (l := l) T b) :=
    lt_of_lt_of_le (ksLabelOneRegion_measure_pos (l := l) T b)
      (measure_mono (ksOneLabelRegion_subset_hull (l := l) T b))
  have hbound := arithmeticTupleNormalizedLogVolume_le_stepVPaperBound
    (ksPlaces T b) ksTuple MeasureTheory.Measure.addHaar () d lam
    (ksExceptional (l := l) T b) ?small_outside hSpos hS
  · unfold ksThetaHullLog
    refine hbound.trans_eq ?_
    unfold urPacketV_K ksExceptionalSum ksLogP
    simp only [hlamC, hdK, Finset.sum_const, Finset.card_univ, Fintype.card_unit,
      nsmul_eq_mul, mul_one]
    ring
  · intro i hi
    have he : ¬ ((completionRationalPrime (nativeBadToKPlace T b)).val - 2 <
        logShellRamificationExponent
          (K := CommonPrimeCompletion ((ksPlaces T b) i (ksTuple i)))
          (p := (completionRationalPrime (nativeBadToKPlace T b)).val)) := by
      intro hlt
      exact hi (by
        unfold ksExceptional
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        simpa using hlt)
    exact Nat.le_of_not_lt he

end LeanFormal.IUT.XiFPaper.Mzk1URPacketActualInstanceActual
end