import tmp.sheaf.xif.paper.PaperRootBaseLZetaActual
import tmp.sheaf.xif.paper.PaperRootLValuedTensorCarrierActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.Basis.VectorSpace

-- S251: unified carrier qVFamTensorBlock ⊗ RootBaseLZeta, with actual
-- RootL -> RootBaseLZeta compatibility, root theta image and mu_2l action.
-- Haar on the full tensor is an exact object/gap if normed-tensor API is absent.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.PaperUnifiedLZetaCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperRootBaseLZetaActual
open LeanFormal.IUT.XiFPaper.PaperRootLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory
open scoped TensorProduct

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

theorem rootL_le_rootBaseLZeta :
    rootNormedExtension T b ≤ RootBaseLZetaField T b := by
  rw [rootNormedExtension, RootBaseLZetaField, IntermediateField.adjoin_le_iff]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  exact IntermediateField.subset_adjoin _ _ (by
    simp [rootBaseZetaGenerators])

noncomputable def rootLtoLZeta : RootL T b →ₐ[rootBase T b] RootBaseLZeta T b :=
  IntermediateField.inclusion (rootL_le_rootBaseLZeta (l := l) T b)

abbrev UnifiedCarrier : Type :=
  TensorProduct ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b) (RootBaseLZeta T b)

noncomputable instance rootBaseLZetaFiniteDimensionalQp :
    FiniteDimensional ℚ_[qVFamTensorP T b] (RootBaseLZeta T b) := by
  haveI : FiniteDimensional (rootBase T b) (RootBaseLZeta T b) :=
    rootBaseLZetaFiniteDimensional (T := T) (b := b)
  exact FiniteDimensional.trans ℚ_[qVFamTensorP T b] (rootBase T b) (RootBaseLZeta T b)

noncomputable instance unifiedFiniteDimensional :
    FiniteDimensional ℚ_[qVFamTensorP T b] (UnifiedCarrier T b) :=
  Module.Finite.tensorProduct (R := ℚ_[qVFamTensorP T b])
    (M := qVFamTensorBlock T b) (N := RootBaseLZeta T b)

noncomputable def qVFamToUnified : qVFamTensorBlock T b → UnifiedCarrier T b :=
  fun x => TensorProduct.tmul ℚ_[qVFamTensorP T b] x (1 : RootBaseLZeta T b)

noncomputable def rootLtoLZetaQp :
    RootL T b →ₗ[ℚ_[qVFamTensorP T b]] RootBaseLZeta T b :=
  (rootLtoLZeta (l := l) T b).toLinearMap.restrictScalars ℚ_[qVFamTensorP T b]

noncomputable def rootLToUnified : RootLValuedCarrier T b → UnifiedCarrier T b :=
  TensorProduct.map (LinearMap.id) (rootLtoLZetaQp T b)

theorem rootLToUnified_tmul (x : qVFamTensorBlock T b) (y : RootL T b) :
    rootLToUnified T b (TensorProduct.tmul ℚ_[qVFamTensorP T b] x y) =
      TensorProduct.tmul ℚ_[qVFamTensorP T b] x (rootLtoLZeta (l := l) T b y) := by
  rw [rootLToUnified, TensorProduct.map_tmul]
  rfl

-- The two generators in RootBaseLZeta.
noncomputable def rootInLZeta : RootBaseLZeta T b :=
  ⟨rootNormedElement T b, by
    exact IntermediateField.subset_adjoin _ _ (by
      simp [rootBaseZetaGenerators])⟩

noncomputable def zetaInLZeta : (RootBaseLZeta T b)ˣ :=
  Units.mk0 ⟨rootBaseZeta T b, by
    exact IntermediateField.subset_adjoin _ _ (by
      simp [rootBaseZetaGenerators])⟩ (by
    intro h
    have h' := congrArg Subtype.val h
    have hpos : 2 * l.value ≠ 0 := Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
    have hz : rootBaseZeta T b ≠ 0 := by
      simpa [rootBaseZeta] using
        (Classical.choose_spec (HasEnoughRootsOfUnity.exists_primitiveRoot
          (rootNormedAmbient T b) (2 * l.value))).ne_zero hpos
    exact hz h')

noncomputable def rootThetaToUnified (j : SignedLabel l.value) : UnifiedCarrier T b :=
  TensorProduct.tmul ℚ_[qVFamTensorP T b] (1 : qVFamTensorBlock T b)
    (rootInLZeta T b ^ ((gaussExponent j.1).toNat ^ 2))

noncomputable def rootThetaImageUnified : Set (UnifiedCarrier T b) :=
  Set.range (rootThetaToUnified (l := l) T b)

noncomputable def unifiedMu2lAction (m : Nat) :
    UnifiedCarrier T b ≃ₗ[ℚ_[qVFamTensorP T b]] UnifiedCarrier T b :=
  TensorProduct.congr (LinearEquiv.refl _ _)
    { toFun := fun x => (zetaInLZeta (l := l) T b ^ m : RootBaseLZeta T b) * x
      invFun := fun x => ((zetaInLZeta (l := l) T b ^ m)⁻¹ : RootBaseLZeta T b) * x
      map_add' := by intro x y; ring
      map_smul' := by intro a x; simp [mul_smul_comm]
      left_inv := by intro x; simp
      right_inv := by intro x; simp }

structure UnifiedHaarObject where
  measurableSpace : MeasurableSpace (UnifiedCarrier T b)
  haar : @Measure (UnifiedCarrier T b) measurableSpace
  positiveFiniteOnImage : Prop

def UnifiedHaarObjectRequired : Prop := Nonempty (UnifiedHaarObject T b)

#check rootL_le_rootBaseLZeta
#check rootLtoLZeta
#check UnifiedCarrier
#check rootLToUnified
#check rootLToUnified_tmul
#check rootThetaToUnified
#check unifiedMu2lAction
#check UnifiedHaarObject

-- S256 exact missing normed/Haar object on the unified tensor carrier.
structure UnifiedNormedHaarGap where
  normedAddCommGroup : NormedAddCommGroup (UnifiedCarrier T b)
  normedSpace : NormedSpace ℚ_[qVFamTensorP T b] (UnifiedCarrier T b)
  completeSpace : CompleteSpace (UnifiedCarrier T b)
  measurableSpace : MeasurableSpace (UnifiedCarrier T b)
  haar : @Measure (UnifiedCarrier T b) measurableSpace
  positiveOnThetaImage : Prop
  finiteOnThetaImage : Prop

def UnifiedNormedHaarGapRequired : Prop :=
  Nonempty (UnifiedNormedHaarGap T b)

#check UnifiedNormedHaarGap
#check UnifiedNormedHaarGapRequired
noncomputable def unifiedBasis :
    Module.Basis (Fin (Module.finrank ℚ_[qVFamTensorP T b] (UnifiedCarrier T b)))
      ℚ_[qVFamTensorP T b] (UnifiedCarrier T b) :=
  Module.finBasis ℚ_[qVFamTensorP T b] (UnifiedCarrier T b)

noncomputable def unifiedEquivFun :
    UnifiedCarrier T b ≃ₗ[ℚ_[qVFamTensorP T b]]
      (Fin (Module.finrank ℚ_[qVFamTensorP T b] (UnifiedCarrier T b)) →
        ℚ_[qVFamTensorP T b]) :=
  (unifiedBasis T b).equivFun

#check unifiedBasis
#check unifiedEquivFun
noncomputable instance unifiedNormedAddCommGroup :
    NormedAddCommGroup (UnifiedCarrier T b) :=
  NormedAddCommGroup.induced (UnifiedCarrier T b)
    (Fin (Module.finrank ℚ_[qVFamTensorP T b] (UnifiedCarrier T b)) →
      ℚ_[qVFamTensorP T b])
    (unifiedEquivFun T b).toAddEquiv.toAddMonoidHom
    (unifiedEquivFun T b).injective

noncomputable instance unifiedNormedSpace :
    NormedSpace ℚ_[qVFamTensorP T b] (UnifiedCarrier T b) :=
  NormedSpace.induced ℚ_[qVFamTensorP T b] (UnifiedCarrier T b)
    (Fin (Module.finrank ℚ_[qVFamTensorP T b] (UnifiedCarrier T b)) →
      ℚ_[qVFamTensorP T b])
    (unifiedEquivFun T b).toLinearMap

noncomputable instance unifiedCompleteSpace : CompleteSpace (UnifiedCarrier T b) :=
  FiniteDimensional.complete ℚ_[qVFamTensorP T b] (UnifiedCarrier T b)

noncomputable instance unifiedMeasurableSpace : MeasurableSpace (UnifiedCarrier T b) :=
  borel _

noncomputable instance unifiedBorelSpace : BorelSpace (UnifiedCarrier T b) := ⟨rfl⟩

noncomputable instance unifiedProperSpace : ProperSpace (UnifiedCarrier T b) :=
  @FiniteDimensional.proper ℚ_[qVFamTensorP T b] inferInstance (UnifiedCarrier T b)
    inferInstance inferInstance inferInstance (unifiedFiniteDimensional T b)

noncomputable def unifiedUnitBall : Set (UnifiedCarrier T b) :=
  Metric.closedBall (0 : UnifiedCarrier T b) 1

noncomputable def unifiedHaar : Measure (UnifiedCarrier T b) :=
  Measure.addHaar

structure UnifiedHaarPositiveFiniteThetaImage where
  thetaImage_measurable : MeasurableSet (rootThetaImageUnified (l := l) T b)
  thetaImage_measure_pos : 0 < unifiedHaar T b (rootThetaImageUnified (l := l) T b)
  thetaImage_measure_lt_top : unifiedHaar T b (rootThetaImageUnified (l := l) T b) < ⊤

def UnifiedHaarPositiveFiniteThetaImageRequired : Prop :=
  Nonempty (UnifiedHaarPositiveFiniteThetaImage T b)

#check unifiedNormedAddCommGroup
#check unifiedNormedSpace
#check unifiedCompleteSpace
#check unifiedHaar
#check UnifiedHaarPositiveFiniteThetaImage
end LeanFormal.IUT.XiFPaper.PaperUnifiedLZetaCarrierActual

end