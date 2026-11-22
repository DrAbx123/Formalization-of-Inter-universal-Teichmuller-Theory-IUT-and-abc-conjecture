import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.RootTensorHaarTransportActual
import tmp.sheaf.xif.paper.PaperC3ThetaRootActual
import tmp.sheaf.xif.paper.SignedLabelOneActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique

noncomputable section
open scoped BigOperators Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.RootTensorThetaHullActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.XiFPaper.RootTensorHaarTransportActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable (mu : rootsOfUnity (2 * l.value) (rootNormedExtension T b))

/-- The mu root as an element of L. -/
noncomputable abbrev muL : rootNormedExtension T b :=
  ((mu : (rootNormedExtension T b)ˣ) : rootNormedExtension T b)

/-- The actual mu^m times theta value in L. -/
noncomputable def muThetaValue (x : ThetaLabel (l := l) × Fin (2 * l.value)) :
    rootNormedExtension T b :=
  (muL (T := T) (b := b) mu) ^ (x.2 : Nat) *
    rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) x.1)

/-- Actual Theta possible image point on the L root tensor carrier. -/
noncomputable def thetaPossibleImagePoint
    (mu : rootsOfUnity (2 * l.value) (rootNormedExtension T b))
    (x : ThetaLabel (l := l) × Fin (2 * l.value)) : rootTensorBlock T b :=
  finitePadicTensorTprod (p := qVFamTensorP T b)
    (fun _ : Unit => rootNormedExtension T b)
    (fun _ => muThetaValue (T := T) (b := b) mu x)

/-- Actual finite Theta possible image union on the L root tensor carrier. -/
noncomputable def thetaPossibleImageUnion
    (mu : rootsOfUnity (2 * l.value) (rootNormedExtension T b)) :
    Set (rootTensorBlock T b) :=
  Set.range (thetaPossibleImagePoint (T := T) (b := b) mu)

/-- Actual field-unit lambda scaling of the Theta possible image on the L tensor carrier. -/
noncomputable def thetaFieldUnitLambdaOHull
    (mu : rootsOfUnity (2 * l.value) (rootNormedExtension T b))
    (lam : rootNormedExtension T b) : Set (rootTensorBlock T b) :=
  Set.range (fun x : ThetaLabel (l := l) × Fin (2 * l.value) =>
    finitePadicTensorTprod (p := qVFamTensorP T b)
      (fun _ : Unit => rootNormedExtension T b)
      (fun _ => (lam : rootNormedExtension T b) *
        muThetaValue (T := T) (b := b) mu x))

theorem thetaPossibleImagePoint_mem
    (mu : rootsOfUnity (2 * l.value) (rootNormedExtension T b))
    (x : ThetaLabel (l := l) × Fin (2 * l.value)) :
    thetaPossibleImagePoint (T := T) (b := b) mu x ∈
      thetaPossibleImageUnion (T := T) (b := b) mu :=
  ⟨x, rfl⟩


/-- Actual field-unit lambda-O hull: lambda times the actual unit ball of L, transported to the root tensor block. -/
noncomputable def thetaLambdaOUnitBallHull
    (lam : rootNormedExtension T b) : Set (rootTensorBlock T b) :=
  (blockLinearEquiv T b).symm ''
    (lam • (blockLinearEquiv T b) '' blockUnitBall T b)

/-- Genuine block Haar measure of the field-unit lambda-O hull. -/
noncomputable def thetaLambdaOUnitBallHullMeasure
    (lam : rootNormedExtension T b) : ENNReal :=
  blockHaar T b (thetaLambdaOUnitBallHull (T := T) (b := b) lam)

/-- Actual normalized log of the field-unit lambda-O hull. -/
noncomputable def thetaLambdaOUnitBallHullLog
    (lam : rootNormedExtension T b) : Real :=
  Real.log (thetaLambdaOUnitBallHullMeasure (T := T) (b := b) lam).toReal

/-- The block linear equivalence is an isometry for the induced norm. -/
noncomputable def blockLinearIsometryEquiv :
    rootTensorBlock T b ≃ₗᵢ[ℚ_[(qVFamTensorP T b)]]
      (rootNormedExtension T b) where
  toLinearEquiv := blockLinearEquiv T b
  norm_map' := by
    intro x
    rfl

/-- The scalar multiplication homeomorphism by a nonzero field element. -/
noncomputable def lambdaScalingHomeomorph
    (lam : rootNormedExtension T b) (hlam : lam ≠ 0) :
    rootNormedExtension T b ≃ₜ rootNormedExtension T b :=
  Homeomorph.smulOfNeZero lam hlam

/-- The block linear isometry as a homeomorphism. -/
noncomputable def blockLinearHomeomorph :
    rootTensorBlock T b ≃ₜ rootNormedExtension T b :=
  (blockLinearIsometryEquiv T b).toHomeomorph

/-- The lambda-O hull is the homeomorphic image of the L unit ball. -/
theorem thetaLambdaOUnitBallHull_eq_homeomorph_image
    (lam : rootNormedExtension T b) (hlam : lam ≠ 0) :
    thetaLambdaOUnitBallHull (T := T) (b := b) lam =
      (blockLinearHomeomorph T b).symm ''
        ((lambdaScalingHomeomorph (T := T) (b := b) lam hlam) ''
          ((blockLinearHomeomorph T b) '' blockUnitBall T b)) := rfl

/-- The scaled unit ball is compact. -/
theorem thetaLambdaOUnitBallHull_isCompact
    (lam : rootNormedExtension T b) (hlam : lam ≠ 0) :
    IsCompact (thetaLambdaOUnitBallHull (T := T) (b := b) lam) := by
  rw [thetaLambdaOUnitBallHull_eq_homeomorph_image (T := T) (b := b) lam hlam]
  apply IsCompact.image
  · apply IsCompact.image
    · apply IsCompact.image
      · simpa [blockUnitBall] using (blockUnitBallPositive T b).isCompact
      · exact (blockLinearHomeomorph T b).continuous
    · exact (lambdaScalingHomeomorph (T := T) (b := b) lam hlam).continuous
  · exact (blockLinearHomeomorph T b).symm.continuous

/-- Genuine block Haar is finite on the scaled hull. -/
theorem thetaLambdaOUnitBallHullMeasure_lt_top
    (lam : rootNormedExtension T b) (hlam : lam ≠ 0) :
    thetaLambdaOUnitBallHullMeasure (T := T) (b := b) lam < ⊤ := by
  haveI : MeasureTheory.Measure.IsAddHaarMeasure (blockHaar T b) :=
    MeasureTheory.Measure.isAddHaarMeasure_addHaarMeasure (blockUnitBallPositive T b)
  exact IsCompact.measure_lt_top
    (thetaLambdaOUnitBallHull_isCompact (T := T) (b := b) lam hlam)

/-- The scaled hull has positive genuine Haar measure. -/
theorem thetaLambdaOUnitBallHullMeasure_pos
    (lam : rootNormedExtension T b) (hlam : lam ≠ 0) :
    0 < thetaLambdaOUnitBallHullMeasure (T := T) (b := b) lam := by
  haveI : MeasureTheory.Measure.IsAddHaarMeasure (blockHaar T b) :=
    MeasureTheory.Measure.isAddHaarMeasure_addHaarMeasure (blockUnitBallPositive T b)
  let e := blockLinearHomeomorph T b
  let s : Set (rootTensorBlock T b) :=
    e.symm '' ((lambdaScalingHomeomorph (T := T) (b := b) lam hlam) ''
      (e '' Metric.ball (0 : rootTensorBlock T b) 1))
  have hs_open : IsOpen s := by
    apply e.symm.isOpenMap
    apply (lambdaScalingHomeomorph (T := T) (b := b) lam hlam).isOpenMap
    exact e.isOpenMap _ Metric.isOpen_ball
  have hs_ne : s.Nonempty := by
    refine ⟨e.symm ((lambdaScalingHomeomorph (T := T) (b := b) lam hlam) (e 0)), ?_⟩
    refine ⟨(lambdaScalingHomeomorph (T := T) (b := b) lam hlam) (e 0), ?_, rfl⟩
    exact ⟨e 0, ⟨0, Metric.mem_ball_self zero_lt_one, rfl⟩, rfl⟩
  have hball : Metric.ball (0 : rootTensorBlock T b) 1 ⊆ blockUnitBall T b := by
    simpa [blockUnitBall, blockUnitBallPositive] using
      (Metric.ball_subset_closedBall (x := (0 : rootTensorBlock T b))
        (ε := (1 : ℝ)))
  have hsub : s ⊆ thetaLambdaOUnitBallHull (T := T) (b := b) lam := by
    intro x hx
    rw [thetaLambdaOUnitBallHull_eq_homeomorph_image (T := T) (b := b) lam hlam]
    exact Set.image_mono (Set.image_mono (Set.image_mono hball)) hx
  have hposS : 0 < blockHaar T b s :=
    pos_iff_ne_zero.mpr
      (MeasureTheory.Measure.IsOpenPosMeasure.open_pos s hs_open hs_ne)
  rw [thetaLambdaOUnitBallHullMeasure]
  exact lt_of_lt_of_le hposS (MeasureTheory.measure_mono hsub)


/-- Additive equivalence given by lambda-scaling on the root tensor block. -/
noncomputable def blockScalingAddEquiv
    (lam : rootNormedExtension T b) (hlam : lam ≠ 0) :
    rootTensorBlock T b ≃+ rootTensorBlock T b where
  toFun x := (blockLinearEquiv T b).symm (lam * blockLinearEquiv T b x)
  invFun x := (blockLinearEquiv T b).symm (lam⁻¹ * blockLinearEquiv T b x)
  left_inv := by
    intro x
    simp only [LinearEquiv.apply_symm_apply]
    rw [← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
    exact LinearEquiv.symm_apply_apply _ _
  right_inv := by
    intro x
    simp only [LinearEquiv.apply_symm_apply]
    rw [← mul_assoc, mul_inv_cancel₀ hlam, one_mul]
    exact LinearEquiv.symm_apply_apply _ _
  map_add' := by
    intro x y
    simp only [map_add, mul_add]

/-- The same scaling as a continuous additive equivalence. -/
noncomputable def blockScalingContinuousAddEquiv
    (lam : rootNormedExtension T b) (hlam : lam ≠ 0) :
    rootTensorBlock T b ≃ₜ+ rootTensorBlock T b where
  toAddEquiv := blockScalingAddEquiv (T := T) (b := b) lam hlam
  continuous_toFun := by
    have h : Continuous ((blockLinearHomeomorph T b).symm ∘
        (lambdaScalingHomeomorph (T := T) (b := b) lam hlam) ∘
          (blockLinearHomeomorph T b)) :=
      (blockLinearHomeomorph T b).symm.continuous.comp
        ((lambdaScalingHomeomorph (T := T) (b := b) lam hlam).continuous.comp
          (blockLinearHomeomorph T b).continuous)
    convert h using 1
    · ext x
      rfl
  continuous_invFun := by
    have h : Continuous ((blockLinearHomeomorph T b).symm ∘
        (lambdaScalingHomeomorph (T := T) (b := b) lam⁻¹ (inv_ne_zero hlam)) ∘
          (blockLinearHomeomorph T b)) :=
      (blockLinearHomeomorph T b).symm.continuous.comp
        ((lambdaScalingHomeomorph (T := T) (b := b) lam⁻¹ (inv_ne_zero hlam)).continuous.comp
          (blockLinearHomeomorph T b).continuous)
    convert h using 1
    · ext x
      rfl


/-- The block Haar measure instance. -/
noncomputable instance blockHaarIsAddHaar : MeasureTheory.Measure.IsAddHaarMeasure (blockHaar T b) :=
  MeasureTheory.Measure.isAddHaarMeasure_addHaarMeasure (blockUnitBallPositive T b)

/-- Actual Haar scaling factor for the block scaling. -/
noncomputable def thetaScalingHaarFactor
    (lam : rootNormedExtension T b) (hlam : lam ≠ 0) : NNReal :=
  MeasureTheory.Measure.addHaarScalarFactor
    ((blockHaar T b).map
      (blockScalingContinuousAddEquiv (T := T) (b := b) lam⁻¹ (inv_ne_zero hlam)))
    (blockHaar T b)



/-- Inverse of the lambda-scaling is the inverse-lambda scaling. -/
theorem blockScalingContinuousAddEquiv_symm_eq
    (lam : rootNormedExtension T b) (hlam : lam ≠ 0) :
    (blockScalingContinuousAddEquiv (T := T) (b := b) lam hlam).symm =
      blockScalingContinuousAddEquiv (T := T) (b := b) lam⁻¹ (inv_ne_zero hlam) := by
  ext x
  rfl

/-- Preimage of the inverse-lambda scaling is the lambda image. -/
theorem blockScaling_preimage_eq_image
    (lam : rootNormedExtension T b) (hlam : lam ≠ 0)
    (S : Set (rootTensorBlock T b)) :
    (blockScalingContinuousAddEquiv (T := T) (b := b) lam⁻¹ (inv_ne_zero hlam)) ⁻¹' S =
      (blockScalingContinuousAddEquiv (T := T) (b := b) lam hlam) '' S := by
  let Tlam := blockScalingContinuousAddEquiv (T := T) (b := b) lam hlam
  let Tinv := blockScalingContinuousAddEquiv (T := T) (b := b) lam⁻¹ (inv_ne_zero hlam)
  have hsym : Tlam.symm = Tinv :=
    blockScalingContinuousAddEquiv_symm_eq (T := T) (b := b) lam hlam
  ext x
  constructor
  · intro hx
    refine ⟨Tlam.symm x, ?_, Tlam.apply_symm_apply x⟩
    rw [hsym]
    exact hx
  · rintro ⟨y, hy, rfl⟩
    change Tinv (Tlam y) ∈ S
    have h : Tinv (Tlam y) = y := by
      rw [← hsym]
      exact Tlam.symm_apply_apply y
    simpa [h] using hy

/-- Actual Haar scaling formula for sets with compact closure. -/
theorem thetaScalingHaarFactor_spec
    (lam : rootNormedExtension T b) (hlam : lam ≠ 0)
    {S : Set (rootTensorBlock T b)}
    (hS : MeasurableSet S) (hScomp : IsCompact (closure S)) :
    blockHaar T b
        ((blockScalingContinuousAddEquiv (T := T) (b := b) lam hlam) '' S) =
      (thetaScalingHaarFactor (T := T) (b := b) lam hlam : ENNReal) *
        blockHaar T b S := by
  let Tlam := blockScalingContinuousAddEquiv (T := T) (b := b) lam hlam
  let Tinv := blockScalingContinuousAddEquiv (T := T) (b := b) lam⁻¹ (inv_ne_zero hlam)
  let μ' : MeasureTheory.Measure (rootTensorBlock T b) :=
    (blockHaar T b).map Tinv
  have h := MeasureTheory.Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure
    (μ' := μ') (μ := blockHaar T b) (s := S) hScomp
  have hmap : μ' S = blockHaar T b (Tlam '' S) := by
    unfold μ'
    rw [MeasureTheory.Measure.map_apply]
    · rw [blockScaling_preimage_eq_image (T := T) (b := b) lam hlam S]
    · exact Tinv.continuous.measurable
    · exact hS
  rw [hmap] at h
  simpa [thetaScalingHaarFactor, NNReal.smul_def] using h



/-- Scaling by one is the identity continuous additive equivalence. -/
theorem blockScalingContinuousAddEquiv_one :
    blockScalingContinuousAddEquiv (T := T) (b := b)
      (1 : rootNormedExtension T b) one_ne_zero =
      ContinuousAddEquiv.refl (rootTensorBlock T b) := by
  ext x
  simp [blockScalingContinuousAddEquiv, blockScalingAddEquiv]

/-- The scaling factor at one is one. -/
theorem thetaScalingHaarFactor_one :
    thetaScalingHaarFactor (T := T) (b := b) (1 : rootNormedExtension T b)
      one_ne_zero = 1 := by
  unfold thetaScalingHaarFactor
  simp [blockScalingContinuousAddEquiv_one]



end LeanFormal.IUT.XiFPaper.RootTensorThetaHullActual
end
