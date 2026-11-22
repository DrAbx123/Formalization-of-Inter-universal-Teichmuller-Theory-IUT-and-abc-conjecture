import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import tmp.sheaf.xif.paper.RootThetaValueInLUnitActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Sets.Compacts

/-! # Actual Haar on the tensor block via explicit transport along block ≃ L

We do not rely on the automatic FinitePadicTensor instances.  The one-factor
linear equivalence block ≃ₗ[Qp] L is used to induce the normed additive group,
the Qp normed-space and finite-dimensional structures on block.  Then the
closed unit ball is a PositiveCompacts and Measure.addHaarMeasure is the actual
Haar.  The unit ball has measure 1, positive and finite.

No fake Haar. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.RootTensorHaarTransportActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.RootThetaValueInLUnitActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.N8Closure.C3Roots
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The one-factor linear equivalence block ≃ L. -/
noncomputable def blockLinearEquiv :
    rootTensorBlock T b ≃ₗ[ℚ_[(qVFamTensorP T b)]] (rootNormedExtension T b) :=
  @PiTensorProduct.subsingletonEquiv Unit ℚ_[(qVFamTensorP T b)] _
    (fun _ : Unit => rootNormedExtension T b)
    (fun _ => inferInstance) (fun _ => inferInstance) inferInstance ()

/-- The induced normed additive group on the tensor block. -/
noncomputable instance blockNormedAddCommGroup :
    NormedAddCommGroup (rootTensorBlock T b) :=
  NormedAddCommGroup.induced (rootTensorBlock T b) (rootNormedExtension T b)
    (blockLinearEquiv T b).toLinearMap.toAddMonoidHom (blockLinearEquiv T b).injective

/-- The induced Qp normed-space structure on the tensor block. -/
noncomputable instance blockNormedSpace :
    NormedSpace ℚ_[(qVFamTensorP T b)] (rootTensorBlock T b) := by
  letI : NormedAddCommGroup (rootTensorBlock T b) := blockNormedAddCommGroup T b
  exact NormedSpace.induced ℚ_[(qVFamTensorP T b)] (rootTensorBlock T b)
    (rootNormedExtension T b) (blockLinearEquiv T b).toLinearMap

/-- Finite-dimensional structure on the tensor block. -/
noncomputable instance blockFiniteDimensional :
    FiniteDimensional ℚ_[(qVFamTensorP T b)] (rootTensorBlock T b) := by
  haveI : FiniteDimensional ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) :=
    rootNormedExtensionFiniteDimensionalQp T b
  exact (blockLinearEquiv T b).symm.finiteDimensional

/-- Topological space on the tensor block. -/
noncomputable instance blockTopologicalSpace :
    TopologicalSpace (rootTensorBlock T b) := inferInstance

/-- Proper-space structure on the tensor block (finite dimension over Qp). -/
noncomputable instance blockProperSpace :
    ProperSpace (rootTensorBlock T b) :=
  FiniteDimensional.proper ℚ_[(qVFamTensorP T b)] (rootTensorBlock T b)

/-- Measurable space on the tensor block. -/
noncomputable instance blockMeasurableSpace :
    MeasurableSpace (rootTensorBlock T b) := borel (rootTensorBlock T b)

/-- Borel space on the tensor block. -/
noncomputable instance blockBorelSpace :
    BorelSpace (rootTensorBlock T b) := ⟨rfl⟩

/-- The actual positive compact unit ball of the tensor block. -/
noncomputable def blockUnitBallPositive :
    TopologicalSpace.PositiveCompacts (rootTensorBlock T b) where
  carrier := Metric.closedBall (0 : rootTensorBlock T b) 1
  isCompact' := by
    simpa using (ProperSpace.isCompact_closedBall (0 : rootTensorBlock T b) 1)
  interior_nonempty' := by
    refine ⟨0, ?_⟩
    rw [mem_interior_iff_mem_nhds]
    exact Metric.mem_nhds_iff.mpr ⟨1, by norm_num, by
      intro y hy
      exact Metric.ball_subset_closedBall hy⟩

noncomputable def blockUnitBall : Set (rootTensorBlock T b) :=
  (blockUnitBallPositive T b : Set (rootTensorBlock T b))

/-- Actual Haar on the tensor block. -/
noncomputable def blockHaar : Measure (rootTensorBlock T b) :=
  Measure.addHaarMeasure (blockUnitBallPositive T b)

theorem blockUnitBall_measure :
    blockHaar T b (blockUnitBall T b) = 1 := by
  unfold blockHaar blockUnitBall
  exact Measure.addHaarMeasure_self (K₀ := blockUnitBallPositive T b)

theorem blockUnitBall_measure_pos :
    0 < blockHaar T b (blockUnitBall T b) := by
  rw [blockUnitBall_measure]
  norm_num

theorem blockUnitBall_measure_lt_top :
    blockHaar T b (blockUnitBall T b) < ⊤ := by
  rw [blockUnitBall_measure]
  exact ENNReal.one_lt_top

noncomputable def blockHaarLog : Real :=
  Real.log (blockHaar T b (blockUnitBall T b)).toReal

theorem blockHaarLog_eq_zero : blockHaarLog T b = 0 := by
  unfold blockHaarLog
  rw [blockUnitBall_measure]
  norm_num


/-- Actual theta image set in the tensor block. -/
noncomputable def blockThetaImageSet : Set (rootTensorBlock T b) :=
  Set.range (rootTensorThetaImage T b)

/-- Actual closure hull of the theta image in the tensor block. -/
noncomputable def blockThetaHull : Set (rootTensorBlock T b) :=
  closure (blockThetaImageSet T b)

/-- Actual Haar measure of the theta image hull. -/
noncomputable def blockThetaHullMeasure : ENNReal :=
  blockHaar T b (blockThetaHull T b)

/-- Actual normalized log of the theta image hull. -/
noncomputable def blockThetaHullLog : Real :=
  Real.log (blockThetaHullMeasure T b).toReal

/-- Actual tensor Haar/theta data (no qPilot comparison). -/
structure BlockHaarData where
  haar : Measure (rootTensorBlock T b)
  haar_eq : haar = blockHaar T b
  unitBall : Set (rootTensorBlock T b)
  unitBall_eq : unitBall = blockUnitBall T b
  unitBall_measure : haar unitBall = 1
  thetaHull : Set (rootTensorBlock T b)
  thetaHull_eq : thetaHull = blockThetaHull T b
  thetaHullMeasure : ENNReal
  thetaHullMeasure_eq : thetaHullMeasure = blockThetaHullMeasure T b
  thetaHullLog : Real
  thetaHullLog_eq : thetaHullLog = blockThetaHullLog T b

noncomputable def blockHaarData : BlockHaarData T b where
  haar := blockHaar T b
  haar_eq := rfl
  unitBall := blockUnitBall T b
  unitBall_eq := rfl
  unitBall_measure := blockUnitBall_measure T b
  thetaHull := blockThetaHull T b
  thetaHull_eq := rfl
  thetaHullMeasure := blockThetaHullMeasure T b
  thetaHullMeasure_eq := rfl
  thetaHullLog := blockThetaHullLog T b
  thetaHullLog_eq := rfl


/-- The theta reference ball in the transported block: image of the L unit ball. -/
noncomputable def blockThetaReference : Set (rootTensorBlock T b) :=
  Metric.closedBall (0 : rootTensorBlock T b) 1

/-- Field scaling on the transported block by a ∈ L. -/
noncomputable def blockScalar (a : rootNormedExtension T b)
    (x : rootTensorBlock T b) : rootTensorBlock T b :=
  (blockLinearEquiv T b).symm (a * (blockLinearEquiv T b) x)

/-- The λO scaled region for a field scaling a. -/
noncomputable def blockScaledRegion (a : rootNormedExtension T b) :
    Set (rootTensorBlock T b) :=
  blockScalar T b a '' blockThetaReference T b


/-- Positive-label theta image point in the tensor block. -/
noncomputable def blockThetaImageThetaEarly (j : ThetaLabel (l := l)) :
    rootTensorBlock T b :=
  rootTensorThetaImage T b (thetaLabelToSigned (l := l) j)

/-- Positive-label theta image set in the tensor block. -/
noncomputable def blockThetaImageSetThetaEarly : Set (rootTensorBlock T b) :=
  Set.range (blockThetaImageThetaEarly T b)

/-- The actual θ λO scaling hull: union over positive theta labels of the scaled reference ball. -/
noncomputable def blockThetaScaledHull : Set (rootTensorBlock T b) :=
  blockThetaImageSetThetaEarly T b ∪
    ⋃ j : ThetaLabel (l := l),
      blockScaledRegion T b
        (rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) :
          rootNormedExtension T b)

/-- The actual theta image is contained in the λO scaling hull. -/
theorem blockThetaImage_subset_scaledHull :
    blockThetaImageSetThetaEarly T b ⊆ blockThetaScaledHull T b := by
  intro x hx
  exact Or.inl hx

/-- Actual Haar measure of the λO scaling hull. -/
noncomputable def blockThetaScaledHullMeasure : ENNReal :=
  blockHaar T b (blockThetaScaledHull T b)

/-- Actual normalized log of the λO scaling hull. -/
noncomputable def blockThetaScaledHullLog : Real :=
  Real.log (blockThetaScaledHullMeasure T b).toReal



/-- Bridge: the transported equivalence sends a root theta tensor image to
the corresponding root theta value in L. -/
theorem blockLinearEquiv_rootTensorThetaImage (j : SignedLabel l.value) :
    (blockLinearEquiv T b) (rootTensorThetaImage T b j) =
      (rootNormedThetaValueInL T b j : rootNormedExtension T b) := by
  change PiTensorProduct.subsingletonEquiv
      (R := ℚ_[(qVFamTensorP T b)]) (s := fun _ : Unit => rootNormedExtension T b)
      (i₀ := ()) (finitePadicTensorTprod (p := qVFamTensorP T b)
        (fun _ : Unit => rootNormedExtension T b)
        (fun _ : Unit => (rootNormedThetaValueInL T b j : rootNormedExtension T b))) =
    rootNormedThetaValueInL T b j
  rw [show finitePadicTensorTprod (p := qVFamTensorP T b)
      (fun _ : Unit => rootNormedExtension T b)
      (fun _ : Unit => (rootNormedThetaValueInL T b j : rootNormedExtension T b)) =
      PiTensorProduct.tprod ℚ_[(qVFamTensorP T b)]
        (fun _ : Unit => (rootNormedThetaValueInL T b j : rootNormedExtension T b)) from rfl]
  exact PiTensorProduct.subsingletonEquiv_apply_tprod
    (R := ℚ_[(qVFamTensorP T b)]) (s := fun _ : Unit => rootNormedExtension T b)
    (i₀ := ()) (f := fun _ : Unit =>
      (rootNormedThetaValueInL T b j : rootNormedExtension T b))

/-- Positive-label theta image in the tensor block. -/
noncomputable def blockThetaImageTheta (j : ThetaLabel (l := l)) :
    rootTensorBlock T b :=
  rootTensorThetaImage T b (thetaLabelToSigned (l := l) j)

/-- Positive-label theta image set in the tensor block. -/
noncomputable def blockThetaImageSetTheta : Set (rootTensorBlock T b) :=
  Set.range (blockThetaImageTheta T b)

/-- The single λO scaling value: maximal positive-label root theta value. -/
noncomputable def singleLambda : rootNormedExtension T b :=
  (rootNormedThetaValueInL T b
    (thetaLabelToSigned (l := l) (maxThetaLabel (l := l) T b)) :
    rootNormedExtension T b)

theorem singleLambda_ne_zero : singleLambda T b ≠ 0 :=
  rootNormedThetaValueInL_ne_zero T b
    (thetaLabelToSigned (l := l) (maxThetaLabel (l := l) T b))

/-- The single λO scaled region. -/
noncomputable def singleScaledRegion : Set (rootTensorBlock T b) :=
  blockScalar T b (singleLambda T b) '' blockThetaReference T b


/-- The reference ball is closed under scalar multiplication by norm ≤ 1. -/
theorem blockScalar_mem_reference {a : rootNormedExtension T b} (ha : ‖a‖ ≤ 1)
    {x : rootTensorBlock T b} (hx : x ∈ blockThetaReference T b) :
    blockScalar T b a x ∈ blockThetaReference T b := by
  rw [blockThetaReference, Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx ⊢
  unfold blockScalar
  rw [show ‖(blockLinearEquiv T b).symm (a * (blockLinearEquiv T b) x)‖ =
      ‖(blockLinearEquiv T b) ((blockLinearEquiv T b).symm
        (a * (blockLinearEquiv T b) x))‖ from rfl]
  rw [(blockLinearEquiv T b).apply_symm_apply, norm_mul]
  calc
    ‖a‖ * ‖(blockLinearEquiv T b) x‖ ≤ 1 * 1 :=
      mul_le_mul ha hx (norm_nonneg _) (by positivity)
    _ = 1 := by norm_num

/-- A norm-smaller scaling region is contained in the maximal single λO region. -/
theorem blockScaledRegion_subset_single {a : rootNormedExtension T b}
    (ha : ‖a‖ ≤ ‖singleLambda T b‖) :
    blockScaledRegion T b a ⊆ singleScaledRegion T b := by
  rintro x ⟨o, ho, rfl⟩
  have hb : ‖a / singleLambda T b‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.mpr (singleLambda_ne_zero T b))]
    exact ha
  refine ⟨blockScalar T b (a / singleLambda T b) o,
    blockScalar_mem_reference T b hb ho, ?_⟩
  unfold blockScalar
  rw [(blockLinearEquiv T b).apply_symm_apply]
  congr 1
  field_simp [singleLambda_ne_zero T b]

/-- Positive-label theta image is contained in the single λO region. -/
theorem blockThetaImageTheta_subset_singleScaledRegion (j : ThetaLabel (l := l)) :
    blockThetaImageTheta T b j ∈ singleScaledRegion T b := by
  have htheta := blockLinearEquiv_rootTensorThetaImage T b
    (thetaLabelToSigned (l := l) j)
  refine ⟨(blockLinearEquiv T b).symm
    ((rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) :
      rootNormedExtension T b) / singleLambda T b), ?_, ?_⟩
  · rw [blockThetaReference, Metric.mem_closedBall, dist_eq_norm, sub_zero]
    rw [show ‖(blockLinearEquiv T b).symm
        ((rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) :
          rootNormedExtension T b) / singleLambda T b)‖ =
        ‖(blockLinearEquiv T b) ((blockLinearEquiv T b).symm
          ((rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) :
            rootNormedExtension T b) / singleLambda T b))‖ from rfl]
    rw [(blockLinearEquiv T b).apply_symm_apply, norm_div]
    change ‖(rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) :
        rootNormedExtension T b)‖ /
      ‖(rootNormedThetaValueInL T b
        (thetaLabelToSigned (l := l) (maxThetaLabel (l := l) T b)) :
        rootNormedExtension T b)‖ ≤ 1
    rw [div_le_one (rootNormedThetaValueInL_norm_pos T b
      (thetaLabelToSigned (l := l) (maxThetaLabel (l := l) T b)))]
    exact maxThetaLabel_spec (l := l) T b j
  · have hsymm : blockThetaImageTheta T b j =
        (blockLinearEquiv T b).symm
          (rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) :
            rootNormedExtension T b) :=
      ((blockLinearEquiv T b).symm_apply_eq).mpr htheta.symm
    rw [hsymm]
    unfold blockScalar
    simp only [(blockLinearEquiv T b).apply_symm_apply,
      mul_div_cancel₀ _ (singleLambda_ne_zero T b)]

/-- Actual Haar measure of the single λO scaled region. -/
noncomputable def singleScaledRegionMeasure : ENNReal :=
  blockHaar T b (singleScaledRegion T b)

/-- Actual normalized log of the single λO scaled region. -/
noncomputable def singleScaledRegionLog : Real :=
  Real.log (singleScaledRegionMeasure T b).toReal


/-- The theta reference is the closed unit ball of the induced norm. -/
theorem blockThetaReference_eq_unitBall :
    blockThetaReference T b = (blockUnitBallPositive T b : Set (rootTensorBlock T b)) := rfl

theorem blockNorm_eq (x : rootTensorBlock T b) :
    ‖x‖ = ‖(blockLinearEquiv T b) x‖ := rfl

theorem blockThetaReference_compact : IsCompact (blockThetaReference T b) := by
  rw [blockThetaReference_eq_unitBall]
  exact (blockUnitBallPositive T b).isCompact'

theorem blockThetaReference_interior_nonempty :
    (interior (blockThetaReference T b)).Nonempty := by
  rw [blockThetaReference_eq_unitBall]
  exact (blockUnitBallPositive T b).interior_nonempty'

/-- Unit scaling by the nonzero single lambda in L. -/
noncomputable def singleScaleUnit : (rootNormedExtension T b)ˣ :=
  Units.mk0 (singleLambda T b) (singleLambda_ne_zero T b)

/-- The linear equivalence of the block induced by single-lambda scaling. -/
noncomputable def singleScaleLinearEquiv :
    rootTensorBlock T b ≃ₗ[ℚ_[(qVFamTensorP T b)]] rootTensorBlock T b :=
  (blockLinearEquiv T b).trans
    (((singleScaleUnit T b).mulLeftLinearEquiv ℚ_[(qVFamTensorP T b)]
      (rootNormedExtension T b)).trans (blockLinearEquiv T b).symm)

/-- The continuous linear equivalence of the block induced by single-lambda scaling. -/
noncomputable def singleScaleCLE :
    rootTensorBlock T b ≃L[ℚ_[(qVFamTensorP T b)]] rootTensorBlock T b :=
  (singleScaleLinearEquiv T b).toContinuousLinearEquiv

theorem singleScaleCLE_apply (x : rootTensorBlock T b) :
    singleScaleCLE T b x = blockScalar T b (singleLambda T b) x := by
  unfold singleScaleCLE singleScaleLinearEquiv blockScalar
  simp [singleScaleUnit]

/-- The single λO region is the image of the reference under scaling. -/
theorem singleScaledRegion_eq_image :
    singleScaledRegion T b = singleScaleCLE T b '' blockThetaReference T b := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, (singleScaleCLE_apply T b y).symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, singleScaleCLE_apply T b y⟩

theorem singleScaledRegion_compact : IsCompact (singleScaledRegion T b) := by
  rw [singleScaledRegion_eq_image]
  exact (blockThetaReference_compact T b).image (singleScaleCLE T b).continuous

theorem singleScaledRegion_interior_nonempty :
    (interior (singleScaledRegion T b)).Nonempty := by
  rw [singleScaledRegion_eq_image]
  obtain ⟨x, hx⟩ := blockThetaReference_interior_nonempty T b
  refine ⟨singleScaleCLE T b x, ?_⟩
  have h := (singleScaleCLE T b).toHomeomorph.image_interior
    (blockThetaReference T b)
  have hx' : (singleScaleCLE T b).toHomeomorph x ∈
      (singleScaleCLE T b).toHomeomorph '' interior (blockThetaReference T b) :=
    ⟨x, hx, rfl⟩
  rw [h] at hx'
  simpa [singleScaledRegion_eq_image] using hx'

theorem singleScaledRegionMeasure_pos : 0 < singleScaledRegionMeasure T b := by
  unfold singleScaledRegionMeasure
  haveI : Measure.IsAddHaarMeasure (blockHaar T b) :=
    Measure.isAddHaarMeasure_addHaarMeasure (blockUnitBallPositive T b)
  have hne : blockHaar T b (interior (singleScaledRegion T b)) ≠ 0 :=
    Measure.IsOpenPosMeasure.open_pos (interior (singleScaledRegion T b))
      isOpen_interior (singleScaledRegion_interior_nonempty T b)
  exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hne)
    (measure_mono interior_subset)

theorem singleScaledRegionMeasure_lt_top : singleScaledRegionMeasure T b < ⊤ := by
  unfold singleScaledRegionMeasure
  haveI : Measure.IsAddHaarMeasure (blockHaar T b) :=
    Measure.isAddHaarMeasure_addHaarMeasure (blockUnitBallPositive T b)
  haveI : MeasureTheory.IsFiniteMeasureOnCompacts (blockHaar T b) := inferInstance
  exact MeasureTheory.IsFiniteMeasureOnCompacts.lt_top_of_isCompact
    (singleScaledRegion_compact T b)

theorem singleScaledRegionLog_eq :
    singleScaledRegionLog T b =
      Real.log (singleScaledRegionMeasure T b).toReal := rfl


/-- The single λO region is the component of the full scaling hull at the
maximal positive theta label. -/
theorem singleScaledRegion_eq_component :
    singleScaledRegion T b =
      blockScaledRegion T b
        (rootNormedThetaValueInL T b
          (thetaLabelToSigned (l := l) (maxThetaLabel (l := l) T b)) :
          rootNormedExtension T b) := by
  unfold singleScaledRegion singleLambda
  rfl

/-- The single λO region is contained in the full λO scaling hull. -/
theorem singleScaledRegion_subset_scaledHull :
    singleScaledRegion T b ⊆ blockThetaScaledHull T b := by
  rw [singleScaledRegion_eq_component]
  intro x hx
  exact Or.inr (Set.mem_iUnion.mpr
    ⟨maxThetaLabel (l := l) T b, hx⟩)

/-- Exact decomposition of the full hull: the single λO region plus the rest. -/
theorem blockThetaScaledHull_eq_single_union_sdiff :
    blockThetaScaledHull T b =
      singleScaledRegion T b ∪
        (blockThetaScaledHull T b \ singleScaledRegion T b) := by
  ext x
  constructor
  · intro hx
    by_cases hxs : x ∈ singleScaledRegion T b
    · exact Or.inl hxs
    · exact Or.inr ⟨hx, hxs⟩
  · rintro (hx | ⟨hx, _⟩)
    · exact singleScaledRegion_subset_scaledHull T b hx
    · exact hx

/-- Measure monotonicity: the single λO region has measure at most the full hull. -/
theorem singleScaledRegionMeasure_le_scaledHull :
    singleScaledRegionMeasure T b ≤ blockThetaScaledHullMeasure T b := by
  unfold singleScaledRegionMeasure blockThetaScaledHullMeasure
  exact measure_mono (singleScaledRegion_subset_scaledHull T b)


/-- Composition of block scalars. -/
theorem blockScalar_blockScalar (a c : rootNormedExtension T b)
    (x : rootTensorBlock T b) :
    blockScalar T b a (blockScalar T b c x) = blockScalar T b (a * c) x := by
  unfold blockScalar
  simp only [(blockLinearEquiv T b).apply_symm_apply]
  congr 1
  ring

/-- The full positive-label λO scaling hull is contained in the single maximal region. -/
theorem blockThetaScaledHull_subset_single :
    blockThetaScaledHull T b ⊆ singleScaledRegion T b := by
  rintro x (hx | hx)
  · rcases hx with ⟨j, rfl⟩
    have htheta := blockLinearEquiv_rootTensorThetaImage T b
      (thetaLabelToSigned (l := l) j)
    have hmem : blockThetaImageThetaEarly T b j ∈
        blockScaledRegion T b
          (rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) :
            rootNormedExtension T b) := by
      refine ⟨(blockLinearEquiv T b).symm 1, ?_, ?_⟩
      · rw [blockThetaReference, Metric.mem_closedBall, dist_eq_norm, sub_zero]
        rw [show ‖(blockLinearEquiv T b).symm (1 : rootNormedExtension T b)‖ =
            ‖(blockLinearEquiv T b) ((blockLinearEquiv T b).symm
              (1 : rootNormedExtension T b))‖ from rfl]
        rw [(blockLinearEquiv T b).apply_symm_apply]
        norm_num
      · have hsymm : blockThetaImageThetaEarly T b j =
            (blockLinearEquiv T b).symm
              (rootNormedThetaValueInL T b
                (thetaLabelToSigned (l := l) j) : rootNormedExtension T b) :=
          ((blockLinearEquiv T b).symm_apply_eq).mpr htheta.symm
        rw [hsymm]
        unfold blockScalar
        rw [(blockLinearEquiv T b).apply_symm_apply, mul_one]
    exact blockScaledRegion_subset_single T b
      (maxThetaLabel_spec (l := l) T b j) hmem
  · rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
    exact blockScaledRegion_subset_single T b
      (maxThetaLabel_spec (l := l) T b j) hj

/-- The single maximal region is exactly the full positive-label λO scaling hull. -/
theorem blockThetaScaledHull_eq_single :
    blockThetaScaledHull T b = singleScaledRegion T b :=
  le_antisymm (blockThetaScaledHull_subset_single T b)
    (singleScaledRegion_subset_scaledHull T b)

theorem blockThetaScaledHullMeasure_eq_single :
    blockThetaScaledHullMeasure T b = singleScaledRegionMeasure T b := by
  unfold blockThetaScaledHullMeasure singleScaledRegionMeasure
  rw [blockThetaScaledHull_eq_single]

theorem blockThetaScaledHullMeasure_pos : 0 < blockThetaScaledHullMeasure T b := by
  rw [blockThetaScaledHullMeasure_eq_single]
  exact singleScaledRegionMeasure_pos T b

theorem blockThetaScaledHullMeasure_lt_top :
    blockThetaScaledHullMeasure T b < ⊤ := by
  rw [blockThetaScaledHullMeasure_eq_single]
  exact singleScaledRegionMeasure_lt_top T b

theorem blockThetaScaledHullLog_eq_single :
    blockThetaScaledHullLog T b = singleScaledRegionLog T b := by
  unfold blockThetaScaledHullLog singleScaledRegionLog
  rw [blockThetaScaledHullMeasure_eq_single]


/-- The single λO region is closed under scaling by norm-one field units
(subset form). -/
theorem singleScaledRegion_blockScalar_unit_subset {u : rootNormedExtension T b}
    (hu : ‖u‖ = 1) :
    blockScalar T b u '' singleScaledRegion T b ⊆ singleScaledRegion T b := by
  rintro x ⟨y, hy, rfl⟩
  unfold singleScaledRegion at hy ⊢
  rcases hy with ⟨o, ho, rfl⟩
  rw [blockScalar_blockScalar]
  refine ⟨blockScalar T b u o,
    blockScalar_mem_reference T b (by rw [hu]) ho, ?_⟩
  rw [blockScalar_blockScalar]
  congr 1
  ring


/-- Scaling by one is the identity on the block. -/
theorem blockScalar_one (x : rootTensorBlock T b) :
    blockScalar T b 1 x = x := by
  unfold blockScalar
  simp

/-- Norm-one scaling is automatically invertible. -/
theorem blockScalar_unit_ne_zero {u : rootNormedExtension T b} (hu : ‖u‖ = 1) :
    u ≠ 0 := by
  intro h
  rw [h, norm_zero] at hu
  norm_num at hu

/-- Reverse inclusion: the single λO region is contained in its image under
any norm-one scaling. -/
theorem singleScaledRegion_subset_blockScalar_unit_image
    {u : rootNormedExtension T b} (hu : ‖u‖ = 1) :
    singleScaledRegion T b ⊆ blockScalar T b u '' singleScaledRegion T b := by
  have hu_ne := blockScalar_unit_ne_zero T b hu
  have hu_inv_norm : ‖u⁻¹‖ = 1 := by
    rw [norm_inv, hu, inv_one]
  intro x hx
  have hx' : blockScalar T b u⁻¹ x ∈ singleScaledRegion T b :=
    singleScaledRegion_blockScalar_unit_subset T b hu_inv_norm ⟨x, hx, rfl⟩
  refine ⟨blockScalar T b u⁻¹ x, hx', ?_⟩
  rw [blockScalar_blockScalar, mul_inv_cancel₀ hu_ne, blockScalar_one]

/-- Equality under norm-one scaling. -/
theorem singleScaledRegion_blockScalar_unit_eq
    {u : rootNormedExtension T b} (hu : ‖u‖ = 1) :
    blockScalar T b u '' singleScaledRegion T b = singleScaledRegion T b :=
  Set.Subset.antisymm
    (singleScaledRegion_blockScalar_unit_subset T b hu)
    (singleScaledRegion_subset_blockScalar_unit_image T b hu)

/-- A set is O×-scaling closed if it is invariant under every norm-one scaling. -/
def IsOUnitScalingClosed (S : Set (rootTensorBlock T b)) : Prop :=
  ∀ u : rootNormedExtension T b, ‖u‖ = 1 →
    blockScalar T b u '' S = S

/-- The single λO region is an actual O×-scaling closed set object. -/
theorem singleScaledRegion_isOUnitScalingClosed :
    IsOUnitScalingClosed T b (singleScaledRegion T b) := by
  intro u hu
  exact singleScaledRegion_blockScalar_unit_eq T b hu


/-- The positive-label root theta image is contained in the single λO region. -/
theorem blockThetaImageSetThetaEarly_subset_single :
    blockThetaImageSetThetaEarly T b ⊆ singleScaledRegion T b := by
  intro x hx
  rw [← blockThetaScaledHull_eq_single]
  exact Or.inl hx

/-- Exact object requirement from PAPER_OBJECT_SPEC that is not yet proved:
the λO hull is not the full unit ball. -/
def ThetaHullNotUnitBallExact : Prop :=
  singleScaledRegion T b ≠ (blockUnitBallPositive T b : Set (rootTensorBlock T b))

/-- Packaged actual ThetaHolomorphicHull object. -/
structure ThetaHolomorphicHullObject where
  carrier : Set (rootTensorBlock T b)
  carrier_eq : carrier = singleScaledRegion T b
  contains_root_image : blockThetaImageSetThetaEarly T b ⊆ carrier
  isOUnitScalingClosed : IsOUnitScalingClosed T b carrier
  isCompact : IsCompact carrier
  scalingValue : rootNormedExtension T b
  scalingValue_ne_zero : scalingValue ≠ 0
  isLambdaOScaled : carrier = blockScalar T b scalingValue '' blockThetaReference T b
  haar : Measure (rootTensorBlock T b)
  haar_eq : haar = blockHaar T b
  measure : ENNReal
  measure_eq : measure = haar carrier
  measure_pos : 0 < measure
  measure_lt_top : measure < ⊤
  log : Real
  log_eq : log = Real.log measure.toReal

/-- The actual ThetaHolomorphicHull object. -/
noncomputable def thetaHolomorphicHullObject : ThetaHolomorphicHullObject T b where
  carrier := singleScaledRegion T b
  carrier_eq := rfl
  contains_root_image := blockThetaImageSetThetaEarly_subset_single T b
  isOUnitScalingClosed := singleScaledRegion_isOUnitScalingClosed T b
  isCompact := singleScaledRegion_compact T b
  scalingValue := singleLambda T b
  scalingValue_ne_zero := singleLambda_ne_zero T b
  isLambdaOScaled := rfl
  haar := blockHaar T b
  haar_eq := rfl
  measure := singleScaledRegionMeasure T b
  measure_eq := rfl
  measure_pos := singleScaledRegionMeasure_pos T b
  measure_lt_top := singleScaledRegionMeasure_lt_top T b
  log := singleScaledRegionLog T b
  log_eq := rfl



/-- The actual root has norm strictly less than one. -/
theorem rootNormedElement_norm_lt_one :
    ‖(rootNormedElement T b : rootNormedAmbient T b)‖ < 1 := by
  have hq : ‖((sourceRootQUnit T b : rootBase T b))‖ < 1 := by
    change ‖qVFamNormalizedGenerator T b‖ < 1
    exact qVFamNormalizedGenerator_norm_lt_one T b
  have hpow := rootNormedElement_pow T b
  have hnormpow :
      ‖(rootNormedElement T b : rootNormedAmbient T b)‖ ^ (2 * l.value) < 1 := by
    rw [← norm_pow, hpow]
    simpa [rootNormedAmbient, rootBase, unitToAlgClosed, norm_algebraMap'] using hq
  have hnz : 2 * l.value ≠ 0 := Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hnz).mp hnormpow

/-- Nonzero root theta values in L have norm strictly less than one. -/
theorem rootNormedThetaValueInL_norm_lt_one {j : SignedLabel l.value}
    (hj : j.1 ≠ 0) :
    ‖(rootNormedThetaValueInL T b j : rootNormedExtension T b)‖ < 1 := by
  change ‖((rootNormedThetaValue T b j : rootNormedAmbient T b))‖ < 1
  unfold rootNormedThetaValue
  rw [norm_zpow]
  have hroot_pos : 0 < ‖(rootNormedElement T b : rootNormedAmbient T b)‖ :=
    norm_pos_iff.mpr (rootNormedElement_ne_zero T b)
  have hroot_lt : ‖(rootNormedElement T b : rootNormedAmbient T b)‖ < 1 :=
    rootNormedElement_norm_lt_one T b
  have hgauss : 0 < gaussExponent j.1 := by
    unfold gaussExponent
    exact sq_pos_of_ne_zero hj
  exact zpow_lt_one₀ hroot_pos hroot_lt hgauss

/-- The maximal scaling lambda has norm strictly less than one. -/
theorem singleLambda_norm_lt_one : ‖singleLambda T b‖ < 1 := by
  unfold singleLambda
  exact rootNormedThetaValueInL_norm_lt_one T b
    (ne_of_gt (maxThetaLabel (l := l) T b).2)

/-- Norm bound for block scalar multiplication. -/
theorem blockScalar_norm_le (a : rootNormedExtension T b)
    (x : rootTensorBlock T b) :
    ‖blockScalar T b a x‖ ≤ ‖a‖ * ‖x‖ := by
  unfold blockScalar
  rw [show ‖(blockLinearEquiv T b).symm (a * (blockLinearEquiv T b) x)‖ =
      ‖(blockLinearEquiv T b) ((blockLinearEquiv T b).symm
        (a * (blockLinearEquiv T b) x))‖ from rfl]
  rw [(blockLinearEquiv T b).apply_symm_apply, norm_mul]
  rw [show ‖x‖ = ‖(blockLinearEquiv T b) x‖ from rfl]

theorem blockScalar_norm_lt_one_of_mem_reference
    (a : rootNormedExtension T b) (ha : ‖a‖ < 1) {o : rootTensorBlock T b}
    (ho : o ∈ blockThetaReference T b) :
    ‖blockScalar T b a o‖ < 1 := by
  have ho_le : ‖o‖ ≤ 1 := by
    rw [blockThetaReference, Metric.mem_closedBall, dist_eq_norm, sub_zero] at ho
    exact ho
  calc
    ‖blockScalar T b a o‖ ≤ ‖a‖ * ‖o‖ := blockScalar_norm_le T b a o
    _ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left ho_le (norm_nonneg _)
    _ = ‖a‖ := mul_one _
    _ < 1 := ha

/-- The λO region is not the full unit ball. -/
theorem singleScaledRegion_ne_unitBall :
    singleScaledRegion T b ≠ (blockUnitBallPositive T b : Set (rootTensorBlock T b)) := by
  intro h
  have hx_ball : (blockLinearEquiv T b).symm 1 ∈
      (blockUnitBallPositive T b : Set (rootTensorBlock T b)) := by
    rw [← blockThetaReference_eq_unitBall]
    rw [blockThetaReference, Metric.mem_closedBall, dist_eq_norm, sub_zero]
    rw [show ‖(blockLinearEquiv T b).symm (1 : rootNormedExtension T b)‖ =
        ‖(blockLinearEquiv T b) ((blockLinearEquiv T b).symm
          (1 : rootNormedExtension T b))‖ from rfl]
    rw [(blockLinearEquiv T b).apply_symm_apply]
    norm_num
  have hx_norm : ‖(blockLinearEquiv T b).symm (1 : rootNormedExtension T b)‖ = 1 := by
    rw [show ‖(blockLinearEquiv T b).symm (1 : rootNormedExtension T b)‖ =
        ‖(blockLinearEquiv T b) ((blockLinearEquiv T b).symm
          (1 : rootNormedExtension T b))‖ from rfl]
    rw [(blockLinearEquiv T b).apply_symm_apply]
    norm_num
  have hx_single : (blockLinearEquiv T b).symm 1 ∈ singleScaledRegion T b := by
    rw [h]
    exact hx_ball
  have hx_single' : ∃ o ∈ blockThetaReference T b,
      blockScalar T b (singleLambda T b) o =
        (blockLinearEquiv T b).symm 1 := by
    simpa [singleScaledRegion] using hx_single
  rcases hx_single' with ⟨o, ho, heq⟩
  have hlt : ‖blockScalar T b (singleLambda T b) o‖ < 1 :=
    blockScalar_norm_lt_one_of_mem_reference T b (singleLambda T b)
      (singleLambda_norm_lt_one T b) ho
  rw [heq, hx_norm] at hlt
  exact lt_irrefl 1 hlt


/-- The packaged hull is not the full unit ball. -/
theorem thetaHullNotUnitBallExact :
    ThetaHullNotUnitBallExact T b :=
  singleScaledRegion_ne_unitBall T b

end LeanFormal.IUT.XiFPaper.RootTensorHaarTransportActual

end