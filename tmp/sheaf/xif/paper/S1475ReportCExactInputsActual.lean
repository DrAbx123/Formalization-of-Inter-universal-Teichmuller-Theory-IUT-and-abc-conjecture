import tmp.sheaf.xif.paper.S1086PerBQ1URootHullActual
import tmp.sheaf.xif.paper.S1095PushforwardHullEqActual
import tmp.sheaf.xif.paper.S1072CanonicalQ1URegionActual
import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual
import tmp.sheaf.xif.paper.S863ProductImageCompactActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalTensorLattice
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIntegerTensorComparison

/-!
# S1475: route C exact inputs, actual tensor/hull/Lambda-O proofs

Route C of the gap report leaves three exact inputs for the xi-f normalized
readout: the q[1u] image containment (`S1086Q1UImageContainment`, equivalently
`S1087CoeffLe`), the q[1u] image measurability
(`S1086Q1URegionMeasurable`), and the product-lattice identification
`S863ProductImageEq`.  This file proves one of them, the measurability input,
from the actual tensor/lattice data, without any ambient Haar = pushforward
assumption.

What is used (all actual, already in the tree):

* `qPilotQ1URegion = F(qVFamPureCoefficient) * O_hol` is a `Zp`-submodule of
  the one-factor qVFam tensor block;
* `F(qVFamPureCoefficient)` is an open compact norm-ball tensor lattice
  (`padicFractionalLattice`, nonnegative actual coefficient, and
  `isOpen_submoduleTensorSpan`);
* the qVFam region therefore contains an open subset and, being an additive
  subgroup, is open (hence Borel);
* the root-stack embedding is a finite-dimensional injective linear map, hence
  a closed embedding (`LinearMap.isClosedEmbedding_of_injective`), hence a
  measurable embedding; the image of the Borel q[1u] region is Borel.

No Haar equality, no `S1086HaarEq`, no ambient = pushforward is used or
asserted.  The two remaining inputs (containment and product-lattice
identification) are not claimed here.
-/

noncomputable section
open scoped BigOperators TensorProduct Topology Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1475ReportCExactInputsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataGapActual
open LeanFormal.IUT.XiFPaper.S1072CanonicalQ1URegionActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S1086PerBQ1URootHullActual
open LeanFormal.IUT.XiFPaper.S1095PushforwardHullEqActual
open LeanFormal.IUT.XiFPaper.S1073RootStackPaperThetaHullActual
open LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S839PaperRootMinimalProductCompactActual
open LeanFormal.IUT.XiFPaper.S841FractionalCompactAbsorptionActual
open LeanFormal.IUT.XiFPaper.S863ProductImageCompactActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (N8Closure.nativePlaceSelection T))]
variable [∀ b : Bad (N8Closure.nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (N8Closure.nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (N8Closure.nativePlaceSelection T))

/-! ## 1. The actual local norm-ball lattice spans the local field

The q[1u] fractional lattice is the tensor of the local norm balls
`padicFractionalLattice c_i`.  For the openness of the tensor lattice we need
that each local ball is a full `Qp`-lattice; this is the exact-generator-free
statement `span Qp (F a) = top`, proved by shifting into the valuation
integers. -/

theorem s1475LocalFractionalSpan_eq_top
    {p : ℕ} [Fact p.Prime] {K : Type*} [NormedField K] [IsUltrametricDist K]
    [NormedAlgebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] (a : ℝ) :
    Submodule.span ℚ_[p] (padicFractionalLattice (p := p) (K := K) a : Set K) = ⊤ := by
  obtain ⟨N, hN⟩ := exists_nat_ge a
  apply top_unique
  rw [← span_padic_valuationIntegerLattice_eq_top (p := p) (K := K)]
  rw [Submodule.span_le]
  intro x hx
  have hx1 : ‖x‖ ≤ 1 := (mem_integers_iff x).mp hx
  have hp_pos : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).pos
  have hp_one : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hnorm : ‖(p : K) ^ N‖ = (p : ℝ) ^ (-(N : ℝ)) := by
    have h := norm_prime_zpow (p := p) (K := K) (N : ℤ)
    simpa using h
  have hmem : ((p : ℚ_[p]) ^ N) • x ∈
      padicFractionalLattice (p := p) (K := K) a := by
    rw [Algebra.smul_def, map_pow, map_natCast, mem_padicFractionalLattice_iff,
      norm_mul, hnorm]
    have hNle : (p : ℝ) ^ (-(N : ℝ)) ≤ (p : ℝ) ^ (-a) :=
      Real.rpow_le_rpow_of_exponent_le hp_one (by linarith)
    calc
      (p : ℝ) ^ (-(N : ℝ)) * ‖x‖ ≤ (p : ℝ) ^ (-(N : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left hx1 (Real.rpow_nonneg hp_pos.le _)
      _ = (p : ℝ) ^ (-(N : ℝ)) := mul_one _
      _ ≤ (p : ℝ) ^ (-a) := hNle
  have hpN : ((p : ℚ_[p]) ^ N) ≠ 0 := by
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hx_eq : ((p : ℚ_[p]) ^ N)⁻¹ • (((p : ℚ_[p]) ^ N) • x) = x := by
    rw [smul_smul, inv_mul_cancel₀ hpN, one_smul]
  rw [← hx_eq]
  exact Submodule.smul_mem (Submodule.span ℚ_[p] (padicFractionalLattice (p := p) (K := K) a : Set K)) _
    (Submodule.subset_span hmem)

/-! ## 2. The actual q[1u] fractional lattice is open -/

theorem s1475Q1UFractionalLattice_open :
    IsOpen (arithmeticTupleFractionalLattice (qVFamTensorPlaces T b) qVFamTensorTuple
      (qVFamPureCoefficient T b) : Set (qVFamTensorBlock T b)) := by
  have hnonneg : ∀ i : qVFamTensorV, 0 ≤ qVFamPureCoefficient T b i := by
    intro i
    have hi : i = () := Subsingleton.elim _ _
    rw [hi]
    exact (qVFamPureCoefficient_pos (l := l) T b).le
  have hspan : ∀ i : qVFamTensorV,
      Submodule.span ℚ_[qVFamTensorP T b]
        (padicFractionalLattice (p := qVFamTensorP T b)
          (K := CommonPrimeCompletion ((qVFamTensorPlaces T b) i (qVFamTensorTuple i)))
          (qVFamPureCoefficient T b i) :
            Set (CommonPrimeCompletion ((qVFamTensorPlaces T b) i (qVFamTensorTuple i)))) = ⊤ := by
    intro i
    exact s1475LocalFractionalSpan_eq_top (p := qVFamTensorP T b)
      (K := CommonPrimeCompletion ((qVFamTensorPlaces T b) i (qVFamTensorTuple i)))
      (qVFamPureCoefficient T b i)
  letI : ∀ i, Module.Free ℤ_[qVFamTensorP T b]
      (padicFractionalLattice (p := qVFamTensorP T b)
        (K := CommonPrimeCompletion ((qVFamTensorPlaces T b) i (qVFamTensorTuple i)))
        (qVFamPureCoefficient T b i)) := fun i =>
    free_padicFractionalLattice_of_nonneg
      (p := qVFamTensorP T b)
      (K := CommonPrimeCompletion ((qVFamTensorPlaces T b) i (qVFamTensorTuple i)))
      (qVFamPureCoefficient T b i) (hnonneg i)
  letI : ∀ i, Module.Finite ℤ_[qVFamTensorP T b]
      (padicFractionalLattice (p := qVFamTensorP T b)
        (K := CommonPrimeCompletion ((qVFamTensorPlaces T b) i (qVFamTensorTuple i)))
        (qVFamPureCoefficient T b i)) := fun i =>
    finite_padicFractionalLattice_of_nonneg
      (p := qVFamTensorP T b)
      (K := CommonPrimeCompletion ((qVFamTensorPlaces T b) i (qVFamTensorTuple i)))
      (qVFamPureCoefficient T b i) (hnonneg i)
  simpa [arithmeticTupleFractionalLattice] using
    isOpen_submoduleTensorSpan (p := qVFamTensorP T b)
      (M := fun i => CommonPrimeCompletion ((qVFamTensorPlaces T b) i (qVFamTensorTuple i)))
      (S := fun i => padicFractionalLattice (p := qVFamTensorP T b)
        (K := CommonPrimeCompletion ((qVFamTensorPlaces T b) i (qVFamTensorTuple i)))
        (qVFamPureCoefficient T b i)) hspan

/-! ## 3. The q[1u] region is open (actual subgroup containing the open lattice) -/

theorem s1475Q1URegion_open :
    IsOpen (qPilotQ1URegion (l := l) T b) := by
  unfold qPilotQ1URegion
  have hFopen := s1475Q1UFractionalLattice_open (l := l) T b
  have hzero : (0 : qVFamTensorBlock T b) ∈
      arithmeticTupleFractionalLattice (qVFamTensorPlaces T b) qVFamTensorTuple
        (qVFamPureCoefficient T b) := Submodule.zero_mem _
  have hone : (1 : qVFamTensorBlock T b) ∈
      arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple := by
    unfold arithmeticTupleHolomorphicLattice
    exact (integralClosure ℤ_[qVFamTensorP T b] (qVFamTensorBlock T b)).one_mem
  have hsub : (arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
        qVFamTensorTuple (qVFamPureCoefficient T b) : Set (qVFamTensorBlock T b)) ⊆
      ((arithmeticTupleFractionalLattice (qVFamTensorPlaces T b) qVFamTensorTuple
          (qVFamPureCoefficient T b) *
        arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :
          Submodule ℤ_[qVFamTensorP T b] (qVFamTensorBlock T b)) :
        Set (qVFamTensorBlock T b)) := by
    intro x hx
    have hmul := Submodule.mul_mem_mul hx hone
    simpa using hmul
  have hnhds : ((arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
        qVFamTensorTuple (qVFamPureCoefficient T b) *
      arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :
        Submodule ℤ_[qVFamTensorP T b] (qVFamTensorBlock T b)) :
      Set (qVFamTensorBlock T b)) ∈ 𝓝 (0 : qVFamTensorBlock T b) :=
    Filter.mem_of_superset (hFopen.mem_nhds hzero) hsub
  exact AddSubgroup.isOpen_of_mem_nhds
    ((arithmeticTupleFractionalLattice (qVFamTensorPlaces T b) qVFamTensorTuple
        (qVFamPureCoefficient T b) *
      arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :
        Submodule ℤ_[qVFamTensorP T b] (qVFamTensorBlock T b)).toAddSubgroup)
    hnhds

/-! ## 4. The root-stack embedding is a closed embedding -/

theorem s1475RootStackEmbedding_isClosedEmbedding :
    Topology.IsClosedEmbedding (rootStackEmbedding (l := l) T b) := by
  have h1 : Topology.IsClosedEmbedding
      (fun x => qVFamBlockLinearEquiv (l := l) T b x) :=
    LinearMap.isClosedEmbedding_of_injective (𝕜 := ℚ_[qVFamTensorP T b])
      (E := qVFamTensorBlock T b) (F := rootBase T b)
      (f := (qVFamBlockLinearEquiv (l := l) T b).toLinearMap) (by
        rw [LinearMap.ker_eq_bot]
        exact (qVFamBlockLinearEquiv (l := l) T b).injective)
  have h2 : Topology.IsClosedEmbedding
      (fun x => algebraMap (rootBase T b) (rootNormedExtension T b) x) := by
    haveI : CompleteSpace (rootBase T b) := inferInstance
    exact LinearMap.isClosedEmbedding_of_injective
      (f := Algebra.linearMap (rootBase T b) (rootNormedExtension T b)) (by
        rw [LinearMap.ker_eq_bot]
        exact (algebraMap (rootBase T b) (rootNormedExtension T b)).injective)
  have h3 : Topology.IsClosedEmbedding
      (fun x => algebraMap (rootNormedExtension T b) (rootStackExtension T b) x) := by
    haveI : CompleteSpace (rootNormedExtension T b) :=
      rootNormedExtensionComplete (l := l) T b
    exact LinearMap.isClosedEmbedding_of_injective
      (f := Algebra.linearMap (rootNormedExtension T b) (rootStackExtension T b)) (by
        rw [LinearMap.ker_eq_bot]
        exact (algebraMap (rootNormedExtension T b) (rootStackExtension T b)).injective)
  have h := h3.comp (h2.comp h1)
  change Topology.IsClosedEmbedding
    (fun x => algebraMap (rootNormedExtension T b) (rootStackExtension T b)
      (algebraMap (rootBase T b) (rootNormedExtension T b)
        (qVFamBlockLinearEquiv (l := l) T b x)))
  exact h

/-! ## 5. Exact input: q[1u] image measurability -/

theorem s1475Q1URegionMeasurable_actual :
    S1086Q1URegionMeasurable (l := l) T b := by
  unfold S1086Q1URegionMeasurable
  have hq : MeasurableSet (qPilotQ1URegion (l := l) T b) :=
    (s1475Q1URegion_open (l := l) T b).measurableSet
  have hce := s1475RootStackEmbedding_isClosedEmbedding (l := l) T b
  exact hce.measurableEmbedding.measurableSet_image' hq

/-! ## 6. Exact first lemma for the containment input

The geometric input `S1086Q1UImageContainment` is exactly the region-level
inclusion of the actual q[1u] region in the actual paper lambda-O region; the
root-stack embedding is injective, so nothing about Haar or pushforward enters
this reduction. -/

theorem s1475Q1UImageContainment_iff_region :
    S1086Q1UImageContainment (l := l) T b ↔
      qPilotQ1URegion (l := l) T b ⊆
        paperLambdaORegion (l := l) T b
          (paperRootCoefficientFamily (l := l) T b) := by
  constructor
  · intro h x hx
    have hx0 : rootStackEmbedding (l := l) T b x ∈
        rootStackEmbedding (l := l) T b '' qPilotQ1URegion (l := l) T b :=
      Set.mem_image_of_mem (rootStackEmbedding (l := l) T b) hx
    have hx' := h hx0
    unfold rootStackPaperThetaHull at hx'
    rcases hx' with ⟨y, hy, hyx⟩
    rw [(rootStackEmbedding_injective_actual (l := l) T b) hyx] at hy
    exact hy
  · intro h
    unfold S1086Q1UImageContainment rootStackPaperThetaHull
    exact Set.image_mono h

/-! ## 7. Exact first lemma for the product-lattice input

The product-lattice identification `S863ProductImageEq` is not an independent
gap: pointwise absorption `F * O_hol <= F` (equivalently the existing S853
input `O_hol <= F(0)`) implies it.  Both sides are then the fractional lattice
`F`: the pointwise product image is `F` because `1 in O_hol`, and the
submodule product is `F` by the absorption hypothesis. -/

theorem s1475ProductImageEq_of_pointwise_absorption
    (h : S841PointwiseAbsorption (l := l) T b) :
    S863ProductImageEq (l := l) T b := by
  have hone : (1 : qVFamTensorBlock T b) ∈ s839HolomorphicLattice (l := l) T b := by
    unfold s839HolomorphicLattice arithmeticTupleHolomorphicLattice
    exact (integralClosure ℤ_[qVFamTensorP T b] (qVFamTensorBlock T b)).one_mem
  have hmul_le : s839FractionalLattice (l := l) T b *
      s839HolomorphicLattice (l := l) T b ≤ s839FractionalLattice (l := l) T b :=
    Submodule.mul_le.mpr h
  have hF_le : s839FractionalLattice (l := l) T b ≤
      s839FractionalLattice (l := l) T b * s839HolomorphicLattice (l := l) T b := by
    intro x hx
    simpa using Submodule.mul_mem_mul hx hone
  have hFO : s839FractionalLattice (l := l) T b *
      s839HolomorphicLattice (l := l) T b = s839FractionalLattice (l := l) T b :=
    le_antisymm hmul_le hF_le
  have hImage_le : s863MulImage (l := l) T b ⊆
      (s839FractionalLattice (l := l) T b : Set (qVFamTensorBlock T b)) := by
    rintro z ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    exact h x hx y hy
  have hF_le_image : (s839FractionalLattice (l := l) T b :
      Set (qVFamTensorBlock T b)) ⊆ s863MulImage (l := l) T b := by
    intro x hx
    exact ⟨(x, 1), ⟨hx, hone⟩, mul_one x⟩
  unfold S863ProductImageEq
  rw [hFO]
  exact Set.Subset.antisymm hF_le_image hImage_le

#check s1475LocalFractionalSpan_eq_top
#check s1475Q1UFractionalLattice_open
#check s1475Q1URegion_open
#check s1475RootStackEmbedding_isClosedEmbedding
#check s1475Q1URegionMeasurable_actual
#check s1475Q1UImageContainment_iff_region
#check s1475ProductImageEq_of_pointwise_absorption

#print axioms s1475LocalFractionalSpan_eq_top
#print axioms s1475Q1UFractionalLattice_open
#print axioms s1475Q1URegion_open
#print axioms s1475RootStackEmbedding_isClosedEmbedding
#print axioms s1475Q1URegionMeasurable_actual
#print axioms s1475Q1UImageContainment_iff_region
#print axioms s1475ProductImageEq_of_pointwise_absorption

end LeanFormal.IUT.XiFPaper.S1475ReportCExactInputsActual
