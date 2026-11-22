import tmp.sheaf.xif.paper.S1512ProductHaarScalingActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellHaarIndex
import LeanFormal.IUT.ABCBridge.Geometry.RationalCommonPrimeFinrank
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.NumberTheory.Padics.PadicNorm

/-!
# S1520: the actual local completion Haar scaling

S1512 reduced the dependent product character DependentProductScalingChar
to two exact statements:

* S1512LocalCompletionScaling s v, the local statement
  distribHaarChar K_v (p_v^{-1}) = p_v;
* S1512ProductHaarDecomposition s, the product measure decomposition.

This file proves the local statement unconditionally.  The proof does not
assume any measure equality.  It uses the actual finite-dimensional normed
Q_p structure of the completion, obtained from the already constructed
NormalizedCompletion norm through normalizedCompletionHomeomorph:

1. on the syntactic completion type we install the normalized norm,
   scalar action, properness, and topological instances;
2. the prime unit pUnitC is a unit of the completion and the donor
   FinitePadicHaarScaling.measure_prime_smul_finiteDimensional computes
   its additive Haar character as p ^ (-finrank);
3. finrank_completion_rat gives finrank = 1, so the inverse prime has
   character p;
4. the topology equality supplied by normalizedCompletionHomeomorph
   transports the character back to the canonical completion topology.

The only remaining input of the S1512 reduction is the product Haar
decomposition S1512ProductHaarDecomposition, which is not assumed here.
-/

noncomputable section
open MeasureTheory
open scoped Pointwise NNReal ENNReal

namespace LeanFormal.IUT.XiFPaper.S1520LocalCompletionHaarActual

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.S1512ProductHaarScalingActual
open LeanFormal.IUT.XiFPaper.S1502DependentScalingCharActual
open LeanFormal.IUT.XiFPaper.S1422HDDDetActual
open LeanFormal.IUT.XiFPaper.S1402HDDDependentSourceActual

set_option linter.unusedVariables false
set_option linter.defProp false

/-! ## 1. The normalized completion topology on the syntactic completion -/

/-- The normalized (spectral) topology, transported to the syntactic completion
type Completion P. -/
@[reducible] def normTop (P : NumberField.FinitePlace ℚ) :
    TopologicalSpace (Completion P) :=
  inferInstanceAs (TopologicalSpace (NormalizedCompletion P))

@[reducible] def canonicalTop (P : NumberField.FinitePlace ℚ) :
    TopologicalSpace (Completion P) := inferInstance

@[reducible] def normTopAddGroup (P : NumberField.FinitePlace ℚ) :
    @IsTopologicalAddGroup (Completion P) (normTop P) _ :=
  inferInstanceAs (IsTopologicalAddGroup (NormalizedCompletion P))

@[reducible] def normLocCompact (P : NumberField.FinitePlace ℚ) :
    @LocallyCompactSpace (Completion P) (normTop P) :=
  inferInstanceAs (LocallyCompactSpace (NormalizedCompletion P))

@[reducible] def normContSmul (P : NumberField.FinitePlace ℚ) :
    @ContinuousConstSMul (Completion P)ˣ (Completion P) (normTop P) _ :=
  inferInstanceAs (ContinuousConstSMul (NormalizedCompletion P)ˣ (NormalizedCompletion P))

@[reducible] def canonicalTopAddGroup (P : NumberField.FinitePlace ℚ) :
    @IsTopologicalAddGroup (Completion P) (canonicalTop P) _ :=
  inferInstanceAs (IsTopologicalAddGroup (Completion P))

@[reducible] def canonicalLocCompact (P : NumberField.FinitePlace ℚ) :
    @LocallyCompactSpace (Completion P) (canonicalTop P) :=
  (normalizedCompletionHomeomorph P).locallyCompactSpace_iff.mp
    (inferInstance : LocallyCompactSpace (NormalizedCompletion P))

@[reducible] def canonicalContSmul (P : NumberField.FinitePlace ℚ) :
    @ContinuousConstSMul (Completion P)ˣ (Completion P) (canonicalTop P) _ :=
  inferInstanceAs (ContinuousConstSMul (Completion P)ˣ (Completion P))

/-- The normalized completion topology is the canonical completion topology.
This is the actual content of normalizedCompletionHomeomorph. -/
theorem normTop_eq_canonicalTop (P : NumberField.FinitePlace ℚ) :
    normTop P = canonicalTop P := by
  let h := normalizedCompletionHomeomorph P
  have hpt : ∀ x : NormalizedCompletion P, h x = x := by
    intro x
    rw [show h = normalizedCompletionHomeomorph P from rfl,
      normalizedCompletionHomeomorph_apply]
    rfl
  apply TopologicalSpace.ext_iff.mpr
  intro s
  have himg : h '' s = (s : Set (Completion P)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hpt x]
      exact hx
    · intro hy
      exact ⟨y, hy, hpt y⟩
  have hiff := h.isOpen_image (s := s)
  rw [himg] at hiff
  exact hiff.symm

/-- distribHaarChar depends only on the topological-space structure (for a
fixed additive group and distributive action). -/
theorem distribHaarChar_topology_congr {G A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] (t₁ t₂ : TopologicalSpace A)
    [@IsTopologicalAddGroup A t₁ _] [@LocallyCompactSpace A t₁]
    [@ContinuousConstSMul G A t₁ _]
    [@IsTopologicalAddGroup A t₂ _] [@LocallyCompactSpace A t₂]
    [@ContinuousConstSMul G A t₂ _]
    (h : t₁ = t₂) (g : G) :
    @MeasureTheory.distribHaarChar G A _ _ _ t₁ _ _ _ g =
      @MeasureTheory.distribHaarChar G A _ _ _ t₂ _ _ _ g := by
  subst h
  rfl

/-! ## 2. The normalized finite-dimensional structure on the completion -/

section NormalizedContextOnCompletion

variable (P : NumberField.FinitePlace ℚ)

local instance instTopology : TopologicalSpace (Completion P) := normTop P
local instance instUniform : UniformSpace (Completion P) :=
  inferInstanceAs (UniformSpace (NormalizedCompletion P))
local instance instNormedField : NormedField (Completion P) :=
  inferInstanceAs (NormedField (NormalizedCompletion P))
local instance instNormedAlgebra : NormedAlgebra (PadicScalarField P) (Completion P) :=
  inferInstanceAs (NormedAlgebra (PadicScalarField P) (NormalizedCompletion P))
local instance instFiniteDimensional :
    FiniteDimensional (PadicScalarField P) (Completion P) :=
  inferInstanceAs (FiniteDimensional (PadicScalarField P) (NormalizedCompletion P))
local instance instUltra : IsUltrametricDist (Completion P) :=
  inferInstanceAs (IsUltrametricDist (NormalizedCompletion P))
local instance instProper : ProperSpace (Completion P) :=
  inferInstanceAs (ProperSpace (NormalizedCompletion P))
local instance instLocCompact : LocallyCompactSpace (Completion P) :=
  inferInstanceAs (LocallyCompactSpace (NormalizedCompletion P))
local instance instTopAddGroup : IsTopologicalAddGroup (Completion P) :=
  inferInstanceAs (IsTopologicalAddGroup (NormalizedCompletion P))
local instance instContSmul : ContinuousConstSMul (Completion P)ˣ (Completion P) :=
  inferInstanceAs (ContinuousConstSMul (NormalizedCompletion P)ˣ (NormalizedCompletion P))
local instance instMeasurable : MeasurableSpace (Completion P) :=
  borel (Completion P)
local instance instBorel : BorelSpace (Completion P) := ⟨rfl⟩

/-- The rational-prime scalar unit in the completion, using the normalized
Q_p-algebra structure. -/
noncomputable def pUnitC : (Completion P)ˣ :=
  Units.mk0
    (algebraMap (PadicScalarField P) (Completion P)
      ((completionRationalPrime P).val : PadicScalarField P))
    (by
      have hnorm :
          ‖algebraMap (PadicScalarField P) (Completion P)
              ((completionRationalPrime P).val : PadicScalarField P)‖ =
            ‖((completionRationalPrime P).val : PadicScalarField P)‖ := by
        simpa using norm_algebraMap' (Completion P)
          ((completionRationalPrime P).val : PadicScalarField P)
      rw [← norm_ne_zero_iff, hnorm, Padic.norm_p]
      exact inv_ne_zero
        (Nat.cast_ne_zero.mpr
          (Fact.out : Nat.Prime (completionRationalPrime P).val).ne_zero))

theorem pUnitC_coe :
    (pUnitC P : Completion P) =
      algebraMap (PadicScalarField P) (Completion P)
        ((completionRationalPrime P).val : PadicScalarField P) := rfl

/-- Actual character of the prime unit: the inverse finrank-th power of p,
obtained from the actual finite-dimensional Haar scaling donor. -/
theorem distribHaarChar_pUnitC :
    distribHaarChar (Completion P) (pUnitC P) =
      (((completionRationalPrime P).val : ℝ≥0) ^
        Module.finrank (PadicScalarField P) (Completion P))⁻¹ := by
  let μ : Measure (Completion P) := Measure.addHaar
  let H : Set (Completion P) := Integers (Completion P)
  letI : Measure.IsAddHaarMeasure μ := Measure.isAddHaarMeasure_addHaarMeasure _
  have hmass :=
    LeanFormal.IUT.LocalFieldLogarithm.measure_localIntegers_pos_lt_top
      (K := Completion P) μ
  have hpos : 0 < μ H := hmass.1
  have hfin : μ H < ⊤ := hmass.2
  apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := H)
    (g := pUnitC P)
    (r := (((completionRationalPrime P).val : ℝ≥0) ^
      Module.finrank (PadicScalarField P) (Completion P))⁻¹) hpos.ne' hfin.ne
  have hact : pUnitC P • H =
      (((completionRationalPrime P).val : PadicScalarField P) • H) := by
    ext x
    simp only [Set.mem_smul_set, Units.smul_def, pUnitC_coe, Algebra.smul_def,
      Algebra.algebraMap_self_apply]
  have hscale :=
    LeanFormal.IUT.FinitePadicHaarScaling.measure_prime_smul_finiteDimensional
      (p := (completionRationalPrime P).val) (M := Completion P) μ H
  rw [hact, hscale]
  congr 1
  rw [ENNReal.coe_inv
      (pow_ne_zero _ (by
        exact_mod_cast (Fact.out : Nat.Prime
          (completionRationalPrime P).val).ne_zero)),
    ENNReal.coe_pow, ENNReal.coe_natCast]

end NormalizedContextOnCompletion

/-! ## 3. Transport to the canonical completion topology -/

/-- The prime-unit character at the canonical completion topology. -/
theorem distribHaarChar_pUnitC_canonical (P : NumberField.FinitePlace ℚ) :
    @MeasureTheory.distribHaarChar (Completion P)ˣ (Completion P) _ _ _
      (canonicalTop P) _ _ _ (pUnitC P) =
      (((completionRationalPrime P).val : ℝ≥0) ^
        Module.finrank (PadicScalarField P) (Completion P))⁻¹ := by
  let hbridge := @distribHaarChar_topology_congr (Completion P)ˣ (Completion P)
    _ _ _ (normTop P) (canonicalTop P)
    (normTopAddGroup P) (normLocCompact P) (normContSmul P)
    (canonicalTopAddGroup P) (canonicalLocCompact P) (canonicalContSmul P)
    (normTop_eq_canonicalTop P) (pUnitC P)
  rw [← hbridge]
  exact distribHaarChar_pUnitC P

theorem finrank_completion_eq_one (P : NumberField.FinitePlace ℚ) :
    Module.finrank (PadicScalarField P) (Completion P) = 1 :=
  finrank_completion_rat P

/-- The local distribHaarChar law for the inverse prime unit at the canonical
completion topology. -/
theorem distribHaarChar_pUnitC_inv_canonical (P : NumberField.FinitePlace ℚ) :
    @MeasureTheory.distribHaarChar (Completion P)ˣ (Completion P) _ _ _
      (canonicalTop P) _ _ _ ((pUnitC P)⁻¹) =
      ((completionRationalPrime P).val : ℝ≥0) := by
  rw [map_inv, distribHaarChar_pUnitC_canonical, finrank_completion_eq_one]
  rw [pow_one, inv_inv]

theorem dependentPrimeInverseUnit_eq_inv_pUnitC
    (s : Finset (NumberField.FinitePlace ℚ)) (v : {v // v ∈ s}) :
    (dependentPrimeInverseUnit s v) = (pUnitC v.1)⁻¹ := by
  apply Units.ext
  simp [dependentPrimeInverseUnit, dependentPlacePrime, pUnitC, map_natCast]

/-- S1520 main theorem. The local completion Haar character is exactly the
residue characteristic: unconditionally, without assuming any product measure
decomposition. -/
theorem s1520LocalCompletionScaling
    (s : Finset (NumberField.FinitePlace ℚ)) (v : {v // v ∈ s}) :
    S1512LocalCompletionScaling s v := by
  unfold S1512LocalCompletionScaling S1502LocalPrimeScaling
  rw [dependentPrimeInverseUnit_eq_inv_pUnitC]
  have h := distribHaarChar_pUnitC_inv_canonical v.1
  simpa [canonicalTop, dependentPlacePrime, S1402DependentE] using
    congrArg (fun r : ℝ≥0 => (r : ENNReal)) h

/-- The exact first missing measure lemma named by S1512, now proved: it is
the local scaling statement itself. -/
theorem s1520FirstMissingMeasureLemma
    (s : Finset (NumberField.FinitePlace ℚ)) (v : {v // v ∈ s}) :
    S1512FirstMissingMeasureLemma s v :=
  s1520LocalCompletionScaling s v

/-- The exact residual input of the S1512 reduction after this file: the
product Haar decomposition.  It is not assumed or proved in S1520. -/
def S1520RemainingProductHaarDecomposition
    (s : Finset (NumberField.FinitePlace ℚ)) : Prop :=
  S1512ProductHaarDecomposition s

end LeanFormal.IUT.XiFPaper.S1520LocalCompletionHaarActual

/-! ## 4. Axiom audit -/

#print axioms LeanFormal.IUT.XiFPaper.S1520LocalCompletionHaarActual.s1520LocalCompletionScaling
#print axioms LeanFormal.IUT.XiFPaper.S1520LocalCompletionHaarActual.distribHaarChar_pUnitC_inv_canonical
#print axioms LeanFormal.IUT.XiFPaper.S1520LocalCompletionHaarActual.finrank_completion_eq_one

end
