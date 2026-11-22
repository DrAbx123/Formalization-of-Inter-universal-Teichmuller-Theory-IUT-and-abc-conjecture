/-
  # The terminal-stage normalized valuation and the global finite-place exponent

  Task task-30 of the Group-1 split.  This module closes residual gap (3) of
  Example36SourceTheaterCarrier.lean: at the concrete Gaussian place it
  identifies the terminal-stage (bottom-stage) normalized additive valuation
  of the stage-model divisor monoid with the global classical finite-place
  valuation exponent finitePlaceValueExponent on global units, through the
  actual completion valuation Valued.v.

  ## Mathematical content

  * bottomStageUnitEquiv / baseToBottomUnit / bottomToBaseUnit: the unit
    equivalence between the actual completion Base p (the bottom stage field
    of the finite Galois reconstruction) and the units of the bottom stage of
    StageIndex p, induced by the Mathlib intermediate-field bottom equivalence
    (IntermediateField.botEquiv).  The underlying element of a completion unit
    is proved to be the image under the actual algebra map into the algebraic
    closure.
  * stageNormalizedAdditiveValuation_surjective: the normalized additive
    valuation of every finite Galois stage is surjective onto Z.  The proof
    uses only that the value-group normalization iso is bijective and that
    ValuativeRel.valuation is surjective onto the value group; no formula for
    the normalization iso is assumed.
  * stageNormalizedAdditiveValuation_bot_nonneg_iff: the nonnegativity set of
    the bottom-stage normalized valuation equals the nonnegativity set of the
    completion exponent of the corresponding completion unit.  This is proved
    through the existing base-integrality characterization of the stage
    valuation (stageNormalizedAdditiveValuation_nonnegative_iff_baseIsIntegral,
    stageIsIntegral_iff_norm_le_one), the isometry of the bottom stage into the
    algebraic closure (norm_algebraMap'), and the base-completion valuation
    integrality criterion (baseValuation_le_one_iff_norm, plus the equivalence
    of Valued.v with the canonical valuative-relation valuation).
  * addMonoidHom_eq_of_surjective_of_nonneg_iff: an abstract rigidity lemma.
    Two surjective additive homomorphisms from an abelian group to Z with the
    same nonnegativity set are equal.  Consequently the normalization of the
    stage valuation is uniquely determined: it is not an extra choice.
  * stageNormalizedAdditiveValuation_bot_eq_completionExponent: the terminal
    stage normalized additive valuation equals the completion exponent
    homomorphism, as homomorphisms.
  * stageNormalizedAdditiveValuation_bot_globalUnit: the integer coordinate
    identity on global units:
      stageNormalizedAdditiveValuation p bottom (image of f)
        = finitePlaceValueExponent (underlyingPrime p) f.
  * stageValueGroupWithZeroIsoInt_bot_globalUnit: the value-group form: the
    normalized value-group image of the completion element of f is exactly the
    actual completion value Valued.v of f.
  * stageNormalizedAdditiveValuation_bot_realified and
    stageNormalizedAdditiveValuation_bot_logVolume: the realified forms, both
    as the integer coordinate cast to R and as the normalized local log-volume
    degree -nu * log #(O / v) of the finite-place degree kernel
    (finitePlaceUnitValueKernel).
  * globalModelDivisor_finite_coordinate_eq_stageNormalizedValuation,
    sourceModelPrincipalDivisor_finite_coordinate_eq_stageNormalizedValuation:
    the finite coordinate of the Example 3.6 model-Frobenioid divisor map and
    of the principal-divisor family are the terminal-stage normalized additive
    valuation of the embedded global unit.

  ## Normalization: no identity normalization is assumed

  The stage normalization iso stageValueGroupWithZeroIsoInt is produced by
  Mathlib as Nonempty.some of the uniqueness statement for order isomorphisms
  of the discrete value group with Z^0.  Its concrete value is never used: the
  only properties used below are bijectivity and order preservation (through
  the two existing stage-integrality lemmas).  The rigidity lemma shows that
  any additive homomorphism with the same surjectivity and the same
  nonnegativity set is equal to it; hence the identification does not depend on
  the chosen normalization iso, and no normalization input remains open for the
  integer coordinate.  The sign convention is fixed by the classical exponent
  completionValuationExponent (positive on a uniformizer, matching
  finitePlaceValueExponent), not by an identity normalization.  The real
  absolute-value normalization (the value of the residue-field logarithm) is
  supplied by the existing finite-place degree kernel, not by the stage data;
  the realified statement records this explicitly.

  ## What is NOT proved

  This is the terminal-stage value-coordinate bridge only.  No theta-pilot,
  q-pilot, Tate-uniformization, Hodge-Arakelov, or source-identification claim
  is made; no map from the local value group back to global units is
  constructed (none exists in the source; only the global-to-local direction is
  formalized).  The rest of the stage model (higher stages, ramification
  transitions) is not re-proved here; the transition compatibility of the
  normalized valuation remains the existing
  stageNormalizedAdditiveValuation_transition.

  Source correspondence: IUT III, Example 3.6 and the local dictionary at a
  finite place; IUT I, Definition 5.2(v) (finite Galois stages of the local
  reconstruction) and Remark 3.9.4 (value groups and log-shells).
-/

import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceTheaterCarrier
import LeanFormal.IUT.IUTII.Frobenioid.Example36PrimeStripBridge
import Iut.Foundations.SourceFiniteStageValuationDivisor
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36
namespace StageNormalizationBridge

open LeanFormal.IUT
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open Iut
open Iut.SourceFinitePlaceReconstruction
open IsDedekindDomain
open scoped WithZero

local instance gaussianPolynomialIrreducibleFactStageNorm :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance fivePrimeFactStageNorm : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

local instance primeFactStageNorm (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  l.factPrime

noncomputable section

/-! ## 1. The bottom stage and its unit equivalence with the completion -/

/-- The bottom stage of the finite Galois reconstruction at a finite place, as
the bottom intermediate field of the completion in its algebraic closure.  It
is definitionally the field at the terminal object of the stage base category
(StageBase = StageIndex^op has terminal object op bottom). -/
abbrev bottomStage (p : NumberField.FinitePlace GaussianField) : Type :=
  ↥(⊥ : IntermediateField (Base p) (Closure p))

/-- The unit equivalence between the actual completion Base p and the bottom
stage of the finite Galois reconstruction, induced by the Mathlib
intermediate-field bottom equivalence and the unit functor. -/
noncomputable def bottomStageUnitEquiv
    (p : NumberField.FinitePlace GaussianField) :
    (Base p)ˣ ≃* (↥(⊥ : StageIndex p).toIntermediateField)ˣ :=
  Units.mapEquiv (IntermediateField.botEquiv (Base p) (Closure p)).symm.toRingEquiv.toMulEquiv

/-- A completion unit regarded as a unit of the bottom stage. -/
noncomputable def baseToBottomUnit (p : NumberField.FinitePlace GaussianField)
    (y : (Base p)ˣ) : (↥(⊥ : StageIndex p).toIntermediateField)ˣ :=
  bottomStageUnitEquiv p y

/-- A bottom-stage unit regarded as a completion unit. -/
noncomputable def bottomToBaseUnit (p : NumberField.FinitePlace GaussianField)
    (u : (↥(⊥ : StageIndex p).toIntermediateField)ˣ) : (Base p)ˣ :=
  (bottomStageUnitEquiv p).symm u

theorem bottomToBaseUnit_baseToBottomUnit
    (p : NumberField.FinitePlace GaussianField) (y : (Base p)ˣ) :
    bottomToBaseUnit p (baseToBottomUnit p y) = y := by
  unfold bottomToBaseUnit baseToBottomUnit
  exact (bottomStageUnitEquiv p).symm_apply_apply y

theorem baseToBottomUnit_bottomToBaseUnit
    (p : NumberField.FinitePlace GaussianField)
    (u : (↥(⊥ : StageIndex p).toIntermediateField)ˣ) :
    baseToBottomUnit p (bottomToBaseUnit p u) = u := by
  unfold bottomToBaseUnit baseToBottomUnit
  exact (bottomStageUnitEquiv p).apply_symm_apply u

/-- The underlying completion element of a bottom-stage unit is the actual
algebra-map image of the completion unit in the algebraic closure. -/
theorem baseToBottomUnit_val_coe (p : NumberField.FinitePlace GaussianField)
    (y : (Base p)ˣ) :
    (((baseToBottomUnit p y : (↥(⊥ : StageIndex p).toIntermediateField)ˣ) :
        ↥(⊥ : StageIndex p).toIntermediateField) : Closure p) =
      algebraMap (Base p) (Closure p) (y : Base p) := by
  have hval : ((baseToBottomUnit p y : (↥(⊥ : StageIndex p).toIntermediateField)ˣ) :
      ↥(⊥ : StageIndex p).toIntermediateField) =
      (IntermediateField.botEquiv (Base p) (Closure p)).symm (y : Base p) := by
    unfold baseToBottomUnit bottomStageUnitEquiv
    rfl
  rw [hval]
  have hbot : (IntermediateField.botEquiv (Base p) (Closure p)).symm (y : Base p) =
      algebraMap (Base p) (↥(⊥ : IntermediateField (Base p) (Closure p)))
        (y : Base p) :=
    IntermediateField.botEquiv_symm (y : Base p)
  rw [hbot]
  exact IsScalarTower.algebraMap_apply (Base p)
    (↥(⊥ : IntermediateField (Base p) (Closure p))) (Closure p) (y : Base p)

/-- The embedding of the completion into its algebraic closure is isometric
for the spectral norm. -/
theorem base_algebraMap_closure_norm (p : NumberField.FinitePlace GaussianField)
    (y : Base p) : ‖algebraMap (Base p) (Closure p) y‖ = ‖y‖ := by
  rw [NormedAlgebra.norm_eq_spectralNorm (K := Base p)]
  exact spectralNorm_extends y

/-- The norm of a bottom-stage unit is the norm of the corresponding
completion unit: the bottom stage is isometric to the completion. -/
theorem baseToBottomUnit_norm (p : NumberField.FinitePlace GaussianField)
    (y : (Base p)ˣ) :
    ‖((baseToBottomUnit p y : (↥(⊥ : StageIndex p).toIntermediateField)ˣ) :
        ↥(⊥ : StageIndex p).toIntermediateField)‖ = ‖(y : Base p)‖ := by
  calc ‖((baseToBottomUnit p y : (↥(⊥ : StageIndex p).toIntermediateField)ˣ) :
        ↥(⊥ : StageIndex p).toIntermediateField)‖
      = ‖((((baseToBottomUnit p y : (↥(⊥ : StageIndex p).toIntermediateField)ˣ) :
          ↥(⊥ : StageIndex p).toIntermediateField) : Closure p))‖ := rfl
    _ = ‖algebraMap (Base p) (Closure p) (y : Base p)‖ :=
        congrArg norm (baseToBottomUnit_val_coe p y)
    _ = ‖(y : Base p)‖ := base_algebraMap_closure_norm p (y : Base p)

/-- The value-group normalization isomorphism of every stage sends zero to
zero (zero is the bottom of the discrete value group, and
stageValueGroupWithZeroIsoInt is an order isomorphism). -/
theorem stageValueGroupWithZeroIsoInt_zero
    (p : NumberField.FinitePlace GaussianField) (stage : StageIndex p) :
    stageValueGroupWithZeroIsoInt p stage 0 = 0 :=
  (stageValueGroupWithZeroIsoInt p stage).toOrderIso.map_bot

/-- The inverse normalization isomorphism sends zero to zero. -/
theorem stageValueGroupWithZeroIsoInt_symm_zero
    (p : NumberField.FinitePlace GaussianField) (stage : StageIndex p) :
    (stageValueGroupWithZeroIsoInt p stage).symm 0 = 0 :=
  (stageValueGroupWithZeroIsoInt p stage).symm.toOrderIso.map_bot

/-! ## 2. Surjectivity of the stage normalized valuation -/

/-- The normalized additive valuation of every finite Galois stage is
surjective onto Z.  Only bijectivity of the value-group normalization and
surjectivity of the canonical valuation are used; the concrete normalization
formula is not needed. -/
theorem stageNormalizedAdditiveValuation_surjective
    (p : NumberField.FinitePlace GaussianField) (stage : StageIndex p) :
    Function.Surjective (stageNormalizedAdditiveValuation p stage) := by
  intro n
  let iso := stageValueGroupWithZeroIsoInt p stage
  let gamma : ValuativeRel.ValueGroupWithZero ↥stage.toIntermediateField :=
    iso.symm (WithZero.exp (-n))
  have hgamma_ne : gamma ≠ 0 := by
    intro hzero
    have hmap : iso gamma = WithZero.exp (-n) :=
      OrderMonoidIso.apply_symm_apply iso (WithZero.exp (-n))
    rw [hzero, stageValueGroupWithZeroIsoInt_zero] at hmap
    exact WithZero.exp_ne_zero hmap.symm
  obtain ⟨x, hx⟩ :=
    ValuativeRel.valuation_surjective (K := ↥stage.toIntermediateField) gamma
  have hx_ne : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact hgamma_ne hx.symm
  refine ⟨Additive.ofMul (Units.mk0 x hx_ne), ?_⟩
  change - WithZero.log (iso (ValuativeRel.valuation ↥stage.toIntermediateField x)) = n
  rw [hx, OrderMonoidIso.apply_symm_apply, WithZero.log_exp]
  ring


/-! ## 3. The sign comparison with the completion exponent -/

/-- The actual completion valuation is at most one exactly when the completion
norm is at most one: on the v-adic completion the valued valuation Valued.v is
equivalent to the canonical valuative-relation valuation of the normed field. -/
theorem valued_v_le_one_iff_norm (p : NumberField.FinitePlace GaussianField)
    (b : Base p) : Valued.v b ≤ 1 ↔ ‖b‖ ≤ 1 := by
  let baseValuation : Valuation (Base p) ℤᵐ⁰ := Valued.v
  letI : baseValuation.Compatible := Valuation.Compatible.ofValuation baseValuation
  exact (ValuativeRel.isEquiv baseValuation
    (ValuativeRel.valuation (Base p))).le_one_iff_le_one.trans
    (baseValuation_le_one_iff_norm p b)

/-- **Sign comparison.**  The bottom-stage normalized additive valuation is
nonnegative exactly when the completion exponent of the corresponding
completion unit is nonnegative.

The chain is: stage nonnegativity is integrality over the base valuation ring of
the completion (existing lemma), integrality is the stage norm being at most
one (existing lemma), the bottom stage is isometric to the completion
(baseToBottomUnit_norm), and the completion valuation integrality is the
classical exponent nonnegativity (existing lemma). -/
theorem stageNormalizedAdditiveValuation_bot_nonneg_iff
    (p : NumberField.FinitePlace GaussianField)
    (u : (↥(⊥ : StageIndex p).toIntermediateField)ˣ) :
    0 ≤ stageNormalizedAdditiveValuation p (⊥ : StageIndex p) (Additive.ofMul u) ↔
      0 ≤ completionValuationExponent (underlyingPrime p) (bottomToBaseUnit p u) := by
  have hintegral :
      0 ≤ stageNormalizedAdditiveValuation p (⊥ : StageIndex p) (Additive.ofMul u) ↔
        IsIntegral (A := Closure p) ↥(ValuativeRel.valuation (Base p)).integer
          ((u : ↥(⊥ : StageIndex p).toIntermediateField) : Closure p) :=
    stageNormalizedAdditiveValuation_nonnegative_iff_baseIsIntegral p
      (⊥ : StageIndex p) u
  have hnorm_integral :
      IsIntegral (A := Closure p) ↥(ValuativeRel.valuation (Base p)).integer
          ((u : ↥(⊥ : StageIndex p).toIntermediateField) : Closure p) ↔
        ‖u.1‖ ≤ 1 := by
    rw [stageIsIntegral_closure_iff_valuation_le_one]
    exact stageValuation_le_one_iff_norm p (⊥ : StageIndex p) u.1
  have hnorm : ‖u.1‖ = ‖(bottomToBaseUnit p u : Base p)‖ := by
    conv_lhs => rw [show u = baseToBottomUnit p (bottomToBaseUnit p u) from
      (baseToBottomUnit_bottomToBaseUnit p u).symm]
    exact baseToBottomUnit_norm p (bottomToBaseUnit p u)
  calc 0 ≤ stageNormalizedAdditiveValuation p (⊥ : StageIndex p) (Additive.ofMul u)
      ↔ IsIntegral (A := Closure p) ↥(ValuativeRel.valuation (Base p)).integer
          ((u : ↥(⊥ : StageIndex p).toIntermediateField) : Closure p) := hintegral
    _ ↔ ‖u.1‖ ≤ 1 := hnorm_integral
    _ ↔ ‖(bottomToBaseUnit p u : Base p)‖ ≤ 1 := by rw [hnorm]
    _ ↔ Valued.v (bottomToBaseUnit p u : Base p) ≤ 1 :=
        (valued_v_le_one_iff_norm p (bottomToBaseUnit p u : Base p)).symm
    _ ↔ 0 ≤ completionValuationExponent (underlyingPrime p) (bottomToBaseUnit p u) :=
        valuation_le_one_iff_zero_le_exponent (K := GaussianField) (underlyingPrime p) (bottomToBaseUnit p u)

/-! ## 4. Rigidity of the normalization -/

/-- **Rigidity lemma.**  Two surjective additive homomorphisms from an abelian
group to the integers with the same nonnegativity set coincide.

Proof: pick p with f p = 1 and let k = g p.  For every y, applying the sign
equivalence to y - f(y) * p and to its negation shows g y = f(y) * k.
Surjectivity of g forces k = +-1, and the sign equivalence at p (where
f p = 1 > 0) forces k = 1. -/
theorem addMonoidHom_eq_of_surjective_of_nonneg_iff {G : Type*} [AddCommGroup G]
    (f g : G →+ ℤ) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hsign : ∀ x, 0 ≤ f x ↔ 0 ≤ g x) : f = g := by
  obtain ⟨p, hp⟩ := hf 1
  have hgp_nonneg : 0 ≤ g p := (hsign p).mp (by rw [hp]; norm_num)
  have hfactor : ∀ y, g y = f y * g p := by
    intro y
    have hkernel : f (y - (f y) • p) = 0 := by
      rw [map_sub, map_zsmul, hp]
      simp
    have hnonneg : 0 ≤ g (y - (f y) • p) :=
      (hsign (y - (f y) • p)).mp (by rw [hkernel])
    have hnonpos : g (y - (f y) • p) ≤ 0 := by
      have hneg : 0 ≤ g (-(y - (f y) • p)) := by
        apply (hsign (-(y - (f y) • p))).mp
        rw [map_neg, hkernel, neg_zero]
      rw [map_neg] at hneg
      linarith
    have hzero : g (y - (f y) • p) = 0 := le_antisymm hnonpos hnonneg
    have hexp : g (y - (f y) • p) = g y - (f y) * g p := by
      rw [map_sub, map_zsmul]
      simp
    linarith
  obtain ⟨y0, hy0⟩ := hg 1
  have hk : g p = 1 := by
    have hprod : f y0 * g p = 1 := by rw [← hfactor y0, hy0]
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hprod with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact h2
    · omega
  ext y
  rw [hfactor y, hk, mul_one]

/-- **Normalization invariance.**  Any additive homomorphism on the bottom-stage
units which is surjective onto the integers and has the same nonnegativity set
as the stage normalized valuation is equal to it.  Hence the normalization of
the stage valuation is uniquely determined by the integrality data; the choice
inside the value-group normalization isomorphism does not affect the integer
coordinate. -/
theorem stageNormalizedAdditiveValuation_bot_unique
    (p : NumberField.FinitePlace GaussianField)
    (w : Additive (↥(⊥ : StageIndex p).toIntermediateField)ˣ →+ ℤ)
    (hw : Function.Surjective w)
    (hsign : ∀ u, 0 ≤ w u ↔
      0 ≤ stageNormalizedAdditiveValuation p (⊥ : StageIndex p) u) :
    w = stageNormalizedAdditiveValuation p (⊥ : StageIndex p) :=
  (addMonoidHom_eq_of_surjective_of_nonneg_iff w
    (stageNormalizedAdditiveValuation p (⊥ : StageIndex p)) hw
    (stageNormalizedAdditiveValuation_surjective p (⊥ : StageIndex p))
    hsign)

/-! ## 5. The completion exponent homomorphism and the terminal-stage identity -/

/-- The completion exponent of the completion unit corresponding to a
bottom-stage unit, as an additive homomorphism on the bottom-stage units.  It is
the composition of the unit equivalence with the actual completion exponent
monoid homomorphism, so no normalization is inserted here. -/
noncomputable def bottomStageCompletionValuation
    (p : NumberField.FinitePlace GaussianField) :
    Additive (↥(⊥ : StageIndex p).toIntermediateField)ˣ →+ ℤ :=
  ((completionValuationExponentMonoidHom
      (K := GaussianField) (underlyingPrime p)).toAdditive).comp
    ((bottomStageUnitEquiv p).symm.toMonoidHom.toAdditive)

theorem bottomStageCompletionValuation_surjective
    (p : NumberField.FinitePlace GaussianField) :
    Function.Surjective (bottomStageCompletionValuation p) := by
  intro n
  obtain ⟨b, hb⟩ := completionValuationExponent_surjective (K := GaussianField) (underlyingPrime p) n
  refine ⟨Additive.ofMul (baseToBottomUnit p b), ?_⟩
  show completionValuationExponent (underlyingPrime p)
    (bottomToBaseUnit p (baseToBottomUnit p b)) = n
  rw [bottomToBaseUnit_baseToBottomUnit, hb]

/-- **Terminal-stage identity of homomorphisms.**  The terminal-stage (bottom
stage) normalized additive valuation of the stage model equals the completion
exponent homomorphism on the corresponding completion units. -/
theorem stageNormalizedAdditiveValuation_bot_eq_bottomStageCompletionValuation
    (p : NumberField.FinitePlace GaussianField) :
    stageNormalizedAdditiveValuation p (⊥ : StageIndex p) =
      bottomStageCompletionValuation p := by
  apply addMonoidHom_eq_of_surjective_of_nonneg_iff
  · exact stageNormalizedAdditiveValuation_surjective p (⊥ : StageIndex p)
  · exact bottomStageCompletionValuation_surjective p
  · intro u
    have h := stageNormalizedAdditiveValuation_bot_nonneg_iff p (Additive.toMul u)
    change 0 ≤ stageNormalizedAdditiveValuation p (⊥ : StageIndex p) u ↔
      0 ≤ completionValuationExponent (underlyingPrime p) (bottomToBaseUnit p u.toMul)
    exact h

/-! ## 6. The identity on global units -/

/-- The global unit of the Gaussian field, embedded in the actual completion
Base p at the finite place p. -/
noncomputable def globalCompletionUnit (p : NumberField.FinitePlace GaussianField)
    (f : GaussianFieldˣ) : (Base p)ˣ :=
  Units.map (algebraMap GaussianField (Base p)).toMonoidHom f

/-- The global unit embedded into the bottom-stage units through the actual
completion. -/
noncomputable def globalUnitToBottomUnit
    (p : NumberField.FinitePlace GaussianField) (f : GaussianFieldˣ) :
    (↥(⊥ : StageIndex p).toIntermediateField)ˣ :=
  baseToBottomUnit p (globalCompletionUnit p f)

theorem globalUnitToBottomUnit_eq (p : NumberField.FinitePlace GaussianField)
    (f : GaussianFieldˣ) :
    globalUnitToBottomUnit p f = baseToBottomUnit p (globalCompletionUnit p f) :=
  rfl

theorem bottomToBaseUnit_globalUnitToBottomUnit
    (p : NumberField.FinitePlace GaussianField) (f : GaussianFieldˣ) :
    bottomToBaseUnit p (globalUnitToBottomUnit p f) = globalCompletionUnit p f :=
  bottomToBaseUnit_baseToBottomUnit p (globalCompletionUnit p f)

/-- **The terminal-stage normalized valuation of a global unit is the global
classical finite-place valuation exponent.** -/
theorem stageNormalizedAdditiveValuation_bot_globalUnit
    (p : NumberField.FinitePlace GaussianField) (f : GaussianFieldˣ) :
    stageNormalizedAdditiveValuation p (⊥ : StageIndex p)
        (Additive.ofMul (globalUnitToBottomUnit p f)) =
      finitePlaceValueExponent (underlyingPrime p) f := by
  rw [stageNormalizedAdditiveValuation_bot_eq_bottomStageCompletionValuation]
  change completionValuationExponent (underlyingPrime p)
      (bottomToBaseUnit p (Additive.toMul
        (Additive.ofMul (globalUnitToBottomUnit p f)))) =
    finitePlaceValueExponent (underlyingPrime p) f
  rw [show Additive.toMul (Additive.ofMul (globalUnitToBottomUnit p f)) =
      globalUnitToBottomUnit p f from rfl]
  rw [bottomToBaseUnit_globalUnitToBottomUnit]
  have h := finitePlaceGlobalUnitValue_exponent (underlyingPrime p) f
  simpa [finitePlaceGlobalUnitValue, globalCompletionUnit] using h

/-! ## 7. Value-group and realified forms -/

/-- **Value-group form.**  The normalized value-group image of the completion
element of a global unit is exactly the actual completion value Valued.v of
that unit.  This is the equality of value-group coordinates before taking the
integer logarithm. -/
theorem stageValueGroupWithZeroIsoInt_bot_globalUnit
    (p : NumberField.FinitePlace GaussianField) (f : GaussianFieldˣ) :
    stageValueGroupWithZeroIsoInt p (⊥ : StageIndex p)
        (ValuativeRel.valuation (↥(⊥ : StageIndex p).toIntermediateField)
          ((globalUnitToBottomUnit p f :
            (↥(⊥ : StageIndex p).toIntermediateField)ˣ) :
            ↥(⊥ : StageIndex p).toIntermediateField)) =
      Valued.v ((globalCompletionUnit p f : (Base p)ˣ) : Base p) := by
  let iso := stageValueGroupWithZeroIsoInt p (⊥ : StageIndex p)
  let unit := (globalUnitToBottomUnit p f : (↥(⊥ : StageIndex p).toIntermediateField)ˣ)
  let value := ValuativeRel.valuation (↥(⊥ : StageIndex p).toIntermediateField)
    (unit : ↥(⊥ : StageIndex p).toIntermediateField)
  have hvalue_ne : value ≠ 0 :=
    (Valuation.ne_zero_iff (ValuativeRel.valuation
      (↥(⊥ : StageIndex p).toIntermediateField))).2 (Units.ne_zero unit)
  have hiso_ne : iso value ≠ 0 := by
    intro hzero
    have hzero' : value = 0 := by
      rw [← OrderMonoidIso.symm_apply_apply iso value, hzero,
        stageValueGroupWithZeroIsoInt_symm_zero]
    exact hvalue_ne hzero'
  have hvalued_ne : Valued.v ((globalCompletionUnit p f : (Base p)ˣ) : Base p) ≠ 0 :=
    (Valuation.ne_zero_iff (Valued.v : Valuation (Base p) ℤᵐ⁰)).2
      (Units.ne_zero (globalCompletionUnit p f))
  have hlog_iso : WithZero.log (iso value) =
      - finitePlaceValueExponent (underlyingPrime p) f := by
    have hstage := stageNormalizedAdditiveValuation_bot_globalUnit p f
    have hdef : stageNormalizedAdditiveValuation p (⊥ : StageIndex p)
        (Additive.ofMul (globalUnitToBottomUnit p f)) = - WithZero.log (iso value) :=
      rfl
    linarith
  have hlog_valued : WithZero.log
      (Valued.v ((globalCompletionUnit p f : (Base p)ˣ) : Base p)) =
      - finitePlaceValueExponent (underlyingPrime p) f := by
    have hvalue := completionValuationExponent_eq_neg_log (K := GaussianField)
      (underlyingPrime p) (globalCompletionUnit p f)
    have hexponent := finitePlaceGlobalUnitValue_exponent (underlyingPrime p) f
    have hexponent' : completionValuationExponent (underlyingPrime p)
        (globalCompletionUnit p f) =
        finitePlaceValueExponent (underlyingPrime p) f := by
      simpa [finitePlaceGlobalUnitValue, globalCompletionUnit] using hexponent
    linarith
  rw [← WithZero.exp_log hiso_ne, ← WithZero.exp_log hvalued_ne,
    hlog_iso, hlog_valued]

/-- **Realified form (integer cast).**  The real-valued additive coordinate of
the terminal-stage normalized valuation of a global unit is the global
finite-place exponent cast to the reals. -/
theorem stageNormalizedAdditiveValuation_bot_realified
    (p : NumberField.FinitePlace GaussianField) (f : GaussianFieldˣ) :
    ((stageNormalizedAdditiveValuation p (⊥ : StageIndex p)
        (Additive.ofMul (globalUnitToBottomUnit p f)) : ℤ) : ℝ) =
      (finitePlaceValueExponent (underlyingPrime p) f : ℝ) := by
  rw [stageNormalizedAdditiveValuation_bot_globalUnit]

/-- **Realified form (normalized log-volume).**  The realified degree of the
terminal-stage normalized valuation of a global unit, read against the actual
residue-field logarithm, is the realification of the finite-place unit value
kernel at the same place.  This is the form consumed by the finite-place degree
kernel. -/
theorem stageNormalizedAdditiveValuation_bot_logVolume
    (p : NumberField.FinitePlace GaussianField) (f : GaussianFieldˣ) :
    -((stageNormalizedAdditiveValuation p (⊥ : StageIndex p)
        (Additive.ofMul (globalUnitToBottomUnit p f)) : ℤ) : ℝ) *
        Real.log ((finitePlaceResidueCardinality
          (underlyingPrime p) : ℕ) : ℝ) =
      (finitePlaceUnitValueKernel (underlyingPrime p)).realification
        (finitePlaceGlobalUnitValue (underlyingPrime p) f) := by
  rw [stageNormalizedAdditiveValuation_bot_globalUnit,
    finitePlaceUnitValueKernel_realification, finitePlaceGlobalUnitValue_exponent]

/-! ## 8. The terminal-stage divisor coordinates of the stage model -/

/-- The stage-model divisor coordinate of the terminal stage on a global unit
is the integer-to-stage-divisor image of the normalized valuation; this is the
definitional unfolding of the stage-model divisor map at the terminal object of
the stage base category. -/
theorem stageModel_divisor_terminal_globalUnit
    (f : GaussianFieldˣ) :
    (stageModelInput concretePlace).divisor
        (Opposite.op (⊥ : StageIndex concretePlace))
        (Additive.ofMul (globalUnitToBottomUnit concretePlace f)) =
      intToStageDivisorGrothendieck
        (stageNormalizedAdditiveValuation concretePlace
          (⊥ : StageIndex concretePlace)
          (Additive.ofMul (globalUnitToBottomUnit concretePlace f))) :=
  rfl

/-- **Terminal-stage divisor coordinate on global units.**  The groupified
divisor coordinate of the stage-model divisor monoid at the terminal stage is
the global classical finite-place valuation exponent. -/
theorem stageModel_divisor_terminal_globalUnit_coordinate
    (f : GaussianFieldˣ) :
    stageDivisorGrothendieckEquivInt
        ((stageModelInput concretePlace).divisor
          (Opposite.op (⊥ : StageIndex concretePlace))
          (Additive.ofMul (globalUnitToBottomUnit concretePlace f))) =
      finitePlaceValueExponent (underlyingPrime concretePlace) f := by
  rw [stageModel_divisor_terminal_globalUnit, stageDivisorGrothendieckEquivInt_intTo]
  exact stageNormalizedAdditiveValuation_bot_globalUnit concretePlace f

/-- **Backend divisor coordinate.**  The finite coordinate of the Example 3.6
model-Frobenioid divisor input globalModelDivisor at the concrete place is the
terminal-stage normalized additive valuation of the embedded global unit.  This
closes residual gap (3) of Example36SourceTheaterCarrier.lean at the level of
the backend divisor map. -/
theorem globalModelDivisor_finite_coordinate_eq_stageNormalizedValuation
    (f : GaussianFieldˣ) :
    ((SourceModelBackend.coneGrothendieckEquiv (F := GaussianField))
        ((SourceModelBackend.globalModelDivisor (F := GaussianField))
          (Additive.ofMul f))).1
        SourceTheaterCarrier.concreteHeightOneSpectrum =
      stageNormalizedAdditiveValuation concretePlace (⊥ : StageIndex concretePlace)
        (Additive.ofMul (globalUnitToBottomUnit concretePlace f)) := by
  rw [SourceTheaterCarrier.example36Backend_divisor_finite_coordinate]
  exact (stageNormalizedAdditiveValuation_bot_globalUnit concretePlace f).symm

/-- **Principal-divisor coordinate.**  The finite coordinate of the principal
divisor family of a global unit at the concrete place is the terminal-stage
normalized additive valuation of the embedded global unit. -/
theorem sourceModelPrincipalDivisor_finite_coordinate_eq_stageNormalizedValuation
    (f : GaussianFieldˣ) :
    (sourceModelPrincipalDivisor (numberFieldGlobalPlaceData (F := GaussianField))
        numberFieldGlobalPlaceData_hasFiniteSupport f).finite
        SourceTheaterCarrier.concreteHeightOneSpectrum =
      stageNormalizedAdditiveValuation concretePlace (⊥ : StageIndex concretePlace)
        (Additive.ofMul (globalUnitToBottomUnit concretePlace f)) := by
  rw [sourceModelPrincipalDivisor_finite_apply]
  rw [SourceTheaterCarrier.example36PlaceData_finiteDelta_concretePlace]
  exact (stageNormalizedAdditiveValuation_bot_globalUnit concretePlace f).symm

/-! ## 9. Summary -/

/-- **Summary of the terminal-stage normalization bridge.**  For the concrete
Gaussian place: the terminal-stage normalized additive valuation of the
stage-model divisor monoid equals the completion exponent homomorphism; on
global units it is the global classical finite-place valuation exponent; its
value-group image is the actual completion value; its realified forms are the
integer cast and the finite-place log-volume degree; and the stage-model
divisor coordinate and the Example 3.6 backend divisor coordinate both agree
with it. -/
theorem sourceStageNormalizationBridge_summary
    (f : GaussianFieldˣ) :
    stageNormalizedAdditiveValuation concretePlace
        (⊥ : StageIndex concretePlace) =
      bottomStageCompletionValuation concretePlace ∧
    stageNormalizedAdditiveValuation concretePlace (⊥ : StageIndex concretePlace)
        (Additive.ofMul (globalUnitToBottomUnit concretePlace f)) =
      finitePlaceValueExponent (underlyingPrime concretePlace) f ∧
    stageValueGroupWithZeroIsoInt concretePlace (⊥ : StageIndex concretePlace)
        (ValuativeRel.valuation (↥(⊥ : StageIndex concretePlace).toIntermediateField)
          ((globalUnitToBottomUnit concretePlace f :
            (↥(⊥ : StageIndex concretePlace).toIntermediateField)ˣ) :
            ↥(⊥ : StageIndex concretePlace).toIntermediateField)) =
      Valued.v ((globalCompletionUnit concretePlace f : (Base concretePlace)ˣ) :
        Base concretePlace) ∧
    ((stageNormalizedAdditiveValuation concretePlace
        (⊥ : StageIndex concretePlace)
        (Additive.ofMul (globalUnitToBottomUnit concretePlace f)) : ℤ) : ℝ) =
      (finitePlaceValueExponent (underlyingPrime concretePlace) f : ℝ) ∧
    ((SourceModelBackend.coneGrothendieckEquiv (F := GaussianField))
        ((SourceModelBackend.globalModelDivisor (F := GaussianField))
          (Additive.ofMul f))).1
        SourceTheaterCarrier.concreteHeightOneSpectrum =
      stageNormalizedAdditiveValuation concretePlace (⊥ : StageIndex concretePlace)
        (Additive.ofMul (globalUnitToBottomUnit concretePlace f)) :=
  ⟨stageNormalizedAdditiveValuation_bot_eq_bottomStageCompletionValuation concretePlace,
    stageNormalizedAdditiveValuation_bot_globalUnit concretePlace f,
    stageValueGroupWithZeroIsoInt_bot_globalUnit concretePlace f,
    stageNormalizedAdditiveValuation_bot_realified concretePlace f,
    globalModelDivisor_finite_coordinate_eq_stageNormalizedValuation f⟩

end

end StageNormalizationBridge
end Example36
end Frobenioid
end IUTII
end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the terminal-stage normalization bridge of the concrete
Gaussian place: the terminal-stage normalized additive valuation of the
stage-model divisor monoid is identified with the global classical finite-place
valuation exponent on global units, through the actual completion valuation
Valued.v, in integer, value-group and realified form; the normalization is
proved rigid; and the stage-model divisor coordinate and the Example 3.6
backend divisor coordinate are identified with it. -/
def example36StageNormalizationBridge : Obligation :=
  { id := "IUT-II.example36-stage-normalization-bridge"
    source :=
      "IUT III, Example 3.6 (local dictionary at a finite place); IUT I, " ++
        "Definition 5.2(v) (finite Galois stages of the local reconstruction); " ++
        "Remark 3.9.4 (value groups and log-shells)"
    status := VerificationStatus.interface
    note :=
      "Constructed the unit equivalence between the actual completion Base p " ++
        "and the bottom stage of the finite Galois reconstruction " ++
        "(bottomStageUnitEquiv, baseToBottomUnit, bottomToBaseUnit), with the " ++
        "underlying element formula and the isometry to the completion. Proved " ++
        "surjectivity of the normalized additive valuation of every stage " ++
        "(stageNormalizedAdditiveValuation_surjective) using only bijectivity of " ++
        "the value-group normalization. Proved the sign comparison of the " ++
        "bottom-stage valuation with the completion exponent " ++
        "(stageNormalizedAdditiveValuation_bot_nonneg_iff) through the existing " ++
        "base-integrality and norm criteria and the isometry of the bottom " ++
        "embedding. Proved the rigidity lemma " ++
        "(addMonoidHom_eq_of_surjective_of_nonneg_iff) and from it the " ++
        "terminal-stage homomorphism identity " ++
        "(stageNormalizedAdditiveValuation_bot_eq_bottomStageCompletionValuation); " ++
        "this shows the normalization of the stage valuation is uniquely " ++
        "determined and no identity normalization is assumed, the choice " ++
        "inside Mathlib's value-group normalization being immaterial " ++
        "(stageNormalizedAdditiveValuation_bot_unique). Proved the integer " ++
        "coordinate identity on global units " ++
        "(stageNormalizedAdditiveValuation_bot_globalUnit: terminal-stage " ++
        "valuation of the embedded global unit equals " ++
        "finitePlaceValueExponent), the value-group identity with the actual " ++
        "completion value Valued.v " ++
        "(stageValueGroupWithZeroIsoInt_bot_globalUnit), the realified forms " ++
        "(integer cast; normalized log-volume equal to the realification of the " ++
        "finite-place unit value kernel), and the stage-model divisor coordinate " ++
        "and Example 3.6 backend divisor coordinate identities " ++
        "(stageModel_divisor_terminal_globalUnit_coordinate, " ++
        "globalModelDivisor_finite_coordinate_eq_stageNormalizedValuation, " ++
        "sourceModelPrincipalDivisor_finite_coordinate_eq_stageNormalizedValuation). " ++
        "Residual input: the real absolute-value normalization (the value of " ++
        "the residue-field logarithm) is supplied by the existing finite-place " ++
        "degree kernel, not by the stage data; the stage model at higher stages " ++
        "and its ramification transitions are not re-proved here. No " ++
        "theta-pilot/q-pilot/Tate claim is made, and no map from the local value " ++
        "group back to global units is constructed."
    dependsOn :=
      [ "IUT-I-II.concrete-source-frobenioid-bridge",
        "IUT-I-II.source-finite-stage-model-frobenioid",
        "IUT-I-II.source-finite-stage-model-evaluation",
        "IUT-II.local-integral-f-prime-strip-carrier",
        "IUT-II.example36-source-theater-carrier" ] }

end LeanFormal.IUT.Audit
