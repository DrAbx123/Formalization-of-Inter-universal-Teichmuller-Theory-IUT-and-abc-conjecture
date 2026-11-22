import tmp.sheaf.xif.paper.S2046M1BridgeActual
import LeanFormal.IUT.IUTII.Frobenioid.PrimeStripFrobenioidCards
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.NumberTheory.Padics.Complex

/-!
# S2090: the evaluated integral-unit subgroup is the algebraic-closure unit group

Layer: O (S2046 M1 corrected local units).

This file constructs the exact bridge

  `evaluatedUnitSubgroup p ≃* (Integers (AlgebraicClosure Q_[p]))^x`

whose conditional use was recorded in `S2046M1BridgeActual`.  The subgroup
`evaluatedUnitSubgroup p` (IUT II, Definition 4.9(i) at the concrete local
model) consists of the algebraic-closure units whose value and inverse value are
integral over the p-adic valuation ring `Z_p`.  The forward direction
`IsIntegral -> norm ≤ 1` is the existing
`localAlgebraicInteger_norm_le_one`.  The reverse direction
`norm ≤ 1 -> IsIntegral` is proved here from the spectral norm: if the norm is
at most one, then every coefficient of the minimal polynomial over `Q_p` has
norm at most one, hence lifts to the p-adic valuation ring, and the lifted
monic polynomial witnesses integrality.  The two integrality conditions are then
packaged into a multiplicative equivalence with the unit group of Mathlib's
integral subring, using `Subtype.ext` on both levels.

No `sorry`, `axiom`, or extra hypothesis is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2090EvaluatedUnitsBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalIntegralMonoid
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-! ## 1. The p-adic valuative relation versus the norm -/

/-- On `Q_p`, the unit ball of the canonical valuative-relation valuation
agrees with the closed unit ball of the p-adic norm. -/
theorem padicValuativeRel_le_one_iff_norm (x : ℚ_[p]) :
    ValuativeRel.valuation ℚ_[p] x ≤ 1 ↔ ‖x‖ ≤ 1 :=
  (Valuation.vle_one_iff (ValuativeRel.valuation ℚ_[p])).symm.trans
    ((Valuation.vle_one_iff (Padic.mulValuation (p := p))).trans
      (LocalIntegralUnitKummerInjectivity.padicMulValuation_le_one_iff_norm_le_one p x))

/-! ## 2. Norm at most one implies integrality over the p-adic integers -/

/-- An element of the algebraic closure whose norm is at most one is integral
over the p-adic valuation ring.  This is the reverse direction of
`localAlgebraicInteger_norm_le_one`. -/
theorem isIntegral_of_norm_le_one (x : AlgebraicClosure ℚ_[p]) (hx : ‖x‖ ≤ 1) :
    IsIntegral (Valuation.integer (ValuativeRel.valuation ℚ_[p])) x := by
  let R := Valuation.integer (ValuativeRel.valuation ℚ_[p])
  change IsIntegral R x
  letI : IsScalarTower R ℚ_[p] (AlgebraicClosure ℚ_[p]) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hmonic : (minpoly ℚ_[p] x).Monic :=
    minpoly.monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hsp : spectralNorm ℚ_[p] (AlgebraicClosure ℚ_[p]) x ≤ 1 := by
    simpa only [PadicAlgCl.spectralNorm_eq] using hx
  have hsp' : spectralValue (minpoly ℚ_[p] x) ≤ 1 := hsp
  have hcoeff : ∀ n : ℕ, ‖(minpoly ℚ_[p] x).coeff n‖ ≤ 1 :=
    (spectralValue_le_one_iff hmonic).mp hsp'
  have hlifts : minpoly ℚ_[p] x ∈ Polynomial.lifts (algebraMap R ℚ_[p]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨(minpoly ℚ_[p] x).coeff n,
      (padicValuativeRel_le_one_iff_norm p _).mpr (hcoeff n)⟩, rfl⟩
  obtain ⟨q, hqmap, -, hqmonic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic hlifts hmonic
  refine ⟨q, hqmonic, ?_⟩
  have h := Polynomial.aeval_map_algebraMap (ℚ_[p]) x q
  rw [hqmap, minpoly.aeval] at h
  exact h.symm

/-- Integrality over the p-adic valuation ring is exactly the condition that
the p-adic norm is at most one. -/
theorem isIntegral_iff_norm_le_one (x : AlgebraicClosure ℚ_[p]) :
    IsIntegral (Valuation.integer (ValuativeRel.valuation ℚ_[p])) x ↔ ‖x‖ ≤ 1 :=
  ⟨fun hx => localAlgebraicInteger_norm_le_one p ⟨x, hx⟩,
    isIntegral_of_norm_le_one p x⟩

/-- Membership in Mathlib's integral subring and integrality over the p-adic
valuation ring agree. -/
theorem isIntegral_iff_mem_integers (x : AlgebraicClosure ℚ_[p]) :
    IsIntegral (Valuation.integer (ValuativeRel.valuation ℚ_[p])) x ↔
      x ∈ Integers (AlgebraicClosure ℚ_[p]) :=
  (isIntegral_iff_norm_le_one p x).trans (mem_integers_iff x).symm

/-! ## 3. The unit-subgroup membership conversion -/

/-- The evaluated integral-unit subgroup is exactly the subgroup of units whose
value and inverse value lie in the integral subring.  This is the
`x ∈ Integers` / `x⁻¹ ∈ Integers` conversion used in the equivalence. -/
theorem mem_evaluatedUnitSubgroup_iff (u : (AlgebraicClosure ℚ_[p])ˣ) :
    u ∈ evaluatedUnitSubgroup p ↔
      ((u : AlgebraicClosure ℚ_[p]) ∈ Integers (AlgebraicClosure ℚ_[p]) ∧
        ((u : AlgebraicClosure ℚ_[p])⁻¹) ∈ Integers (AlgebraicClosure ℚ_[p])) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(isIntegral_iff_mem_integers p _).mp h1,
      (isIntegral_iff_mem_integers p _).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(isIntegral_iff_mem_integers p _).mpr h1,
      (isIntegral_iff_mem_integers p _).mpr h2⟩

/-! ## 4. The multiplicative equivalence -/

/-- The exact bridge: the evaluated integral-unit subgroup is the actual unit
group of `Integers (AlgebraicClosure Q_p)`. -/
noncomputable def evaluatedUnitsEquivIntegersUnits :
    evaluatedUnitSubgroup p ≃* (Integers (AlgebraicClosure ℚ_[p]))ˣ where
  toFun u :=
    { val := ⟨((u : (AlgebraicClosure ℚ_[p])ˣ) : AlgebraicClosure ℚ_[p]),
        (mem_integers_iff _).mpr
          (localAlgebraicInteger_norm_le_one p
            ⟨((u : (AlgebraicClosure ℚ_[p])ˣ) : AlgebraicClosure ℚ_[p]),
              u.property.1⟩)⟩
      inv := ⟨(((u : (AlgebraicClosure ℚ_[p])ˣ) : AlgebraicClosure ℚ_[p]))⁻¹,
        (mem_integers_iff _).mpr
          (localAlgebraicInteger_norm_le_one p
            ⟨(((u : (AlgebraicClosure ℚ_[p])ˣ) : AlgebraicClosure ℚ_[p]))⁻¹,
              u.property.2⟩)⟩
      val_inv := by
        apply Subtype.ext
        change ((u : (AlgebraicClosure ℚ_[p])ˣ) : AlgebraicClosure ℚ_[p]) *
          (((u : (AlgebraicClosure ℚ_[p])ˣ) : AlgebraicClosure ℚ_[p]))⁻¹ = 1
        exact mul_inv_cancel₀ (Units.ne_zero (u : (AlgebraicClosure ℚ_[p])ˣ))
      inv_val := by
        apply Subtype.ext
        change (((u : (AlgebraicClosure ℚ_[p])ˣ) : AlgebraicClosure ℚ_[p]))⁻¹ *
          ((u : (AlgebraicClosure ℚ_[p])ˣ) : AlgebraicClosure ℚ_[p]) = 1
        exact inv_mul_cancel₀ (Units.ne_zero (u : (AlgebraicClosure ℚ_[p])ˣ)) }
  invFun w :=
    ⟨Units.map (Integers (AlgebraicClosure ℚ_[p])).subtype.toMonoidHom w, by
      constructor
      · exact isIntegral_of_norm_le_one p _
          ((mem_integers_iff _).mp w.val.property)
      · have h : IsIntegral (Valuation.integer (ValuativeRel.valuation ℚ_[p]))
            ((w.inv : Integers (AlgebraicClosure ℚ_[p])) :
              AlgebraicClosure ℚ_[p]) :=
          isIntegral_of_norm_le_one p _
            ((mem_integers_iff _).mp w.inv.property)
        have hz : (((Units.map (Integers (AlgebraicClosure ℚ_[p])).subtype.toMonoidHom w :
            (AlgebraicClosure ℚ_[p])ˣ) : AlgebraicClosure ℚ_[p]))⁻¹ =
            ((w.inv : Integers (AlgebraicClosure ℚ_[p])) : AlgebraicClosure ℚ_[p]) := by
          rw [← Units.val_inv_eq_inv_val]
          rfl
        rw [hz]
        exact h⟩
  left_inv u := by
    apply Subtype.ext
    apply Units.ext
    rfl
  right_inv w := by
    apply Units.ext
    apply Subtype.ext
    rfl
  map_mul' u v := by
    apply Units.ext
    apply Subtype.ext
    rfl

@[simp]
theorem evaluatedUnitsEquivIntegersUnits_apply_coe (u : evaluatedUnitSubgroup p) :
    ((evaluatedUnitsEquivIntegersUnits p u : (Integers (AlgebraicClosure ℚ_[p]))ˣ) :
        AlgebraicClosure ℚ_[p]) = ((u : (AlgebraicClosure ℚ_[p])ˣ) :
          AlgebraicClosure ℚ_[p]) := rfl

@[simp]
theorem evaluatedUnitsEquivIntegersUnits_symm_apply (w :
    (Integers (AlgebraicClosure ℚ_[p]))ˣ) :
    ((evaluatedUnitsEquivIntegersUnits p).symm w :
      (AlgebraicClosure ℚ_[p])ˣ) =
      Units.map (Integers (AlgebraicClosure ℚ_[p])).subtype.toMonoidHom w := rfl

/-! ## 5. Consumers: the S2046 M1 bridge is now inhabited -/

/-- The equivalence, as an inhabitant of the exact type recorded as missing in
`S2046M1BridgeActual`. -/
noncomputable def S2046EvaluatedUnitsToIntegersRequired_actual :
    S2046M1BridgeActual.S2046EvaluatedUnitsToIntegersRequired p :=
  evaluatedUnitsEquivIntegersUnits p

/-- The exact S2046 M1 first missing type is now inhabited. -/
theorem S2046EvaluatedUnitsToIntegersRequired_nonempty :
    Nonempty (S2046M1BridgeActual.S2046EvaluatedUnitsToIntegersRequired p) :=
  ⟨evaluatedUnitsEquivIntegersUnits p⟩

/-- Unconditional composition: the units of the local integral monoid are the
actual local `O^x` units. -/
noncomputable def S2046LocalUnitsEquivOtriUnits :
    (Otri p)ˣ ≃* LocalOFieldUnits p :=
  S2046M1BridgeActual.S2046LocalUnitsEquivOtriUnitsOfBridge p
    (evaluatedUnitsEquivIntegersUnits p)

/-- Actual identification of `(Otri p)^x` with the units of the integral
subring. -/
noncomputable def S2090OtriUnitsEquivIntegersUnits :
    (Otri p)ˣ ≃* (Integers (AlgebraicClosure ℚ_[p]))ˣ :=
  (unitEvaluationEquiv p).trans (evaluatedUnitsEquivIntegersUnits p)

/-! ## 6. Axiom probes -/

#check evaluatedUnitsEquivIntegersUnits
#check S2046LocalUnitsEquivOtriUnits
#check S2090OtriUnitsEquivIntegersUnits
#print axioms isIntegral_of_norm_le_one
#print axioms isIntegral_iff_mem_integers
#print axioms mem_evaluatedUnitSubgroup_iff
#print axioms evaluatedUnitsEquivIntegersUnits
#print axioms S2046EvaluatedUnitsToIntegersRequired_actual
#print axioms S2046EvaluatedUnitsToIntegersRequired_nonempty
#print axioms S2046LocalUnitsEquivOtriUnits
#print axioms S2090OtriUnitsEquivIntegersUnits

end LeanFormal.IUT.XiFPaper.S2090EvaluatedUnitsBridgeActual

end
