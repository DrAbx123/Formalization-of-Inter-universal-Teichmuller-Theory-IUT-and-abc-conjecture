import LeanFormal.IUT.Foundations.LocalFields.AlgebraicUnitFiniteCarrier
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# A common finite local-field carrier for two actual algebraic units

The compositum of the two individual carriers is finite-dimensional.
This is the common complete domain used to prove the global logarithm
law; no completeness of the ambient algebraic extension is assumed.
-/

namespace LeanFormal.IUT.LocalFieldIntegralUnits

noncomputable section

variable {Ω : Type*} [NormedField Ω] [IsUltrametricDist Ω]
variable {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] Ω]

def integralUnitLiftToIntermediateField (F : IntermediateField ℚ_[p] Ω)
    (u : (Integers Ω)ˣ) (hu : (u.val : Ω) ∈ F) : (Integers F)ˣ :=
  unitOfNormOne ⟨⟨u.val, hu⟩, norm_unit_eq_one u⟩

theorem integralUnitLiftToIntermediateField_val (F : IntermediateField ℚ_[p] Ω)
    (u : (Integers Ω)ˣ) (hu : (u.val : Ω) ∈ F) :
    ((integralUnitLiftToIntermediateField F u hu).val : F).val = (u.val : Ω) := rfl

def finiteUnitPairField (u v : (Integers Ω)ˣ) : IntermediateField ℚ_[p] Ω :=
  finiteUnitField (p := p) u ⊔ finiteUnitField (p := p) v

theorem mem_finiteUnitPairField_left (u v : (Integers Ω)ˣ) :
    (u.val : Ω) ∈ finiteUnitPairField (p := p) u v :=
  (show finiteUnitField (p := p) u ≤ finiteUnitPairField (p := p) u v from le_sup_left)
    (IntermediateField.mem_adjoin_simple_self ℚ_[p] (u.val : Ω))

theorem mem_finiteUnitPairField_right (u v : (Integers Ω)ˣ) :
    (v.val : Ω) ∈ finiteUnitPairField (p := p) u v :=
  (show finiteUnitField (p := p) v ≤ finiteUnitPairField (p := p) u v from le_sup_right)
    (IntermediateField.mem_adjoin_simple_self ℚ_[p] (v.val : Ω))

variable [Algebra.IsAlgebraic ℚ_[p] Ω]

instance finiteUnitPairField_finiteDimensional (u v : (Integers Ω)ˣ) :
    FiniteDimensional ℚ_[p] (finiteUnitPairField (p := p) u v) :=
  IntermediateField.finiteDimensional_sup _ _

instance finiteUnitPairField_properSpace (u v : (Integers Ω)ˣ) :
    ProperSpace (finiteUnitPairField (p := p) u v) :=
  FiniteDimensional.proper ℚ_[p] (finiteUnitPairField (p := p) u v)

end

end LeanFormal.IUT.LocalFieldIntegralUnits
