import LeanFormal.IUT.Foundations.LocalFields.AlgebraicUnitFiniteCarrier

/-!
# A complete finite carrier for an arbitrary algebraic field element

This carrier supplies the local field in which denominators are cleared
into the actual unit logarithmic image before passage back to the
ambient, possibly noncomplete, algebraic extension.
-/

namespace LeanFormal.IUT.LocalFieldIntegralUnits

noncomputable section

variable {Ω : Type*} [NormedField Ω]
variable {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] Ω]
variable [Algebra.IsAlgebraic ℚ_[p] Ω]

def finiteElementField (x : Ω) : IntermediateField ℚ_[p] Ω :=
  IntermediateField.adjoin ℚ_[p] {x}

instance finiteElementField_finiteDimensional (x : Ω) :
    FiniteDimensional ℚ_[p] (finiteElementField (p := p) x) :=
  IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic x).isIntegral

instance finiteElementField_properSpace (x : Ω) :
    ProperSpace (finiteElementField (p := p) x) :=
  FiniteDimensional.proper ℚ_[p] (finiteElementField (p := p) x)

def finiteElementLift (x : Ω) : finiteElementField (p := p) x :=
  ⟨x, IntermediateField.mem_adjoin_simple_self ℚ_[p] x⟩

omit [Algebra.IsAlgebraic ℚ_[p] Ω] in
theorem finiteElementLift_val (x : Ω) : (finiteElementLift (p := p) x).val = x := rfl

end

end LeanFormal.IUT.LocalFieldIntegralUnits
