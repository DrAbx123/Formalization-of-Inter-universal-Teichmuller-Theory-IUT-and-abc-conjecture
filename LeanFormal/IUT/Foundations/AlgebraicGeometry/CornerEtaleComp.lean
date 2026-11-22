import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace ABCBridge.CornerEtaleComp

noncomputable section

universe u

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- Composition of finite etale algebra maps is finite etale. -/
theorem etale_comp [Algebra.Etale A B] [Module.Finite A B]
    [Algebra.Etale B C] [Module.Finite B C] :
    Algebra.Etale A C ∧ Module.Finite A C :=
  ⟨Algebra.Etale.comp A B C, Module.Finite.trans B C⟩

end

end ABCBridge.CornerEtaleComp
