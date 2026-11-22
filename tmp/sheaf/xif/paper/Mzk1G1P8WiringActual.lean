import tmp.sheaf.xif.paper.Mzk1G1P8ProducerAssemblyActual
import tmp.sheaf.xif.paper.Mzk1P8ActualDisplayHeightActual
import Mathlib.Tactic
/-!
# P8-P wiring: assembly input → P8UniformHeightBound → ABCConjecture

Thin wrappers over the DONE skeleton `Mzk1G1P8ProducerAssemblyActual` (22:03:14):
`P8AssemblyInput` collects the L-H/G-K/H-T per-triple outputs; the reverse arrow of
`abcConjecture_iff_freyJProductHeightCriterion` then gives ABC.
-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.P8WiringActual
open LeanFormal.IUT.XiFPaper.P8ProducerAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual
open LeanFormal.IUT

/-- P8-P: the parameterized assembly (one input per `ε`) produces the uniform height bound. -/
theorem p8_input_of_all
    (H : ∀ epsilon : ℝ, 0 < epsilon → LeanFormal.IUT.XiFPaper.P8ProducerAssemblyActual.P8AssemblyInput epsilon) :
    P8UniformHeightBound :=
  p8UniformHeightBound_of_assembly H

/-- P8-P gives ABC (through the assembled uniform height bound). -/
theorem p8_assembly_actual
    (H : ∀ epsilon : ℝ, 0 < epsilon → LeanFormal.IUT.XiFPaper.P8ProducerAssemblyActual.P8AssemblyInput epsilon) :
    ABCConjecture :=
  abcConjecture_of_assembly H

/-- The last arrow: `P8UniformHeightBound ⇒ ABCConjecture` via the accepted reverse
equivalence `abcConjecture_iff_freyJProductHeightCriterion`. -/
theorem abc_of_p8 (h : P8UniformHeightBound) : ABCConjecture :=
  p8_abc_of_uniformHeightBound_actual h

#print axioms p8_input_of_all
#print axioms p8_assembly_actual
#print axioms abc_of_p8
end LeanFormal.IUT.XiFPaper.P8WiringActual
end