import tmp.sheaf.xif.paper.PaperC3TensorBlockActual

/-!
# qUnit tensor scalar decomposition: exact obstruction

The requested per-factor definition

  normalizedUnit v = qUnit v / ||qUnit v||

is not a term in the current setup: CommonPrimeCompletion is a p-adic
completion field, not an ℝ-algebra, and there is no coercion ℝ -> K that would
let a field element be divided by its real norm.  A valid scalar decomposition
must use a p-adic scalar (for example p^(-n) with an integer exponent) and an
integral norm-one unit.

This file proves the actual nonzero/positive norm facts and records the exact
missing scalar decomposition.  It does not define a fake normalized unit.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QUnitTensorScalarDecompositionObstructionActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual

universe u v

variable {l : PrimeGeFive}
variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

/-- qUnit has nonzero norm. -/
theorem qUnit_norm_ne_zero (v : V) :
    ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≠ 0 :=
  norm_ne_zero_iff.mpr (Units.ne_zero (G.qUnit v))

/-- qUnit has positive norm. -/
theorem qUnit_norm_pos (v : V) :
    0 < ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ :=
  norm_pos_iff.mpr (Units.ne_zero (G.qUnit v))

/-- Exact missing qUnit tensor scalar decomposition. -/
structure QUnitTensorScalarDecompositionGap where
  scalarTensor : Prop
  integralUnitTensor : Prop
  normalizedFactor : Prop
  norm_one_factor : Prop
  decomposition_eq : Prop
  scalar_power_relation : Prop

/-- Exact missing decomposition object. -/
def QUnitTensorScalarDecompositionGapRequired : Prop :=
  Nonempty QUnitTensorScalarDecompositionGap

/-- Consumer relation: the norm facts are actual, but the scalar/unit tensor
decomposition remains exact because the scalar must be a p-adic power, not the
real norm. -/
def QUnitTensorScalarDecompositionNotConstructed : Prop :=
  QUnitTensorScalarDecompositionGapRequired

end LeanFormal.IUT.XiFPaper.QUnitTensorScalarDecompositionObstructionActual
end
