import tmp.sheaf.xif.paper.PaperC3TensorGeometryActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks

/-! # Actual tensor block for the completion-valued source geometry -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperCompletionTensorActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorGeometryActual

universe ua uv upi umon ui u

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type uv} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

/-- The actual nondegenerate tensor places indexed by the source places. -/
abbrev PaperTensorPlaces : V → Unit → FinitePlaceAtPrime K p :=
  fun v _ => G.place v

/-- The actual tensor tuple. -/
abbrev PaperTensorTuple : V → Unit := fun _ => ()

/-- The actual tensor block: one completion factor per actual source place. -/
abbrev PaperTensorBlock : Type (max uv u) :=
  ArithmeticTensorTupleBlock (PaperTensorPlaces (G := G)) (PaperTensorTuple (V := V))

/-- The actual unit of the tensor block. -/
noncomputable def paperTensorUnit : (PaperTensorBlock (G := G))ˣ :=
  1

theorem paperTensorUnit_val :
    (paperTensorUnit (G := G) : PaperTensorBlock (G := G)) = 1 := rfl

theorem paperTensorBlock_finrank_pos :
    0 < Module.finrank ℚ_[p] (PaperTensorBlock (G := G)) :=
  finrank_arithmeticTensorTupleBlock_pos (PaperTensorPlaces (G := G))
    (PaperTensorTuple (V := V))

end LeanFormal.IUT.XiFPaper.PaperCompletionTensorActual

end