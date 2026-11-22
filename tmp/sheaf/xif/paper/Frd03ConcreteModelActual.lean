import LeanFormal.IUT.IUTII.Frobenioid.ConcreteSourceFrobenioidBridge
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Frd03: concrete model Frobenioid layer [FrdI §5] (A-class reuse)

The tree's concrete model Frobenioid presentation (Iut.FrobenioidPresentation via
concreteStageModel, with the divisorial monoid and model input of
ConcreteSourceFrobenioidBridge) is REUSED as the [FrdI] §5 model-Frobenioid
witness.  Paper category-theoreticity/functoriality theorems remain class B.

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.Frd03ConcreteModelActual

open LeanFormal.IUT
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open Iut

local instance frd03PrimeFact (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  l.factPrime

universe u

/-- The concrete model Frobenioid presentation at the prime l (reuse). -/
def concreteModelFrobenioid (l : PrimeGeFive) : Iut.FrobenioidPresentation :=
  concreteStageModel

/-- The concrete model Frobenioid exists (A-class; FrdI §5 witness). -/
theorem concreteModelFrobenioid_nonempty (l : PrimeGeFive) :
    Nonempty Iut.FrobenioidPresentation.{0} :=
  ⟨concreteModelFrobenioid l⟩

/-- The boundary's model is the concrete model Frobenioid (reused equality law). -/
theorem concreteModelFrobenioid_eq_boundary_model (l : PrimeGeFive) :
    (concreteSourceFrobenioidBoundary l).model = concreteModelFrobenioid l :=
  boundary_model l

/-- The concrete model's finite Kummer kernel law (reused). -/
theorem concreteModelFrobenioid_kernel (l : PrimeGeFive) :
    (concreteSourceFrobenioidBoundary l).cStage.localCarrier.kummer.finiteReduction.ker =
      AddSubgroup.zmultiples (l.value : ℤ) :=
  boundary_kernel l

/-- FrdI §5 reuse record. -/
def frdModelReuse : List (String × String × String) :=
  [ ("FrdI §5 Model Frobenioids", "concreteStageModel : Iut.FrobenioidPresentation", "A (reuse tree concrete model)"),
    ("model divisorial monoid / model input", "ConcreteSourceFrobenioidBridge: concreteStageModelDivisorialMonoid / concreteStageModelInput", "A (reuse)"),
    ("category-theoreticity of the model", "FrdI §3/§4 paper theorems", "B (named; not claimed)") ]

end LeanFormal.IUT.XiFPaper.Frd03ConcreteModelActual

end
