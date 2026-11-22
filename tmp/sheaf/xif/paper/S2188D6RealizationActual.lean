import tmp.sheaf.xif.paper.S2177SignQuotientDataActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36OrbicurveFeasibility

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2188D6RealizationActual

open LeanFormal.IUT
open CategoryTheory
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility
open LeanFormal.IUT.XiFPaper.S2177SignQuotientDataActual

universe u

variable {l : PrimeGeFive}

/-! ## 1. The exact nondegenerate D6 carrier -/

/-- The D6 geometric realization with the curve fixed to the paper arithmetic
curve: actual nondegenerate etale-stack fiber, effective descent, and a
surjective realization of the curve's projective points. -/
structure S2188D6Realization
    (A : InitialThetaArithmeticData l) where
  fiber : Iut.EtaleStackPseudofunctor A.F
  isStack : fiber.IsStack (Iut.SchemeOverField.etaleTopology A.F)
  nondegenerate : ¬ IsPointFiber fiber
  curvePointRealization :
    ∃ f : fiber.obj (LocallyDiscrete.mk (Opposite.op (baseSchemeObject A.F))) →
        A.curve.curve.toProjective.Point, Function.Surjective f

/-- From the S2177 D6 package, build the fixed-curve carrier. -/
noncomputable def s2188D6RealizationOfS2177
    {A : InitialThetaArithmeticData l}
    (D : S2177ActualD6Orbicurve A) :
    S2188D6Realization A where
  fiber := D.D.fiber
  isStack := D.D.isStack
  nondegenerate := D.D.nondegenerate
  curvePointRealization := D.curve_eq ▸ D.D.curvePointRealization

/-- From the fixed-curve carrier, build the S2177 D6 package. -/
noncomputable def s2188S2177OfD6Realization
    {A : InitialThetaArithmeticData l}
    (D : S2188D6Realization A) :
    S2177ActualD6Orbicurve A where
  D :=
    { curve := A.curve
      fiber := D.fiber
      isStack := D.isStack
      nondegenerate := D.nondegenerate
      curvePointRealization := D.curvePointRealization }
  curve_eq := rfl

/-- Exact equivalence of the S2177 package and the fixed-curve D6 carrier. -/
theorem s2188D6Realization_iff_s2177
    (A : InitialThetaArithmeticData l) :
    Nonempty (S2188D6Realization A) ↔
      Nonempty (S2177ActualD6Orbicurve A) := by
  constructor
  · rintro ⟨D⟩
    exact ⟨s2188S2177OfD6Realization D⟩
  · rintro ⟨D⟩
    exact ⟨s2188D6RealizationOfS2177 D⟩

/-! ## 2. The stack-fiber component and degeneracy exclusions -/

/-- Exact stack-fiber component: a non-point etale stack fiber with effective
descent over the actual etale topology. -/
structure S2188EtaleStackFiberRequired
    (F : Type u) [Field F] where
  fiber : Iut.EtaleStackPseudofunctor F
  isStack : fiber.IsStack (Iut.SchemeOverField.etaleTopology F)
  nondegenerate : ¬ IsPointFiber fiber

/-- A D6 carrier supplies the stack-fiber component. -/
noncomputable def s2188EtaleStackFiberOfD6
    {A : InitialThetaArithmeticData l}
    (D : S2188D6Realization A) :
    S2188EtaleStackFiberRequired A.F where
  fiber := D.fiber
  isStack := D.isStack
  nondegenerate := D.nondegenerate

/-- The terminal constant fiber cannot be the D6 fiber. -/
theorem s2188_terminal_fiber_forbidden
    {A : InitialThetaArithmeticData l}
    (D : S2188D6Realization A) :
    D.fiber ≠
      InitialThetaSource.Definition31OrbicurveInstance.terminalConstantFiber A.F := by
  intro h
  exact D.nondegenerate
    (h ▸ terminalConstant_isPointFiber A.F)

/-- Exact first missing proposition: the nondegenerate stack-fiber component. -/
def S2188EtaleStackFiberRequiredProp
    (F : Type u) [Field F] : Prop :=
  Nonempty (S2188EtaleStackFiberRequired F)

/-- The proposition is definitionally the nonemptiness of the fiber component. -/
theorem s2188EtaleStackFiberRequiredProp_iff
    (F : Type u) [Field F] :
    S2188EtaleStackFiberRequiredProp F ↔
      Nonempty (S2188EtaleStackFiberRequired F) :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.S2188D6RealizationActual
end