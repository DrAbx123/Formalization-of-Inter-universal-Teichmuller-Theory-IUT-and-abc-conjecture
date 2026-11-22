import tmp.sheaf.xif.paper.S2149StackFiberDataActual
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2149StackFiberDataActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open LeanFormal.IUT.XiFPaper.S2143StackQuotientWitnessActual
open LeanFormal.IUT.XiFPaper.S1732SourceAssemblyActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual

/-- The ordinary functor underlying the actual functorial pointwise colimit:
U maps to the action-groupoid quotient at U, and f : U -> V maps to the
precomposition functor S1971PrecompFunctor f. -/
noncomputable def S2152PFunctor :
    (Iut.SchemeOverField S1726K)ᵒᵖ ⥤ Cat where
  obj U := S1971PointwiseQuotient (LocallyDiscrete.mk U)
  map f := (S1971PrecompFunctor (Discrete.mk f)).toCatHom
  map_id U := rfl
  map_comp f g := rfl

/-- The actual functorial pointwise colimit Q, via the strict-bicategory
promotion of an ordinary functor into Cat. -/
noncomputable def S2152Q : Iut.EtaleStackPseudofunctor S1726K :=
  S2152PFunctor.toPseudofunctor'

/-- The value of Q at every test object is the pointwise action-groupoid
quotient. -/
theorem S2152Q_obj (U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ) :
    S2152Q.obj U = S1971PointwiseQuotient U := rfl

/-- The actual pointwise equivalence to the action-groupoid quotient. -/
theorem S2152Q_pointwise
    (U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ) :
    Nonempty (CategoryTheory.Equivalence (S2152Q.obj U) (S1971PointwiseQuotient U)) :=
  ⟨CategoryTheory.Equivalence.refl⟩

/-- The actual functorial pointwise colimit witness: Q is a pseudofunctor whose
U-points are the pointwise action-groupoid quotient. -/
theorem S2152FunctorialPointwiseColimit :
    S1971FunctorialPointwiseColimit :=
  ⟨S2152Q, fun U => S2152Q_pointwise U⟩

/-- The only remaining input for this Q: it is an etale stack. -/
def S2152QIsStack : Prop :=
  S2152Q.IsStack (Iut.SchemeOverField.etaleTopology S1726K)

/-- The exact descent API for this Q. -/
def S2152QDescentAPI (l : PrimeGeFive) : Prop :=
  S2149RequiredDescentAPI l S2152Q

/-- The stack condition of Q is exactly the descent API. -/
theorem S2152QIsStack_iff_descent (l : PrimeGeFive) :
    S2152QIsStack ↔
      S2152Q.IsPrestack (Iut.SchemeOverField.etaleTopology S1726K) ∧
        S2149EffectiveDescent l S2152Q :=
  S2149IsStack_iff (l := l) S2152Q

/-- Conditional construction of the S2149 stack fiber datum from the missing
IsStack field of Q. -/
noncomputable def S2152StackFiberData_of_isStack
    (l : PrimeGeFive) (h : S2152QIsStack) : S2149StackFiberData l :=
  { Q := S2152Q
    pointwise := fun U => S2152Q_pointwise U
    prestack := (S2152QIsStack_iff_descent l).mp h |>.1
    effective := (S2152QIsStack_iff_descent l).mp h |>.2 }

/-- Conditional construction of the S2143 fiber datum. -/
noncomputable def S2152S2143FiberData_of_isStack
    (l : PrimeGeFive) (h : S2152QIsStack) : S2143StackFiberData l :=
  (S2152StackFiberData_of_isStack l h).toS2143

/-- Conditional actual: IsStack of Q yields the S2149 fiber first missing. -/
theorem S2152S2149FiberFirstMissing_of_isStack
    (l : PrimeGeFive) (h : S2152QIsStack) :
    S2149StackFiberFirstMissing l :=
  ⟨S2152StackFiberData_of_isStack l h⟩

/-- Conditional actual: IsStack of Q yields the S2143 fiber first missing. -/
theorem S2152S2143FiberFirstMissing_of_isStack
    (l : PrimeGeFive) (h : S2152QIsStack) :
    S2143StackFiberFirstMissing l :=
  ⟨S2152S2143FiberData_of_isStack l h⟩

/-- Exact first missing for the constructed Q: Q.IsStack, equivalently
IsPrestack plus effective descent for Q. -/
def S2152FirstMissing : Prop := S2152QIsStack

#print axioms S2152PFunctor
#print axioms S2152Q
#print axioms S2152Q_obj
#print axioms S2152Q_pointwise
#print axioms S2152FunctorialPointwiseColimit
#print axioms S2152QIsStack_iff_descent
#print axioms S2152StackFiberData_of_isStack
#print axioms S2152S2143FiberData_of_isStack
#print axioms S2152S2149FiberFirstMissing_of_isStack
#print axioms S2152S2143FiberFirstMissing_of_isStack

end LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual

end
