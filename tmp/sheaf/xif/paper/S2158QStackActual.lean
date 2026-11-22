import tmp.sheaf.xif.paper.S2152PointwiseColimitActual
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack

noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S2149StackFiberDataActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2158QStackActual

/-- The prestack half for the actual pointwise colimit Q: all hom-presheaves
of Q are sheaves for the slice etale site. -/
def S2158QPrestack : Prop :=
  S2152Q.IsPrestack (Iut.SchemeOverField.etaleTopology S1726K)

/-- The same prestack half written as the concrete sheaf condition on the
hom-presheaves. -/
def S2158QHomSheaf : Prop :=
  forall (S : Iut.SchemeOverField S1726K)
    (M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S))),
    Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology S1726K).over S)
      (S2152Q.presheafHom M N)

/-- The prestack condition is exactly the sheaf condition on every hom-presheaf. -/
theorem S2158QPrestack_iff_homSheaf :
    S2158QPrestack ↔ S2158QHomSheaf := by
  constructor
  · intro h S M N
    exact h.isSheaf M N
  · intro h
    exact ⟨fun {S} M N => h S M N⟩

/-- Effective descent for Q on every etale covering sieve. -/
def S2158QEffectiveDescent (l : PrimeGeFive) : Prop :=
  S2149EffectiveDescent l S2152Q

/-- The required API in one package. -/
structure S2158QRequiredAPI (l : PrimeGeFive) where
  prestack : S2158QPrestack
  effective : S2158QEffectiveDescent l

/-- The required API is exactly the stack condition of Q. -/
theorem S2158QRequiredAPI_iff_isStack (l : PrimeGeFive) :
    Nonempty (S2158QRequiredAPI l) ↔ S2152QIsStack := by
  constructor
  · rintro ⟨h⟩
    exact (S2152QIsStack_iff_descent l).mpr ⟨h.prestack, h.effective⟩
  · intro h
    exact ⟨{ prestack := (S2152QIsStack_iff_descent l).mp h |>.1
             effective := (S2152QIsStack_iff_descent l).mp h |>.2 }⟩

/-- Conditional actual: the API gives the S2149 stack fiber datum. -/
noncomputable def S2158StackFiberData_of_API (l : PrimeGeFive)
    (h : S2158QRequiredAPI l) : S2149StackFiberData l :=
  S2152StackFiberData_of_isStack l
    ((S2158QRequiredAPI_iff_isStack l).mp ⟨h⟩)

/-- The exact first missing for the constructed Q: prestack plus effective
descent, equivalently Q.IsStack. -/
def S2158FirstMissing (l : PrimeGeFive) : Prop :=
  Nonempty (S2158QRequiredAPI l)

/-- The first missing is exactly the stack condition of Q. -/
theorem S2158FirstMissing_iff_isStack (l : PrimeGeFive) :
    S2158FirstMissing l ↔ S2152QIsStack :=
  S2158QRequiredAPI_iff_isStack l

/-- A concrete description of the two remaining obligations: the hom-presheaf
sheaf condition and effective descent. -/
def S2158ConcreteFirstMissing (l : PrimeGeFive) : Prop :=
  S2158QHomSheaf ∧ S2158QEffectiveDescent l

/-- The concrete description is equivalent to the required API. -/
theorem S2158ConcreteFirstMissing_iff (l : PrimeGeFive) :
    S2158ConcreteFirstMissing l ↔ Nonempty (S2158QRequiredAPI l) := by
  constructor
  · rintro ⟨hH, hD⟩
    exact ⟨⟨S2158QPrestack_iff_homSheaf.mpr hH, hD⟩⟩
  · rintro ⟨h⟩
    exact ⟨S2158QPrestack_iff_homSheaf.mp h.prestack, h.effective⟩

#print axioms S2158QPrestack_iff_homSheaf
#print axioms S2158QRequiredAPI_iff_isStack
#print axioms S2158StackFiberData_of_API
#print axioms S2158FirstMissing_iff_isStack
#print axioms S2158ConcreteFirstMissing_iff

end LeanFormal.IUT.XiFPaper.S2158QStackActual

end
