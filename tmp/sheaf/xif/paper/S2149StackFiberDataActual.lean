import tmp.sheaf.xif.paper.S2143StackQuotientWitnessActual
import tmp.sheaf.xif.paper.S2093D9StackActual
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack

noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2143StackQuotientWitnessActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open LeanFormal.IUT.XiFPaper.S2093D9StackActual
open LeanFormal.IUT.XiFPaper.S1732SourceAssemblyActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2149StackFiberDataActual

/-- Exact effective-descent API for a pseudofunctor Q on the etale site of
SchemeOverField (S1732A l).F. -/
def S2149EffectiveDescent (l : PrimeGeFive)
    (Q : Iut.EtaleStackPseudofunctor (S1732A l).F) : Prop :=
  forall (U : Iut.SchemeOverField (S1732A l).F) (R : Sieve U),
    R ∈ Iut.SchemeOverField.etaleTopology (S1732A l).F U ->
      (Q.toDescentData (fun f : R.arrows.category => f.obj.hom)).EssSurj

/-- IsStack decomposes exactly into the prestack condition and effective
descent. -/
theorem S2149IsStack_iff (l : PrimeGeFive)
    (Q : Iut.EtaleStackPseudofunctor (S1732A l).F) :
    Q.IsStack (Iut.SchemeOverField.etaleTopology (S1732A l).F) ↔
      Q.IsPrestack (Iut.SchemeOverField.etaleTopology (S1732A l).F) ∧
        S2149EffectiveDescent l Q := by
  constructor
  · intro h
    refine ⟨h.toIsPrestack, ?_⟩
    intro U R hR
    exact h.essSurj_of_sieve R hR
  · rintro ⟨hP, hD⟩
    exact { toIsPrestack := hP, essSurj_of_sieve := fun {U} R hR => hD U R hR }

/-- The stack fiber datum in descent-API form: an actual pseudofunctor Q,
pointwise equivalence to the action-groupoid quotient, the prestack half and
effective descent. -/
structure S2149StackFiberData (l : PrimeGeFive) where
  Q : Iut.EtaleStackPseudofunctor (S1732A l).F
  pointwise : forall U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ,
    Nonempty (CategoryTheory.Equivalence (Q.obj U) (S1971PointwiseQuotient U))
  prestack : Q.IsPrestack (Iut.SchemeOverField.etaleTopology (S1732A l).F)
  effective : S2149EffectiveDescent l Q

/-- The descent-API fiber datum gives the IsStack fiber data. -/
def S2149StackFiberData.toS2143 {l : PrimeGeFive}
    (D : S2149StackFiberData l) : S2143StackFiberData l :=
  { Q := D.Q
    isStack := (S2149IsStack_iff l D.Q).mpr ⟨D.prestack, D.effective⟩
    pointwise := D.pointwise }

/-- The IsStack fiber data gives the descent-API fiber data. -/
def S2149StackFiberData.ofS2143 {l : PrimeGeFive}
    (D : S2143StackFiberData l) : S2149StackFiberData l :=
  { Q := D.Q
    pointwise := D.pointwise
    prestack := (S2149IsStack_iff l D.Q).mp D.isStack |>.1
    effective := (S2149IsStack_iff l D.Q).mp D.isStack |>.2 }

/-- The two fiber-data forms are equivalent. -/
theorem S2149StackFiberData_iff {l : PrimeGeFive} :
    Nonempty (S2149StackFiberData l) ↔
      Nonempty (S2143StackFiberData l) :=
  ⟨fun ⟨D⟩ => ⟨D.toS2143⟩, fun ⟨D⟩ => ⟨S2149StackFiberData.ofS2143 D⟩⟩

/-- The exact first missing at the fiber level, in descent-API form. -/
def S2149StackFiberFirstMissing (l : PrimeGeFive) : Prop :=
  Nonempty (S2149StackFiberData l)

/-- The descent-API first missing is exactly the S2143 fiber first missing. -/
theorem S2149StackFiberFirstMissing_iff {l : PrimeGeFive} :
    S2149StackFiberFirstMissing l ↔
      S2143StackFiberFirstMissing l :=
  S2149StackFiberData_iff

/-- The required descent API: prestack (descent of morphisms) plus effective
descent for every etale covering sieve. -/
def S2149RequiredDescentAPI (l : PrimeGeFive)
    (Q : Iut.EtaleStackPseudofunctor (S1732A l).F) : Prop :=
  Q.IsPrestack (Iut.SchemeOverField.etaleTopology (S1732A l).F) ∧
    S2149EffectiveDescent l Q

/-- The required API is exactly IsStack. -/
theorem S2149RequiredDescentAPI_iff (l : PrimeGeFive)
    (Q : Iut.EtaleStackPseudofunctor (S1732A l).F) :
    S2149RequiredDescentAPI l Q ↔
      Q.IsStack (Iut.SchemeOverField.etaleTopology (S1732A l).F) :=
  (S2149IsStack_iff l Q).symm

#print axioms S2149IsStack_iff
#print axioms S2149StackFiberData_iff
#print axioms S2149StackFiberFirstMissing_iff
#print axioms S2149RequiredDescentAPI_iff

end LeanFormal.IUT.XiFPaper.S2149StackFiberDataActual

end
