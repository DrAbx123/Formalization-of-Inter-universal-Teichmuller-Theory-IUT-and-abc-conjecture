import tmp.sheaf.xif.paper.S2104D9HonestQuotientActual
import tmp.sheaf.xif.paper.S1971ActionStackificationActual

noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1964QuotientCFActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open LeanFormal.IUT.XiFPaper.S2104D9HonestQuotientActual
open LeanFormal.IUT.XiFPaper.S1732SourceAssemblyActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2143StackQuotientWitnessActual

/-- The fiber half of the stack quotient witness: an actual etale stack fiber
whose U-points are the pointwise sign action groupoid. -/
structure S2143StackFiberData (l : PrimeGeFive) where
  Q : Iut.EtaleStackPseudofunctor (S1732A l).F
  isStack : Q.IsStack (Iut.SchemeOverField.etaleTopology (S1732A l).F)
  pointwise : forall U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ,
    Nonempty (CategoryTheory.Equivalence (Q.obj U) (S1971PointwiseQuotient U))

/-- The normalized quotient orbicurve associated to a fiber datum. -/
noncomputable def S2143CF (l : PrimeGeFive) (D : S2143StackFiberData l) :
    Iut.HyperbolicOrbicurve (S1732A l).F :=
  realizedHyperbolicOrbicurve (S1732A l).F D.Q D.isStack
    S1964HonestQuotientSignature S1964HonestQuotientSignature_hyperbolic

/-- The quotient universal-property half. -/
def S2143QuotientUniversalProperty (l : PrimeGeFive)
    (A : Iut.OrbicurveSignAction S1726Orbicurve)
    (D : S2143StackFiberData l) : Prop :=
  exists quotient : Iut.OrbicurveSignInvariantMorphism A (S2143CF l D),
    Nonempty (Iut.OrbicurveSignQuotientWitness A quotient)

/-- The exact stack quotient witness decomposed into a fiber and the quotient
universal property. -/
structure S2143StackQuotientWitness (l : PrimeGeFive)
    (A : Iut.OrbicurveSignAction S1726Orbicurve) where
  fiber : S2143StackFiberData l
  universal : S2143QuotientUniversalProperty l A fiber

/-- The fiber-level first missing. -/
def S2143StackFiberFirstMissing (l : PrimeGeFive) : Prop :=
  Nonempty (S2143StackFiberData l)

/-- The normalized witness is equivalent to the raw S1971 witness by reusing
the fiber, pointwise equivalence and quotient data. -/
theorem S2143Witness_of_S1971 {l : PrimeGeFive}
    {A : Iut.OrbicurveSignAction S1726Orbicurve}
    (h : Nonempty (S1971StackQuotientWitness l A)) :
    Nonempty (S2143StackQuotientWitness l A) := by
  obtain ⟨W⟩ := h
  let D : S2143StackFiberData l :=
    { Q := W.cF.stack.fiber
      isStack := W.cF.stack.isStack
      pointwise := W.pointwise }
  refine ⟨⟨D, ?_⟩⟩
  refine ⟨S2104QuotientOfStackWitness W, ⟨S2104WitnessOfStackWitness W⟩⟩

/-- The normalized witness gives the raw S1971 witness. -/
theorem S1971Witness_of_S2143 {l : PrimeGeFive}
    {A : Iut.OrbicurveSignAction S1726Orbicurve}
    (h : Nonempty (S2143StackQuotientWitness l A)) :
    Nonempty (S1971StackQuotientWitness l A) := by
  obtain ⟨W⟩ := h
  obtain ⟨quotient, ⟨witness⟩⟩ := W.universal
  exact ⟨{ cF := S2143CF l W.fiber
           pointwise := W.fiber.pointwise
           quotient := quotient
           witness := witness }⟩

/-- The two witness forms are equivalent. -/
theorem S2143Witness_iff {l : PrimeGeFive}
    {A : Iut.OrbicurveSignAction S1726Orbicurve} :
    Nonempty (S1971StackQuotientWitness l A) ↔
      Nonempty (S2143StackQuotientWitness l A) :=
  ⟨S2143Witness_of_S1971, S1971Witness_of_S2143⟩

/-! ## Consumers -/

/-- A normalized witness gives the honest quotient (via S2104). -/
theorem S2143HonestQuotient_of_witness {l : PrimeGeFive}
    {A : Iut.OrbicurveSignAction S1726Orbicurve}
    (h : Nonempty (S2143StackQuotientWitness l A)) :
    Nonempty (S2104HonestCFQuotient (l := l) (A := A)) :=
  S2104HonestCFQuotient_of_stackWitness (S1971Witness_of_S2143 h)

/-- A normalized witness gives the S1964 first missing. -/
theorem S2143S1964FirstMissing_of_witness {l : PrimeGeFive}
    {A : Iut.OrbicurveSignAction S1726Orbicurve}
    (h : Nonempty (S2143StackQuotientWitness l A)) :
    S1964FirstMissing l A :=
  S2104S1964FirstMissing_of_stackWitness (S1971Witness_of_S2143 h)

/-- The fiber half is a necessary first missing. -/
theorem S2143StackFiberFirstMissing_of_witness {l : PrimeGeFive}
    {A : Iut.OrbicurveSignAction S1726Orbicurve}
    (h : Nonempty (S2143StackQuotientWitness l A)) :
    S2143StackFiberFirstMissing l :=
  h.elim fun W => ⟨W.fiber⟩

#print axioms S2143CF
#print axioms S2143Witness_of_S1971
#print axioms S1971Witness_of_S2143
#print axioms S2143Witness_iff
#print axioms S2143HonestQuotient_of_witness
#print axioms S2143S1964FirstMissing_of_witness
#print axioms S2143StackFiberFirstMissing_of_witness

end LeanFormal.IUT.XiFPaper.S2143StackQuotientWitnessActual

end
