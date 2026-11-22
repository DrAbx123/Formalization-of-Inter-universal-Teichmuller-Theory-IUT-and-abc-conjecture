import tmp.sheaf.xif.paper.S2025QuotientStackPackageActual

/-! Consumer check for S2025: the olean imports and the named interface is usable. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1994KSideCovers
open LeanFormal.IUT.XiFPaper.S1997LTorsRootStackActual
open LeanFormal.IUT.XiFPaper.S2022QuotientStackActual
open LeanFormal.IUT.XiFPaper.S2025QuotientStackPackageActual

universe u

variable {K : Type u} [Field K] {l : PrimeGeFive}

#check @S2025FirstMissing
#check @S2025FirstMissing_iff_S2022FirstMissing
#check @S2025QuotientReceiver.root
#check @S2025Receiver_stackyPoint
#check @S2025Receiver_not_representable
#check @S2025Receiver_originEndEquiv
#check @S2025PrestackStackification.toS2022FirstMissing
#check @S2025StackyPoint.toS1994StackyOrbicurve

example (h : S2025FirstMissing K l) : S1997RootStackificationMissing K l :=
  S2025FirstMissing_implies_S1997 h

example (h : S2025PrestackStackification.{u}) : S2022FirstMissing (K := K) (l := l) :=
  h.toS2022FirstMissing (K := K) (l := l)

example (R : S2025QuotientReceiver K l) :
    ∃ (U : Iut.SchemeOverField K)
      (X : R.quotient.obj (LocallyDiscrete.mk (Opposite.op U)))
      (f : End X), f ≠ 𝟙 X ∧ f ^ l.value = 𝟙 X :=
  S2025Receiver_stackyPoint R

#print axioms S2025FirstMissing_iff_S2022FirstMissing
#print axioms S2025PrestackStackification.toS2022FirstMissing
#print axioms S2025Receiver_stackyPoint

end