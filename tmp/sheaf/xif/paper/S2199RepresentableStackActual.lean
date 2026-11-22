import tmp.sheaf.xif.paper.S2193D6RealizationModelActual
import tmp.sheaf.xif.paper.S1419D6NonterminalStackActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2199RepresentableStackActual

open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility
open LeanFormal.IUT.XiFPaper.S2193D6RealizationModelActual
open LeanFormal.IUT.XiFPaper.S2188D6RealizationActual
open LeanFormal.IUT.N8Closure.DiscreteSheafIsStack
open LeanFormal.IUT.N8Closure.RepresentableStackIsStackConstructed
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual

universe u

variable {l : PrimeGeFive}

/-- The representable etale pseudofunctor is an etale stack: the tree's
discrete-sheaf-to-stack bridge plus representable presheaf is a sheaf. -/
theorem s2199_representable_isStack
    (F : Type u) [Field F] (X : Iut.SchemeOverField F) :
    (Iut.schemeRepresentableEtalePseudofunctor F X).IsStack
      (Iut.SchemeOverField.etaleTopology F) := by
  have hP : Presieve.IsSheaf (Iut.SchemeOverField.etaleTopology F) (yoneda.obj X) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (representableEtalePresheaf_isSheaf (F := F) X)
  change (discretePseudo (C := Iut.SchemeOverField F) (yoneda.obj X)).IsStack
    (Iut.SchemeOverField.etaleTopology F)
  exact DiscreteSheafStack.discretePseudo_isStack (P := yoneda.obj X) hP

/-- S2193's representable fiber is definitionally this pseudofunctor, so its
IsStack obligation is closed. -/
theorem s2199_s2193RepresentableIsStack
    (F : Type u) [Field F] (X : Iut.SchemeOverField F) :
    S2193RepresentableIsStack F X := by
  change (Iut.schemeRepresentableEtalePseudofunctor F X).IsStack
    (Iut.SchemeOverField.etaleTopology F)
  exact s2199_representable_isStack F X

/-- Actual representable stack candidate: any scheme over F now supplies the
IsStack field. -/
noncomputable def s2199RepresentableStack
    (F : Type u) [Field F] (X : Iut.SchemeOverField F) :
    S2193RepresentableStack F where
  scheme := X
  isStack := s2199_s2193RepresentableIsStack F X

/-- Remaining D6 data after IsStack is closed: nondegeneracy and the curve-point
surjection for the paper curve. -/
structure S2199D6Remaining
    (A : InitialThetaArithmeticData l) where
  scheme : Iut.SchemeOverField A.F
  nondegenerate : ¬ IsPointFiber (Iut.schemeRepresentableEtalePseudofunctor A.F scheme)
  curvePointRealization :
    ∃ f : (Iut.schemeRepresentableEtalePseudofunctor A.F scheme).obj
          (LocallyDiscrete.mk (Opposite.op (baseSchemeObject A.F))) →
        A.curve.curve.toProjective.Point, Function.Surjective f

/-- Once nondegeneracy and curve-point realization are supplied, the
representable scheme gives the actual D6 carrier; IsStack is now a theorem. -/
noncomputable def s2199D6RealizationOfRemaining
    {A : InitialThetaArithmeticData l}
    (R : S2199D6Remaining A) :
    S2188D6Realization A where
  fiber := Iut.schemeRepresentableEtalePseudofunctor A.F R.scheme
  isStack := s2199_representable_isStack A.F R.scheme
  nondegenerate := R.nondegenerate
  curvePointRealization := R.curvePointRealization

/-- Exact remaining first missing after S2199: nondegenerate representable
scheme plus curve-point surjection. -/
def S2199D6RemainingRequired
    (A : InitialThetaArithmeticData l) : Prop :=
  Nonempty (S2199D6Remaining A)

/-- The remaining proposition is definitionally its structure nonemptiness. -/
theorem s2199D6RemainingRequired_iff
    (A : InitialThetaArithmeticData l) :
    S2199D6RemainingRequired A ↔
      Nonempty (S2199D6Remaining A) :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.S2199RepresentableStackActual
end