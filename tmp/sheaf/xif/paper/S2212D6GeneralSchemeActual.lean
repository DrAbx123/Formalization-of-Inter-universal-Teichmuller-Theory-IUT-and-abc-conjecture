import tmp.sheaf.xif.paper.S2205D6SchemeActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2212D6GeneralSchemeActual

open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility
open LeanFormal.IUT.XiFPaper.S2205D6SchemeActual
open LeanFormal.IUT.XiFPaper.S2199RepresentableStackActual
open LeanFormal.IUT.XiFPaper.S2193D6RealizationModelActual
open LeanFormal.IUT.XiFPaper.S2188D6RealizationActual

universe u

variable {l : PrimeGeFive}

/-! ## 1. Two distinct sections imply nondegeneracy -/

/-- A scheme over A.F with two distinct A.F-sections. -/
structure S2212TwoPointScheme
    (A : InitialThetaArithmeticData l) where
  X : Iut.SchemeOverField A.F
  s1 : baseSchemeObject A.F ⟶ X
  s2 : baseSchemeObject A.F ⟶ X
  s1_ne_s2 : s1 ≠ s2

/-- Two distinct sections exclude the point-fiber condition for the
representable pseudofunctor. -/
theorem s2212_twoPoint_nondegenerate
    {A : InitialThetaArithmeticData l}
    (D : S2212TwoPointScheme A) :
    ¬ IsPointFiber
      (Iut.schemeRepresentableEtalePseudofunctor A.F D.X) := by
  intro h
  have hbase := h (Opposite.op (baseSchemeObject A.F))
  change Subsingleton (Discrete (baseSchemeObject A.F ⟶ D.X)) at hbase
  haveI := hbase
  have hs : (Discrete.mk D.s1 : Discrete (baseSchemeObject A.F ⟶ D.X)) =
      Discrete.mk D.s2 := Subsingleton.elim _ _
  exact D.s1_ne_s2 (congrArg Discrete.as hs)

/-! ## 2. D6 from a two-point scheme plus curve points -/

/-- A two-point scheme plus a surjective realization of the paper curve's
projective points. -/
structure S2212GeneralD6Scheme
    (A : InitialThetaArithmeticData l) where
  twoPoint : S2212TwoPointScheme A
  curvePointRealization :
    ∃ f : (Iut.schemeRepresentableEtalePseudofunctor A.F twoPoint.X).obj
          (LocallyDiscrete.mk (Opposite.op (baseSchemeObject A.F))) →
        A.curve.curve.toProjective.Point, Function.Surjective f

/-- Such a scheme gives the exact S2199 D6 remaining data. -/
noncomputable def s2212D6RemainingOfGeneral
    {A : InitialThetaArithmeticData l}
    (D : S2212GeneralD6Scheme A) :
    S2199D6Remaining A where
  scheme := D.twoPoint.X
  nondegenerate := s2212_twoPoint_nondegenerate D.twoPoint
  curvePointRealization := D.curvePointRealization

/-- Exact first-missing proposition for the general scheme route. -/
def S2212GeneralD6SchemeRequired
    (A : InitialThetaArithmeticData l) : Prop :=
  Nonempty (S2212GeneralD6Scheme A)

/-- The proposition is definitionally the nonemptiness of the general scheme
datum. -/
theorem s2212GeneralD6SchemeRequired_iff
    (A : InitialThetaArithmeticData l) :
    S2212GeneralD6SchemeRequired A ↔
      Nonempty (S2212GeneralD6Scheme A) :=
  Iff.rfl

/-- The abstract two-point component alone supplies nondegeneracy; it does not
supply the curve-point realization. -/
def S2212TwoPointSchemeRequired
    (A : InitialThetaArithmeticData l) : Prop :=
  Nonempty (S2212TwoPointScheme A)

end LeanFormal.IUT.XiFPaper.S2212D6GeneralSchemeActual
end
