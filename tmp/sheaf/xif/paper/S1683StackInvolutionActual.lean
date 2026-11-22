import tmp.sheaf.xif.paper.S1674StackStrongTransActual

-- S1683: coordinate involution square actual; stack TwoIso/nonidentity and
-- signAction/quotient are exact missing.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1683StackInvolutionActual

open CategoryTheory
open AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1653OrbicurveStackLiftActual
open LeanFormal.IUT.XiFPaper.S1670OrbicurveStackLiftActual
open LeanFormal.IUT.XiFPaper.S1674StackStrongTransActual

variable {l : PrimeGeFive}

theorem S1683PolyEndo_sq :
    (S1653PolyEndo (l := l)).comp (S1653PolyEndo (l := l)) =
      AlgHom.id (S1348K l) (MvPolynomial (Fin 2) (S1348K l)) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [S1653PolyEndo]

theorem S1683CoordEndo_sq :
    (S1653CoordEndo (l := l)).comp (S1653CoordEndo (l := l)) =
      AlgHom.id (S1348K l) (S1348CoordinateRing l) := by
  apply Ideal.Quotient.algHom_ext
  ext a
  have h := AlgHom.congr_fun (S1683PolyEndo_sq (l := l))
    (MvPolynomial.X (R := S1348K l) a)
  simp only [AlgHom.comp_apply, AlgHom.id_apply] at h
  change Ideal.Quotient.mk _
    (S1653PolyEndo (S1653PolyEndo (MvPolynomial.X (R := S1348K l) a))) =
    Ideal.Quotient.mk _ (MvPolynomial.X (R := S1348K l) a)
  rw [h]

/-- Exact missing: the scheme endomorphism square = identity. -/
def S1683SchemeEndoSqRequired : Prop :=
  S1670SchemeEndo (l := l) ≫ S1670SchemeEndo (l := l) =
    𝟙 (S1419AffineOver l)

/-- Exact missing: the stack lift is not the identity. -/
def S1683StackLiftNonidentityRequired : Prop :=
  S1674StackLift (l := l) ≠ S1674IdentityHom (l := l)

/-- Exact missing: square TwoIso to the identity. -/
abbrev S1683SquareTwoIsoRequired : Type 1 :=
  Iut.HyperbolicOrbicurve.Hom.TwoIso
    (Iut.HyperbolicOrbicurve.Hom.comp
      (S1674StackLift (l := l)) (S1674StackLift (l := l)))
    (Iut.HyperbolicOrbicurve.Hom.id (S1536XF (l := l)))

abbrev S1683SignActionRequired : Type 1 :=
  Iut.OrbicurveSignAction (S1536XF (l := l))

abbrev S1683SignQuotientRequired : Type 1 :=
  Σ (action : Iut.OrbicurveSignAction (S1536XF (l := l)))
    (C : Iut.HyperbolicOrbicurve (S1280Arithmetic l).F)
    (quotient : Iut.OrbicurveSignInvariantMorphism action C),
    Iut.OrbicurveSignQuotientWitness action quotient

#check S1683PolyEndo_sq
#check S1683CoordEndo_sq
#check S1683SchemeEndoSqRequired
#check S1683StackLiftNonidentityRequired
#check S1683SquareTwoIsoRequired
#check S1683SignActionRequired
#check S1683SignQuotientRequired

end LeanFormal.IUT.XiFPaper.S1683StackInvolutionActual

end