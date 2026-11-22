import tmp.sheaf.xif.paper.S1683StackInvolutionActual

-- S1685: actual scheme endomorphism square from coord endo square.
-- Stack TwoIso/nonidentity and signAction/quotient remain exact missing.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1685StackTwoIsoActual

open CategoryTheory
open AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1653OrbicurveStackLiftActual
open LeanFormal.IUT.XiFPaper.S1670OrbicurveStackLiftActual
open LeanFormal.IUT.XiFPaper.S1674StackStrongTransActual
open LeanFormal.IUT.XiFPaper.S1683StackInvolutionActual

variable {l : PrimeGeFive}

/-- Actual scheme-level square: S1670SchemeEndo composed with itself is the
identity, from S1683CoordEndo_sq. -/
theorem S1685SchemeEndo_sq :
    S1670SchemeEndo (l := l) ≫ S1670SchemeEndo (l := l) =
      𝟙 (S1419AffineOver l) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left]
  change Spec.map (CommRingCat.ofHom
    (S1653CoordEndo (l := l)).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (S1653CoordEndo (l := l)).toRingHom) = 𝟙 _
  rw [← Spec.map_comp (f := CommRingCat.ofHom (S1653CoordEndo (l := l)).toRingHom)
    (g := CommRingCat.ofHom (S1653CoordEndo (l := l)).toRingHom)]
  rw [← CommRingCat.ofHom_comp]
  change Spec.map (CommRingCat.ofHom
    (((S1653CoordEndo (l := l)).comp (S1653CoordEndo (l := l))).toRingHom)) =
    𝟙 (Spec (CommRingCat.of (S1348CoordinateRing l)))
  have h : ((S1653CoordEndo (l := l)).comp (S1653CoordEndo (l := l))).toRingHom =
      (AlgHom.id (S1348K l) (S1348CoordinateRing l)).toRingHom :=
    congrArg AlgHom.toRingHom (S1683CoordEndo_sq (l := l))
  rw [h]
  simp

/-- Exact missing: the stack lift is not the identity. -/
def S1685StackLiftNonidentityRequired : Prop :=
  S1674StackLift (l := l) ≠ S1674IdentityHom (l := l)

/-- Exact missing: square TwoIso to the identity. -/
abbrev S1685SquareTwoIsoRequired : Type 1 :=
  Iut.HyperbolicOrbicurve.Hom.TwoIso
    (Iut.HyperbolicOrbicurve.Hom.comp
      (S1674StackLift (l := l)) (S1674StackLift (l := l)))
    (Iut.HyperbolicOrbicurve.Hom.id (S1536XF (l := l)))

abbrev S1685SignActionRequired : Type 1 :=
  Iut.OrbicurveSignAction (S1536XF (l := l))

abbrev S1685SignQuotientRequired : Type 1 :=
  Σ (action : Iut.OrbicurveSignAction (S1536XF (l := l)))
    (C : Iut.HyperbolicOrbicurve (S1280Arithmetic l).F)
    (quotient : Iut.OrbicurveSignInvariantMorphism action C),
    Iut.OrbicurveSignQuotientWitness action quotient

#check S1685SchemeEndo_sq
#check S1685StackLiftNonidentityRequired
#check S1685SquareTwoIsoRequired
#check S1685SignActionRequired
#check S1685SignQuotientRequired

end LeanFormal.IUT.XiFPaper.S1685StackTwoIsoActual

end