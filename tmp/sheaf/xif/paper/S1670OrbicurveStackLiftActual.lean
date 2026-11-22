import tmp.sheaf.xif.paper.S1653OrbicurveStackLiftActual

-- S1670: actual scheme endomorphism of S1419AffineOver from the coordinate
-- [-1] endomorphism; the StrongTrans stack lift is the exact first missing.
-- No fake StrongTrans/signAction/quotient.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1670OrbicurveStackLiftActual

open CategoryTheory
open AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1653OrbicurveStackLiftActual

variable {l : PrimeGeFive}

theorem S1670CoordEndo_comp_algebraMap :
    (S1653CoordEndo (l := l)).toRingHom.comp
      (algebraMap (S1348K l) (S1348CoordinateRing l)) =
      algebraMap (S1348K l) (S1348CoordinateRing l) := by
  ext a
  exact (S1653CoordEndo (l := l)).commutes a

/-- Actual scheme endomorphism of the S1419 affine scheme over F, induced by
the coordinate [-1] endomorphism x |-> x, y |-> -x-y. -/
noncomputable def S1670SchemeEndo :
    S1419AffineOver l ⟶ S1419AffineOver l :=
  Over.homMk (Spec.map (CommRingCat.ofHom (S1653CoordEndo (l := l)).toRingHom)) (by
    dsimp [S1419AffineOver]
    erw [← Spec.map_comp, ← CommRingCat.ofHom_comp, S1670CoordEndo_comp_algebraMap])

/-- The actual identity endomorphism. -/
noncomputable def S1670IdentityHom :
    (S1536XF (l := l)).Hom (S1536XF (l := l)) :=
  Iut.HyperbolicOrbicurve.Hom.id (S1536XF (l := l))

/-- Exact first missing: the nontrivial StrongTrans stack lift. -/
abbrev S1670MissingStrongTrans : Type 1 :=
  (S1536XF (l := l)).Hom (S1536XF (l := l))

abbrev S1670MissingNontrivialLift : Type 1 :=
  { f : S1670MissingStrongTrans (l := l) //
      f ≠ S1670IdentityHom (l := l) }

/-- Exact missing square condition for a stack lift f. -/
abbrev S1670SquareTwoIsoRequired
    (f : S1670MissingStrongTrans (l := l)) : Type 1 :=
  Iut.HyperbolicOrbicurve.Hom.TwoIso
    (Iut.HyperbolicOrbicurve.Hom.comp f f)
    (Iut.HyperbolicOrbicurve.Hom.id (S1536XF (l := l)))

/-- Missing sign action/quotient targets. -/
abbrev S1670SignActionRequired : Type 1 :=
  Iut.OrbicurveSignAction (S1536XF (l := l))

abbrev S1670SignQuotientRequired : Type 1 :=
  Σ (action : Iut.OrbicurveSignAction (S1536XF (l := l)))
    (C : Iut.HyperbolicOrbicurve (S1280Arithmetic l).F)
    (quotient : Iut.OrbicurveSignInvariantMorphism action C),
    Iut.OrbicurveSignQuotientWitness action quotient

#check S1670SchemeEndo
#check S1670IdentityHom
#check S1670MissingStrongTrans
#check S1670MissingNontrivialLift
#check S1670SquareTwoIsoRequired
#check S1670SignActionRequired
#check S1670SignQuotientRequired

end LeanFormal.IUT.XiFPaper.S1670OrbicurveStackLiftActual

end