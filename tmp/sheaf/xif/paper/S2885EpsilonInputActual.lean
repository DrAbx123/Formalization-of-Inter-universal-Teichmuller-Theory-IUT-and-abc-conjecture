import tmp.sheaf.xif.paper.S2873CuspGenericActual
import tmp.sheaf.xif.paper.S2880CorrectedA6CoreNontrivialActual

noncomputable section
open LeanFormal.IUT
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2885EpsilonInputActual

universe u
variable {F : Type u} [Field F]

/-- Packaged generic cusp input for an arbitrary cK: exactly the
GenericCuspData fields, with no data invented. -/
structure S2885EpsilonInput (X : Iut.HyperbolicOrbicurve F) where
  data : LeanFormal.IUT.XiFPaper.S2873CuspGenericActual.GenericCuspData X

/-- Convert the packaged input to the literal epsilon field. -/
noncomputable def S2885EpsilonInput.toCusp {X : Iut.HyperbolicOrbicurve F}
    (I : S2885EpsilonInput X) : Iut.OrbicurveBoundaryCusp X :=
  LeanFormal.IUT.XiFPaper.S2873CuspGenericActual.cuspOfGenericData I.data

/-- Conversely, any actual cusp packages as a generic input. -/
noncomputable def S2885EpsilonInput.ofCusp {X : Iut.HyperbolicOrbicurve F}
    (c : Iut.OrbicurveBoundaryCusp X) : S2885EpsilonInput X :=
  ⟨{ compactification := c.compactification,
     openMap := c.openMap,
     openImmersion := c.openImmersion,
     residueScheme := c.residueScheme,
     point := c.point,
     isBoundary := c.isBoundary }⟩

/-- The packaged input is equivalent to the literal cusp type. -/
theorem S2885EpsilonInput.nonempty_iff {X : Iut.HyperbolicOrbicurve F} :
    Nonempty (S2885EpsilonInput X) ↔
      Nonempty (Iut.OrbicurveBoundaryCusp X) := by
  constructor
  · rintro ⟨I⟩
    exact ⟨I.toCusp⟩
  · rintro ⟨c⟩
    exact ⟨ofCusp c⟩

/-- Specialization to the A6 K-side cK: the epsilon field of S2880/S2876 can
be filled from a packaged generic cusp input. -/
noncomputable def S2885A6Epsilon
    (cK : Iut.HyperbolicOrbicurve LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual.S2847A6.K)
    (I : S2885EpsilonInput cK) : Iut.OrbicurveBoundaryCusp cK :=
  I.toCusp

#check S2885EpsilonInput
#check S2885EpsilonInput.toCusp
#check S2885EpsilonInput.ofCusp
#check S2885EpsilonInput.nonempty_iff


/-- Replace the explicit epsilon field of an S2880 input by the packaged
generic cusp input (same cK, no other field changed). -/
noncomputable def S2885WithEpsilon
    {signAction : Iut.OrbicurveSignAction
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve}
    (I : LeanFormal.IUT.XiFPaper.S2880CorrectedA6CoreNontrivialActual.S2880Inputs signAction)
    (J : S2885EpsilonInput I.cK) :
    LeanFormal.IUT.XiFPaper.S2880CorrectedA6CoreNontrivialActual.S2880Inputs signAction :=
  { I with epsilon := J.toCusp }

/-- Same replacement for the S2876 core inputs. -/
noncomputable def S2885WithEpsilon2876
    {signAction : Iut.OrbicurveSignAction
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve}
    (I : LeanFormal.IUT.XiFPaper.S2876CorrectedA6CoreActual.S2876Inputs signAction)
    (J : S2885EpsilonInput I.cK) :
    LeanFormal.IUT.XiFPaper.S2876CorrectedA6CoreActual.S2876Inputs signAction :=
  { I with epsilon := J.toCusp }

#check S2885WithEpsilon
#check S2885WithEpsilon2876

#check S2885A6Epsilon
#print axioms S2885EpsilonInput.toCusp
#print axioms S2885EpsilonInput.nonempty_iff

end LeanFormal.IUT.XiFPaper.S2885EpsilonInputActual
end