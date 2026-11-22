import tmp.sheaf.xif.paper.S2199RepresentableStackActual
import tmp.sheaf.xif.paper.S1419D6NonterminalStackActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2205D6SchemeActual

open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility
open LeanFormal.IUT.XiFPaper.S2199RepresentableStackActual
open LeanFormal.IUT.XiFPaper.S2193D6RealizationModelActual
open LeanFormal.IUT.XiFPaper.S2188D6RealizationActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual

universe u

variable {l : PrimeGeFive}

/-! ## 1. A concrete nondegenerate representable model (S1419) -/

/-- The actual S1419 affine Gaussian representable fiber is nondegenerate.
This is a concrete model: two distinct algebra points give two sections, so the
fiber at the base test object is not a subsingleton. -/
theorem s2205_concrete_model_nondegenerate (l : PrimeGeFive) :
    ¬ IsPointFiber
      (Iut.schemeRepresentableEtalePseudofunctor (S1348K l) (S1419AffineOver l)) := by
  rintro h
  rcases S1419NonterminalFiber l with ⟨U, hU⟩
  exact hU (h U)

/-- The same concrete model is an actual etale stack. -/
theorem s2205_concrete_model_isStack (l : PrimeGeFive) :
    (Iut.schemeRepresentableEtalePseudofunctor (S1348K l) (S1419AffineOver l)).IsStack
      (Iut.SchemeOverField.etaleTopology (S1348K l)) :=
  s2199_representable_isStack (S1348K l) (S1419AffineOver l)

/-! ## 2. Exact missing for the general paper field/curve -/

/-- Exact D6 scheme obligation for the paper arithmetic field and curve:
an actual scheme over A.F, a nondegenerate representable fiber, and a
surjective realization of A.curve's projective points. -/
abbrev S2205D6SchemeRequired
    (A : InitialThetaArithmeticData l) : Type _ :=
  S2199D6Remaining A

/-- The exact obligation is definitionally S2199D6Remaining. -/
theorem s2205D6SchemeRequired_iff
    (A : InitialThetaArithmeticData l) :
    Nonempty (S2205D6SchemeRequired A) ↔
      Nonempty (S2199D6Remaining A) :=
  Iff.rfl

/-- A general D6 scheme datum supplies the actual D6 realization. -/
noncomputable def s2205D6RealizationOfScheme
    {A : InitialThetaArithmeticData l}
    (D : S2205D6SchemeRequired A) :
    S2188D6Realization A :=
  s2199D6RealizationOfRemaining D

/-- Exact first missing: scheme over A.F plus nondegeneracy and
curve-point surjection.  No inhabitant is asserted. -/
def S2205D6SchemeRequiredProp
    (A : InitialThetaArithmeticData l) : Prop :=
  Nonempty (S2205D6SchemeRequired A)

/-- Definitional restatement. -/
theorem s2205D6SchemeRequiredProp_iff
    (A : InitialThetaArithmeticData l) :
    S2205D6SchemeRequiredProp A ↔
      Nonempty (S2205D6SchemeRequired A) :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.S2205D6SchemeActual
end