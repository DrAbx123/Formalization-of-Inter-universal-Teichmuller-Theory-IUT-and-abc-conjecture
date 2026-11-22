import tmp.sheaf.xif.paper.S2171SourceCompletionActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36OrbicurveFeasibility
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2177SignQuotientDataActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility
open LeanFormal.IUT.XiFPaper.S2171SourceCompletionActual

universe u

variable {l : PrimeGeFive}

/-! ## 1. Exact nondegenerate orbicurve realization -/

/-- The actual nondegenerate D6 geometric realization whose curve is the paper
arithmetic curve.  This is the exact input needed for xF and xF_geometry; no
inhabitant is constructed. -/
structure S2177ActualD6Orbicurve
    (A : InitialThetaArithmeticData l) where
  D : MissingD6GeometricRealization A.F
  curve_eq : D.curve = A.curve

/-- A D6 realization gives a hyperbolic orbicurve with the source signature. -/
theorem s2177_exists_hyperbolicOrbicurve
    {A : InitialThetaArithmeticData l}
    (D : S2177ActualD6Orbicurve A) :
    ∃ xF : Iut.HyperbolicOrbicurve A.F,
      xF.signature = sourceTypeOneOne := by
  obtain ⟨xF, hxF⟩ := D.D.exists_oncePuncturedHyperbolicOrbicurve
  refine ⟨xF, ?_⟩
  rw [hxF]
  rfl

/-- A D6 realization gives the actual once-punctured geometry field for its own
curve. -/
theorem s2177_exists_xF_geometry
    {A : InitialThetaArithmeticData l}
    (D : S2177ActualD6Orbicurve A) :
    ∃ xF : Iut.HyperbolicOrbicurve A.F,
      Nonempty (SourceOncePuncturedGeometry D.D.curve xF) := by
  obtain ⟨xF, hxF⟩ := D.D.exists_oncePuncturedHyperbolicOrbicurve
  refine ⟨xF, ⟨{ signature := ?_ }⟩⟩
  show xF.signature = sourceTypeOneOne
  rw [hxF]
  rfl

/-- The same geometry transported to the paper arithmetic curve, using the
explicit curve equality field. -/
theorem s2177_exists_xF_geometry_for_arithmetic
    {A : InitialThetaArithmeticData l}
    (D : S2177ActualD6Orbicurve A) :
    ∃ xF : Iut.HyperbolicOrbicurve A.F,
      Nonempty (SourceOncePuncturedGeometry A.curve xF) := by
  obtain ⟨xF, ⟨G⟩⟩ := s2177_exists_xF_geometry D
  exact ⟨xF, ⟨D.curve_eq ▸ G⟩⟩

/-! ## 2. Exact first missing -/

/-- Exact target: a nondegenerate etale-stack realization of the paper
once-punctured elliptic curve, with the curve identification. -/
def S2177ActualD6OrbicurveRequired
    (A : InitialThetaArithmeticData l) : Prop :=
  Nonempty (S2177ActualD6Orbicurve A)

/-- The exact first missing is definitionally the nondegenerate D6 realization. -/
theorem s2177ActualD6OrbicurveRequired_iff
    (A : InitialThetaArithmeticData l) :
    S2177ActualD6OrbicurveRequired A ↔
      Nonempty (S2177ActualD6Orbicurve A) :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.S2177SignQuotientDataActual
end