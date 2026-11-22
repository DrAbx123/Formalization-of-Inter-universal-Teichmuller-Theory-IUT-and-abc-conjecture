import tmp.sheaf.xif.paper.S1383RealCuspCoordinateActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S1400RealCuspCoordinateActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1320SectionsCuspActual
open LeanFormal.IUT.XiFPaper.S1330CuspEpsilonActual
open LeanFormal.IUT.XiFPaper.S1357RealCuspCoordinateActual
open LeanFormal.IUT.XiFPaper.S1383RealCuspCoordinateActual

/-- Exact first field for the D8 real cusp coordinate. -/
abbrev S1400EpsilonMap (l : PrimeGeFive)
    (S : SourceSignQuotientData (S1280Arithmetic l)) :=
  S1383EpsilonMap l S

/-- The actual q is not the cusp epsilon. -/
theorem s1400ActualQ_ne_epsilon (l : PrimeGeFive)
    (C : Theorem311Source.SourceCuspClause) :
    C.epsilon ≠ Real.log (S1320ActualQ l) :=
  S1330ActualLogQ_ne_epsilon l C

/-- The actual projective cusp point gives no positive x-coordinate. -/
theorem s1400CuspRep_x_zero (l : PrimeGeFive)
    {P : Fin 3 → (S1280Arithmetic l).F}
    (h : (⟦P⟧ : WeierstrassCurve.Projective.PointClass (S1280Arithmetic l).F) =
      ⟦![0, 1, 0]⟧) :
    P 0 = 0 :=
  S1330CuspRep_x_zero l h

/-- Exact missing object: a real coordinate map on the paper cusp, with the
positivity/nonzero/cuspScale/compatibility data.  No inhabitant is asserted. -/
def s1400RealCuspCoordinateRequired
    (l : PrimeGeFive)
    (S : SourceSignQuotientData (S1280Arithmetic l)) : Prop :=
  S1330RealCuspCoordinateMissing l S

/-- Sign-quotient/cusp input is actual as a carrier; the coordinate function
is the exact first field. -/
theorem s1400PaperCuspCarrier_actual (l : PrimeGeFive)
    (S : SourceSignQuotientData (S1280Arithmetic l)) :
    S1400EpsilonMap l S = (S1330PaperCusp l S → Real) := rfl

end LeanFormal.IUT.XiFPaper.S1400RealCuspCoordinateActual

end
