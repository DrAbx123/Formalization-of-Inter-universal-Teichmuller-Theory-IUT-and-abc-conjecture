import tmp.sheaf.xif.paper.S1357RealCuspCoordinateActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S1383RealCuspCoordinateActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1320SectionsCuspActual
open LeanFormal.IUT.XiFPaper.S1330CuspEpsilonActual
open LeanFormal.IUT.XiFPaper.S1357RealCuspCoordinateActual

/-- Exact first-field type: a real-valued epsilon map on the actual paper
cusp. -/
abbrev S1383EpsilonMap (l : PrimeGeFive)
    (S : SourceSignQuotientData (S1280Arithmetic l)) :=
  S1357EpsilonMap l S

/-- The actual q is not the cusp epsilon. -/
theorem s1383ActualQ_ne_epsilon (l : PrimeGeFive)
    (C : Theorem311Source.SourceCuspClause) :
    C.epsilon ≠ Real.log (S1320ActualQ l) :=
  S1330ActualLogQ_ne_epsilon l C

/-- The projective actual cusp point has zero x-coordinate, so it gives no
positive x epsilon. -/
theorem s1383CuspRep_x_zero (l : PrimeGeFive)
    {P : Fin 3 → (S1280Arithmetic l).F}
    (h : (⟦P⟧ : WeierstrassCurve.Projective.PointClass (S1280Arithmetic l).F) =
      ⟦![0, 1, 0]⟧) :
    P 0 = 0 :=
  S1330CuspRep_x_zero l h

/-- Exact first field: epsilonOf plus positivity/nonzero/cuspScale/compat.
No inhabitant is asserted. -/
def s1383RealCuspCoordinateRequired
    (l : PrimeGeFive)
    (S : SourceSignQuotientData (S1280Arithmetic l)) : Prop :=
  S1330RealCuspCoordinateMissing l S

/-- Conditional construction is already the S1357 exact constructor; this
file uses it rather than duplicating it. -/
theorem s1383ConditionalConstructorAvailable
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (R : S1330RealCuspCoordinate l S) (c : S1330PaperCusp l S) :
    (S1330CuspClauseOfRealCuspCoordinate R c).epsilon = R.epsilonOf c :=
  rfl

end LeanFormal.IUT.XiFPaper.S1383RealCuspCoordinateActual

end
