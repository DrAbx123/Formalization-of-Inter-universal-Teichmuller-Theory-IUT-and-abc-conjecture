import tmp.sheaf.xif.paper.S1330CuspEpsilonActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S1357RealCuspCoordinateActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1320SectionsCuspActual
open LeanFormal.IUT.XiFPaper.S1330CuspEpsilonActual

/-- The faithful paper cusp carrier for S1330/S1357. -/
abbrev S1357PaperCusp (l : PrimeGeFive)
    (S : SourceSignQuotientData (S1280Arithmetic l)) : Type 1 :=
  S1330PaperCusp l S

/-- Exact first field of a real cusp coordinate: a real-valued epsilon map on
the actual paper cusp.  This is a type, not a Prop placeholder. -/
abbrev S1357EpsilonMap (l : PrimeGeFive)
    (S : SourceSignQuotientData (S1280Arithmetic l)) :=
  S1357PaperCusp l S → Real

/-- Conditional actual construction of the exact real cusp coordinate from
its first field and the required positivity/nonzero/cuspScale data. -/
noncomputable def s1357RealCuspCoordinateOfMap
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (epsilonOf : S1357EpsilonMap l S)
    (heps_pos : ∀ c, 0 < epsilonOf c)
    (heps_ne : ∀ c, epsilonOf c ≠ 0)
    (cuspScaleOf : S1357PaperCusp l S → Real)
    (hscale_pos : ∀ c, 0 < cuspScaleOf c)
    (heps_scale : ∀ c, epsilonOf c * cuspScaleOf c ≠ 0)
    (compat : S1357PaperCusp l S → Prop)
    (hcompat : ∀ c, compat c) :
    S1330RealCuspCoordinate l S where
  epsilonOf := epsilonOf
  epsilon_positive := heps_pos
  epsilon_nonzero := heps_ne
  cuspScaleOf := cuspScaleOf
  cuspScale_positive := hscale_pos
  epsilon_scale_relation := heps_scale
  epsilon_compatibility := compat
  epsilon_compatibility_proved := hcompat

/-- The actual q cannot be the cusp epsilon (reused S1330 fact). -/
theorem s1357ActualQ_ne_epsilon (l : PrimeGeFive) (C : Theorem311Source.SourceCuspClause) :
    C.epsilon ≠ Real.log (S1320ActualQ l) :=
  S1330ActualLogQ_ne_epsilon l C

/-- The actual projective cusp point has no positive x-coordinate. -/
theorem s1357CuspRep_x_zero (l : PrimeGeFive)
    {P : Fin 3 → (S1280Arithmetic l).F}
    (h : (⟦P⟧ : WeierstrassCurve.Projective.PointClass (S1280Arithmetic l).F) =
      ⟦![0, 1, 0]⟧) :
    P 0 = 0 :=
  S1330CuspRep_x_zero l h

/-- Exact missing object remains S1330RealCuspCoordinate; no inhabitant is
asserted.  The first field is S1357EpsilonMap plus its positivity data. -/
def s1357RealCuspCoordinateRequired
    (l : PrimeGeFive)
    (S : SourceSignQuotientData (S1280Arithmetic l)) : Prop :=
  Nonempty (S1330RealCuspCoordinate l S)

end LeanFormal.IUT.XiFPaper.S1357RealCuspCoordinateActual

end
