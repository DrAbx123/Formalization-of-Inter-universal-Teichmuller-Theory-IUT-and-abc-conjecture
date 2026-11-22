import tmp.sheaf.xif.paper.S1322ConcretePaperSourceActual
import tmp.sheaf.xif.paper.S1319OrbicurveClauseActual
import tmp.sheaf.xif.paper.S1320SectionsCuspActual
import tmp.sheaf.xif.paper.S1895OIdentificationsActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

namespace LeanFormal.IUT.XiFPaper.S2602S1322GapDependencyActual

open LeanFormal.IUT.XiFPaper.S1322ConcretePaperSourceActual
open LeanFormal.IUT.XiFPaper.S1319OrbicurveClauseActual
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual

/-- The actual S1319 orbicurve clause over the concrete Gaussian curve. -/
theorem s2602_orbicurve_actual (l : PrimeGeFive) :
    Nonempty (SourceOrbicurveClause.{0, 0, 0}) := ⟨S1319SourceOrbicurveClause l⟩

/-- The exact remaining fields of an `S1322SourceGap`: D5 torsion, D7 sections, D8 cusp.  D6 is supplied by the actual S1319 clause, and the five D9 pairs by the concrete `S1895PaperInput`. -/
structure S2602GapMissingFields (D : S1895PaperInput) where
  torsion : S1322D5Field D.l
  sections : S1322D7Field
  cusp : S1322D8Field

/-- From the missing D5/D7/D8 fields, the orbicurve D6 and the D9 pairs, produce a genuine `S1322SourceGap`. -/
noncomputable def S2602GapOfFields (D : S1895PaperInput)
    (M : S2602GapMissingFields D) : S1322SourceGap D.l where
  torsion := M.torsion
  tail :=
    { orbicurve := S1319SourceOrbicurveClause D.l
      sections := M.sections
      cusp := M.cusp
      redCompat := D.redCompat
      redCompat_proved := D.hredCompat
      torCompat := D.torCompat
      torCompat_proved := D.htorCompat
      orbCompat := D.orbCompat
      orbCompat_proved := D.horbCompat
      secCompat := D.secCompat
      secCompat_proved := D.hsecCompat
      cusCompat := D.cusCompat
      cusCompat_proved := D.hcusCompat }

/-- The concrete `OriginalInput` attached to the gap. -/
noncomputable def S2602OriginalInputOfFields (D : S1895PaperInput)
    (M : S2602GapMissingFields D) : OriginalInput.{0, 0, 0, 0, 0} D.l Unit :=
  S1322SourceGap.toOriginalInput (S2602GapOfFields D M)

/-- The first field of the gap is exactly the D5 torsion clause. -/
theorem S2602GapOfFields_torsion (D : S1895PaperInput)
    (M : S2602GapMissingFields D) :
    (S2602GapOfFields D M).torsion = M.torsion := rfl

end LeanFormal.IUT.XiFPaper.S2602S1322GapDependencyActual

end