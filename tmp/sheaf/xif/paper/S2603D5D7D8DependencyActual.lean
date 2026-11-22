import tmp.sheaf.xif.paper.S1298TorsionClauseActual
import tmp.sheaf.xif.paper.S1320SectionsCuspActual
import tmp.sheaf.xif.paper.S2602S1322GapDependencyActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

namespace LeanFormal.IUT.XiFPaper.S2603D5D7D8DependencyActual

open LeanFormal.IUT.XiFPaper.S1298TorsionClauseActual
open LeanFormal.IUT.XiFPaper.S1320SectionsCuspActual
open LeanFormal.IUT.XiFPaper.S2602S1322GapDependencyActual
open LeanFormal.IUT.InitialThetaSource.Definition31D4D9Supply

/-- D5 first field: every torsion gap supplies a rank-two basis. -/
theorem s2603_d5_firstField (l : PrimeGeFive)
    (G : S1298TorsionSourceGap l) : Nonempty (S1298TorsionBasisType l) :=
  s1298TorsionSourceGap_firstField l G

/-- D6 is actual: the S1319 orbicurve clause exists over every `l`. -/
theorem s2603_d6_actual (l : PrimeGeFive) :
    Nonempty (SourceOrbicurveClause.{0, 0, 0}) :=
  s2602_orbicurve_actual l

/-- D7 exact decomposition: first field `localGroupCarrier` plus the S1320 tail. -/
theorem s2603_d7_decomp (l : PrimeGeFive) :
    Nonempty (D7LocalGroupSectionSupply.{0, 0} (S1320Layer l)) ↔
      ∃ G0 : S1320D7FirstField l, Nonempty (S1320D7Tail l G0) :=
  S1320D7Supply_nonempty_iff_firstField_tail l

/-- D8 exact decomposition: first field `epsilon : Real` plus the S1320 tail. -/
theorem s2603_d8_decomp :
    Nonempty SourceCuspClause ↔
      ∃ e : S1320CuspFirstField, Nonempty (S1320CuspTail e) :=
  S1320CuspClause_nonempty_iff_firstField_tail

end LeanFormal.IUT.XiFPaper.S2603D5D7D8DependencyActual

end