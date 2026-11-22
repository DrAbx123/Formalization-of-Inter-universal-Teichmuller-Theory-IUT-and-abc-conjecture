import tmp.sheaf.xif.paper.S1359OrbifoldPiActual

-- S1382: D6 orbifold Pi exact first field.
-- S1348 gives actual curve/cover/structure-group/cusp data, but no nonpoint
-- etale stack fiber and no orbicurve fundamental-group data.  S1359 isolates
-- the exact first field.  No terminal/point fiber, no l-torsion sequence,
-- no connected-cover construction.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1382OrbifoldPiActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1319OrbicurveClauseActual
open LeanFormal.IUT.XiFPaper.S1359OrbifoldPiActual

universe u

variable (l : PrimeGeFive)

/-- Exact first field: a nonterminal hyperbolic orbicurve over K together
with its certified orbicurve fundamental-group data over G_K. -/
abbrev S1382OrbifoldPiExactFirstField : Type 1 :=
  Σ F : S1359FirstField l, S1359OrbifoldPiRemainder l F

/-- Exact first field is equivalent to the frozen S1319 orbifold-Pi data. -/
noncomputable def s1382EquivData :
    S1382OrbifoldPiExactFirstField l ≃ S1319OrbifoldPiData l :=
  (S1359OrbifoldPiDataEquiv l).symm

theorem s1382Nonempty_iff_gap :
    Nonempty (S1382OrbifoldPiExactFirstField l) ↔
      S1319OrbifoldPiGap l := by
  constructor
  · rintro ⟨⟨F, groups⟩⟩
    exact (S1359OrbifoldPiGap_iff l).mpr ⟨F, ⟨groups⟩⟩
  · intro h
    rcases (S1359OrbifoldPiGap_iff l).mp h with ⟨F, ⟨groups⟩⟩
    exact ⟨⟨F, groups⟩⟩

#check S1382OrbifoldPiExactFirstField
#check s1382EquivData
#check s1382Nonempty_iff_gap
#check S1359FirstField
#check S1359OrbifoldPiRemainder
#check S1359StackFirstField
#check S1359FirstFieldOfMissingD6
#check S1359OrbifoldPiDataOfMissingD6
#check S1359OrbifoldPiSequence

end LeanFormal.IUT.XiFPaper.S1382OrbifoldPiActual

end