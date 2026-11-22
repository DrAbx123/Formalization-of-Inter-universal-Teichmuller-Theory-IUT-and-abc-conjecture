import tmp.sheaf.xif.paper.S1382OrbifoldPiActual
import tmp.sheaf.xif.paper.S1348D6OrbicurveActual

/-! # S1398: D6 supply assembly

Consumer: the D6 supply of Definition 3.1(d).  This file assembles the actual
S1348 degree-two cover clause with the S1359/S1382 exact first field
(nonterminal hyperbolic orbicurve + certified orbifold fundamental-group data)
and the S1319 orbifold-Pi record.  The exact first field is

```text
Sigma D : MissingD6GeometricRealization K,
  OrbicurveFundamentalGroupData (S1359FirstFieldOfMissingD6 D) G_K
```

with the actual D6 curve equal to the S1280 Gaussian curve.  No terminal or
point fiber is used; S1359's nondegeneracy is the non-point condition.
Conditional on this field, the clause, the stack fiber and the orbifold Pi
are actual objects; no l-torsion sequence is used as the orbifold Pi. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1398D6SupplyActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1319OrbicurveClauseActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1359OrbifoldPiActual
open LeanFormal.IUT.XiFPaper.S1382OrbifoldPiActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility

variable (l : PrimeGeFive)

/-- Conditional D6 supply: an actual non-point D6 realization, its certified
orbifold fundamental-group data, and the matching S1280 curve. -/
structure S1398D6Supply where
  D : MissingD6GeometricRealization (S1359K l)
  curve_eq : D.curve = (S1280Arithmetic l).curve
  groups : S1359OrbifoldPiRemainder l (S1359FirstFieldOfMissingD6 l D)

namespace S1398D6Supply

variable (S : S1398D6Supply l)

/-- The exact first field of the supply. -/
noncomputable def firstField : S1359FirstField l :=
  S1359FirstFieldOfMissingD6 l S.D

/-- The exact stack field of the supply. -/
noncomputable def stack : S1359StackFirstField l :=
  S1359StackFirstFieldOfFirstField l S.firstField

/-- The S1319 orbifold-Pi record assembled from the exact first field. -/
noncomputable def orbifoldPi : S1319OrbifoldPiData l :=
  S1359OrbifoldPiDataOfMissingD6 l S.D S.groups

/-- The actual S1348 degree-two-cover SourceOrbicurveClause.  Its geometric
fields are the S1348 actual cover/structure group/cusp data; its exact sequence
is the one induced by the orbifold groups of the supply. -/
noncomputable def clause : SourceOrbicurveClause.{0, 0, 0} :=
  S1348ClauseOfFirstField l ⟨S.firstField.X, S.groups⟩

@[simp] theorem clause_cover :
    S.clause.cover = S1348Cover l := rfl

@[simp] theorem clause_structureGroup :
    S.clause.structureGroup = S1348StructureGroup l := rfl

@[simp] theorem clause_cuspCount : S.clause.cuspCount = S1348CuspCount := rfl

@[simp] theorem orbifoldPi_X : S.orbifoldPi.X = S.firstField.X := rfl

theorem orbifoldPi_nonterminal : S1319NonterminalFiber S.orbifoldPi.X :=
  S.orbifoldPi.nonterminal

@[simp] theorem stack_fiber : S.stack.fiber = S.D.fiber := rfl

end S1398D6Supply

/-- The exact first field of the D6 supply. -/
abbrev S1398D6ExactFirstField : Type 1 :=
  Σ D : MissingD6GeometricRealization (S1359K l),
    S1359OrbifoldPiRemainder l (S1359FirstFieldOfMissingD6 l D)

end LeanFormal.IUT.XiFPaper.S1398D6SupplyActual
end
