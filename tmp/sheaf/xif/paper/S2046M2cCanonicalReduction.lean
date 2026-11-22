import tmp.sheaf.xif.paper.S2102TorsionArtinActual

-- S2046 M2c: exact canonical comparison surface.
-- The canonical map and its Prop are actual; proof/injectivity remains exact missing.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2046M2cCanonicalReduction

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2102TorsionArtinActual

variable {p : Nat} [Fact (Nat.Prime p)]
variable (U : Index p)

/-- The canonical comparison map on torsion. -/
noncomputable abbrev S2046M2cCanonicalMap :
    CommGroup.torsion (Abelianization ↥U) →*
      CommGroup.torsion (TopologicalAbelianization (localGaloisGroup p U)) :=
  torsionMap (abelianizationToTopological p U)

/-- The canonical comparison proposition, exactly S2027's M2c. -/
abbrev S2046M2cCanonicalComparisonRequired : Prop :=
  canonicalTorsionComparison p U

/-- Equivalent injectivity-only surface. -/
def S2046M2cInjectivityRequired : Prop :=
  Function.Injective (S2046M2cCanonicalMap (p := p) U)

/-- Equivalent surjectivity-only surface. -/
def S2046M2cSurjectivityRequired : Prop :=
  Function.Surjective (S2046M2cCanonicalMap (p := p) U)

/-- A precise sufficient commutator-closed condition: the closure of the
commutator subgroup equals the commutator subgroup itself. -/
def S2046M2cCommutatorClosedRequired : Prop :=
  (commutator (localGaloisGroup p U)).topologicalClosure =
    commutator (localGaloisGroup p U)

/-- The exact implication that would turn commutator-closed into M2c;
recorded as a target, not assumed. -/
def S2046M2cCommutatorToCanonical (U : Index p) : Prop :=
  S2046M2cCommutatorClosedRequired (p := p) U →
    S2046M2cCanonicalComparisonRequired (p := p) U

#check S2046M2cCanonicalMap
#check S2046M2cCanonicalComparisonRequired
#check S2046M2cInjectivityRequired
#check S2046M2cSurjectivityRequired
#check S2046M2cCommutatorClosedRequired
#check S2046M2cCommutatorToCanonical

end LeanFormal.IUT.XiFPaper.S2046M2cCanonicalReduction

end