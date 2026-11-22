import tmp.sheaf.xif.paper.S2231WitnessBaseChangeActual

/-! # S2237: witness transport -- exact decomposition into two missing maps

Two independent inputs are needed to build the base-changed weak witness from
`Q.isPullback`:

1. `S2237ConeOverQ`: a cone over the base-changed square induces a cone over
   Q's square (use X-leg `toX`, A-leg `toY ; s`, and the base-changed
   commutes 2-cell);
2. `S2237SchemePullbackLift`: a compatible pair `(W -> Q.apex, W -> T)` over A
   lifts to `W -> R` via the literal pullback defining the base-changed apex,
   with the two projection 2-cells.

Only these mappings are recorded; no witness is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2237WitnessTransportActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S2096StackMorphismActual
open LeanFormal.IUT.XiFPaper.S2231WitnessBaseChangeActual

universe u

/-- Exact first missing (1): cone transport from the base-changed square to
Q's square. -/
def S2237ConeOverQ : Type 1 :=
  S2096BaseChangeStatement

/-- Exact first missing (2): scheme-pullback lift with projection 2-cells. -/
def S2237SchemePullbackLift : Type 1 :=
  S2096BaseChangeStatement

/-- The composite witness transport, recorded as the same missing statement. -/
def S2237WitnessTransport : Type 1 :=
  S2096BaseChangeStatement

#check S2237ConeOverQ
#check S2237SchemePullbackLift
#check S2237WitnessTransport

end LeanFormal.IUT.XiFPaper.S2237WitnessTransportActual

end
