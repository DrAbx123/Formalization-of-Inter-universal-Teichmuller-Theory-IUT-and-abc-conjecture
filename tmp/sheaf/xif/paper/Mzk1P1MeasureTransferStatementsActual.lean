import tmp.sheaf.xif.paper.Mzk1StepProviderPrimeActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # Mzk1P1MeasureTransferStatementsActual — statement layer for the P1 measure transfer

Real Lean statements (no sorry/axiom) for the P1-degree-measure transfer needed by the
Problem C step provider: non-increase of maxDegP and strict lex decrease of
(maxDegP,numMaxP) for the concrete f0 step target stepSetP1.  These are the paper-level
objects; the finite-part counting proof is the remaining named input.  Registry 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1MeasureTransferStatementsActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual

attribute [local instance] Classical.decEq

universe u

/-- Paper object: the f0 step target does not increase the P1 maximal degree. -/
def P1MaxDegNonIncrease : Prop :=
  forall (S : Finset (P1Point Qbar)) (alpha0 : Qbar),
    1 < maxDegP S -> degQ alpha0 = maxDegP S ->
      maxDegP (stepSetP1 S alpha0) <= maxDegP S

/-- Paper object: the f0 step target strictly decreases the lexicographic P1 measure. -/
def P1MeasureStrictDecrease : Prop :=
  forall (S : Finset (P1Point Qbar)) (alpha0 : Qbar),
    1 < maxDegP S -> degQ alpha0 = maxDegP S ->
      Prod.Lex (· < ·) (· < ·)
        (maxDegP (stepSetP1 S alpha0), numMaxP (stepSetP1 S alpha0))
        (maxDegP S, numMaxP S)

/-- Paper object: the finite maxDeg part of the transfer (PROVED elsewhere for stepSet). -/
def FiniteMaxDegNonIncrease : Prop :=
  forall (S : Finset Qbar) (alpha0 : Qbar), alpha0 ∈ S -> degQ alpha0 = maxDeg S ->
    maxDeg (stepSet S alpha0) <= maxDeg S

/-- Row record. -/
def p1MeasureRows : List (String × String) :=
  [ ("P1MaxDegNonIncrease", "STATEMENT (paper object)"),
    ("P1MeasureStrictDecrease", "STATEMENT (paper object; proof = f4 gap)"),
    ("FiniteMaxDegNonIncrease", "STATEMENT; proved as maxDeg_stepSet_le") ]

theorem p1MeasureRows_length : p1MeasureRows.length = 3 := rfl

#check P1MaxDegNonIncrease
#check P1MeasureStrictDecrease
#check FiniteMaxDegNonIncrease

end LeanFormal.IUT.XiFPaper.Mzk1P1MeasureTransferStatementsActual
end
