import tmp.sheaf.xif.paper.Mzk1NestedInductionActual
import tmp.sheaf.xif.paper.Mzk1StepProviderPrimeActual

/-! # Mzk1F4bFiniteReuseActual — finite-version reuse record for the f4b P1 numMax gap

A475: the finite-part count ingredients of the f4b gap already exist in
Mzk1NestedInductionActual (numMaxP at :612, numMaxP_image_ofFinite at :661,
maxDeg_stepSet_le/numMax_stepSet_lt).  This file states, as explicit Prop objects, the
finite and P1 transfer statements and records the existing declarations by name, without
copying theory and without asserting the missing P1-step bound.  No sorry/axiom. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1F4bFiniteReuseActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual

attribute [local instance] Classical.decEq

universe u

/-- Paper object (finite part): the step target does not increase the finite max degree. -/
def FiniteMaxDegTransferStatement : Prop :=
  forall (S : Finset Qbar) (alpha0 : Qbar), alpha0 ∈ S -> degQ alpha0 = maxDeg S ->
    maxDeg (stepSet S alpha0) <= maxDeg S

/-- Paper object (finite part): on the stable-max-degree branch the finite max count drops. -/
def FiniteNumMaxStrictStatement : Prop :=
  forall (S : Finset Qbar) (alpha0 : Qbar), alpha0 ∈ S -> degQ alpha0 = maxDeg S ->
    numMax (stepSet S alpha0) < numMax S

/-- Paper object (P1 part, the A475 repo-current missing item): the concrete step target
strictly decreases the P1 lexicographic measure. -/
def P1MeasureTransferStatement : Prop :=
  forall (S : Finset P1Point Qbar) (alpha0 : Qbar), 1 < maxDegP S -> degQ alpha0 = maxDegP S ->
    Prod.Lex (· < ·) (· < ·)
      (maxDegP (stepSetP1 S alpha0), numMaxP (stepSetP1 S alpha0))
      (maxDegP S, numMaxP S)

/-- Row record: reuse evidence (existing finite declarations vs missing P1 transfer). -/
def f4bFiniteReuseRows : List (String × String) :=
  [ ("FiniteMaxDegTransferStatement", "reuse: maxDeg_stepSet_le (Mzk1NestedInductionActual)"),
    ("FiniteNumMaxStrictStatement", "reuse: numMax_stepSet_lt (Mzk1NestedInductionActual)"),
    ("P1MeasureTransferStatement", "repo-current missing (A475 evidence; P1 step counting)") ]

theorem f4bFiniteReuseRows_length : f4bFiniteReuseRows.length = 3 := rfl

#check numMaxP
#check numMaxP_image_ofFinite
#check FiniteMaxDegTransferStatement
#check P1MeasureTransferStatement

end LeanFormal.IUT.XiFPaper.Mzk1F4bFiniteReuseActual
end
