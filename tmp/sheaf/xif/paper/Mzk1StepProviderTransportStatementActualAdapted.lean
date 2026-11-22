import tmp.sheaf.xif.paper.Mzk1StepProviderPrimeAssemblyActualAdapted

/-! # Mzk1StepProviderTransportStatementActualAdapted — f5 transport statement (real)

Real Lean (no sorry/axiom): the f5 target-transport object as an explicit statement with its
definitional equivalence to F0StepTransportInput.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1StepProviderTransportStatementActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual
open LeanFormal.IUT.XiFPaper.PaperScopeLemma24Actual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeAssemblyActualAdapted

attribute [local instance] Classical.decEq

universe u

/-- Paper object: composition transport of the 2.4 target from S' = stepSetP1 S alpha0 and
beta' = f0Map alpha0 beta back to (S,beta). -/
def F0TransportStatement : Prop :=
  forall (S : Finset (P1Point Qbar)) (beta : P1Point Qbar) (alpha0 : Qbar),
    PaperScopeLemma24Target (stepSetP1 S alpha0) (f0Map alpha0 beta) ->
      PaperScopeLemma24Target S beta

theorem f0TransportStatement_iff : F0TransportStatement ↔ F0StepTransportInput :=
  Iff.rfl

def f0TransportRows : List (String × String) :=
  [ ("F0TransportStatement", "DEFINED"), ("f0TransportStatement_iff", "PROVED (rfl)") ]

theorem f0TransportRows_length : f0TransportRows.length = 2 := rfl

#check F0TransportStatement
#check f0TransportStatement_iff

end LeanFormal.IUT.XiFPaper.Mzk1StepProviderTransportStatementActualAdapted
end
