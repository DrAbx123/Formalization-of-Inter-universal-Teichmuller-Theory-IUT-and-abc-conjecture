import tmp.sheaf.xif.paper.S2089StackCancellationActual
import tmp.sheaf.xif.paper.S2090StackCancellationObstructionActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S2088GMapCancellationActual
open LeanFormal.IUT.XiFPaper.S2089StackCancellationActual
open LeanFormal.IUT.XiFPaper.S2090StackCancellationObstructionActual
namespace LeanFormal.IUT.XiFPaper.S2377StackPresentationActual

universe u

/-- Fixed-morphism postcomposition cancellation: a local extra input that
would let one cancel the comparison 2-isomorphism after postcomposition by g.
This is not available in general (S2090). -/
structure S2377PostcompCancellationAt
    {X Y Z : EtaleStackOverField S1726K} (g : Y.Hom Z) : Type _ where
  cancel : forall {a b : X.Hom Y},
    Iso (Pseudofunctor.StrongTrans.vcomp a g) (Pseudofunctor.StrongTrans.vcomp b g) ->
    Iso a b

/-- The global postcomposition cancellation is exactly S2090's obstruction. -/
abbrev S2377PostcompCancellation : Type _ :=
  S2090PostcompCancellation

/-- Exact presentation obligation for stack cancellation. -/
abbrev S2377PresentationRequired : Type 1 :=
  S2089StackPresentationStatement

/-- Exact finite-etale property obligation for the presentation. -/
abbrev S2377PropertyRequired : Prop :=
  S2089StackPropertyStatement

/-- Presentation plus property give stack cancellation, and then the full
S2086 input; no S2130/S2185/S2269 is used. -/
noncomputable def S2377StackCancellationOfPresentation
    (hpres : S2377PresentationRequired) (hprop : S2377PropertyRequired) :
    S2088StackCancellation :=
  S2089StackCancellationOfPresentation hpres hprop

/-- Exact first-missing proposition of the presentation route. -/
def S2377PresentationFirstMissing : Prop :=
  Nonempty S2377PresentationRequired

/-- Definitional restatement. -/
theorem S2377PresentationFirstMissing_iff :
    S2377PresentationFirstMissing ↔ Nonempty S2377PresentationRequired :=
  Iff.rfl


noncomputable def S2377PostcompAtOfGlobal
    (h : S2377PostcompCancellation)
    {X Y Z : EtaleStackOverField S1726K} (g : Y.Hom Z) :
    S2377PostcompCancellationAt (X := X) g where
  cancel := fun {a b} e => h g e


end LeanFormal.IUT.XiFPaper.S2377StackPresentationActual
end