import tmp.sheaf.xif.paper.S2089StackCancellationActual
import tmp.sheaf.xif.paper.S2090StackCancellationObstructionActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open AlgebraicGeometry
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S2088GMapCancellationActual
open LeanFormal.IUT.XiFPaper.S2089StackCancellationActual
open LeanFormal.IUT.XiFPaper.S2090StackCancellationObstructionActual
namespace LeanFormal.IUT.XiFPaper.S2374StackCancellationActual

abbrev S2374PresentationRequired : Type 1 :=
  S2089StackPresentationStatement

abbrev S2374PropertyRequired : Prop :=
  S2089StackPropertyStatement

noncomputable def S2374StackCancellationOfPresentation
    (hpres : S2374PresentationRequired) (hprop : S2374PropertyRequired) :
    S2088StackCancellation :=
  S2089StackCancellationOfPresentation hpres hprop

theorem S2374SchemeCancellation {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Etale (f ≫ g)] [LocallyOfFiniteType g] [FormallyUnramified g]
    [IsFinite (f ≫ g)] [IsSeparated g] :
    Etale f ∧ IsFinite f :=
  S2088_scheme_finiteEtale_cancel f g

abbrev S2374PostcompObstruction : Type _ :=
  S2090PostcompCancellation

def S2374StackCancellationFirstMissing : Prop :=
  Nonempty S2374PresentationRequired

theorem S2374StackCancellationFirstMissing_iff :
    S2374StackCancellationFirstMissing ↔
      Nonempty S2374PresentationRequired :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.S2374StackCancellationActual
end