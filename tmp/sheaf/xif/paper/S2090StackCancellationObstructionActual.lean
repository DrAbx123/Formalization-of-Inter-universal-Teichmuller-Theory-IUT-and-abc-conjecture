import tmp.sheaf.xif.paper.S2089StackCancellationActual

/-! # S2090: obstruction to the stack-cancellation presentation route

To build a presentation of `f` at `ptY` from presentations of `g` at
`ptY ≫ g` and of `f ≫ g`, one must cancel the postcomposition by `g` in the
comparison 2-isomorphism: from
  Iso (vcomp (vcomp xsrc f) g) (vcomp proj (vcomp ptY g))
deduce
  Iso (vcomp xsrc f) (vcomp proj ptY).
This is postcomposition cancellation of 2-isomorphisms, which is false for an
arbitrary stack morphism `g` (in Cat, postcomposition by a constant functor
loses information).  Hence `S2089StackPresentationStatement` cannot be proved
from the recorded fields alone.

The exact additional input is representability/faithfulness of the cover-map
morphisms (S2087GMapFiniteEtaleField), or a direct finite-etale proof of
structureMap = toA ≫ A.map.  No cancellation witness is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2090StackCancellationObstructionActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S2089StackCancellationActual

universe u

/-- Exact missing postcomposition-cancellation principle (false in general). -/
def S2090PostcompCancellation : Type _ :=
  ∀ {X Y Z : EtaleStackOverField S1726K} (g : Y.Hom Z)
    {a b : X.Hom Y},
    Iso (Pseudofunctor.StrongTrans.vcomp a g)
      (Pseudofunctor.StrongTrans.vcomp b g) →
    Iso a b

#check S2090PostcompCancellation

end LeanFormal.IUT.XiFPaper.S2090StackCancellationObstructionActual

end
