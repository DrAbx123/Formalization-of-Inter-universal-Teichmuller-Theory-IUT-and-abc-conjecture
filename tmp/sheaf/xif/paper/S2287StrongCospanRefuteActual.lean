import tmp.sheaf.xif.paper.S2284S2086QuantifierActual
import tmp.sheaf.xif.paper.S1852CoherentCoverActual
import tmp.sheaf.xif.paper.S1641CoverMapCompositionActual

/-! # S2287: can the doubled cover refute S2103StrongCospanGMapFiniteEtale?

Audit result: no.  S2103 quantifies only over `g.map` and asks for *some*
`StrongEtaleStackFiniteEtaleMorphism g.map`.  The cover's weak datum
`g.finiteEtale` is not part of that quantifier.  S1852Doubled_not_strong only
rules out strong structures `M` with `M.toWeak = S1850DoubledFiniteEtale`;
it says nothing about other strong structures on the same identity map.

Thus taking `g = S1641CoverMapId S1850DoubledCover` does NOT refute S2103.
The exact obstruction to this refutation route is the missing equality
`M.toWeak = g.finiteEtale` inside S2103.  No refutation is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2287StrongCospanRefuteActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1850RefuteS1756Actual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S2103StrongAssemblyActual
open LeanFormal.IUT.XiFPaper.S2284S2086QuantifierActual

universe u

/-- The identity cover map on the doubled cover. -/
abbrev S2287G : S1728CoverMap S1850DoubledCover S1850DoubledCover :=
  S1641CoverMapId S1850DoubledCover

/-- The double-cover instantiation of S2103. -/
def S2287StrongOnDoubled : Type 1 :=
  StrongEtaleStackFiniteEtaleMorphism S2287G.map

/-- S2103 at the doubled identity map is exactly a strong structure on the
identity map; its weak part is not tied to the doubled cover datum. -/
noncomputable def S2287QuantifierInstance
    (h : S2103StrongCospanGMapFiniteEtale) : S2287StrongOnDoubled :=
  h S1850DoubledCover S1850DoubledCover S1850DoubledCover S2287G S2287G

#check S2287StrongOnDoubled
#check S2287QuantifierInstance
#check S1852Doubled_not_strong

end LeanFormal.IUT.XiFPaper.S2287StrongCospanRefuteActual

end
