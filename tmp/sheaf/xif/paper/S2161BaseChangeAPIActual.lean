import tmp.sheaf.xif.paper.S2156S2096BaseChangeActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual

/-! # S2161: the scheme-map base-change API is unconditional

For any scheme morphism `q : R -> T`, the strong transformation
`S1742StrongTransOfHom q` is definitionally the functor induced by `q`, so
`SchemeRepresentableMap q` is immediate.  Hence the first exact missing input
of S2156, `S2156SchemeRepresentableMapBaseChange`, is proved here with no
extra hypothesis on the square; the finite-etale and presentation data are
only needed for the separate witness transport.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2161BaseChangeAPIActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2156S2096BaseChangeActual

universe u

/-- **The scheme-map base-change API is unconditional**: every scheme
morphism is scheme-representable. -/
noncomputable def S2161SchemeRepresentableMapBaseChange :
    S2156SchemeRepresentableMapBaseChange := by
  intro S A T g s R q r hsq G hs hse hq hqe
  exact
    { transformation := S1742StrongTransOfHom q
      app_eq := fun U => rfl }

#print axioms S2161SchemeRepresentableMapBaseChange

end LeanFormal.IUT.XiFPaper.S2161BaseChangeAPIActual

end
