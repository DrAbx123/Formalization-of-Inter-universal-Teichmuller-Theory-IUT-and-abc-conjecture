import tmp.sheaf.xif.paper.S2086ToAAssemblyActual
import tmp.sheaf.xif.paper.S2103StrongAssemblyActual

/-! # S2284: S2086/S2087 target quantifier audit

`S2086CospanGMapFiniteEtale` is *definitionally* the full quantifier

  forall (A B C : S1728Cover) (f : A -> C) (g : B -> C),
    EtaleStackFiniteEtaleMorphism g.map.

So the target is not restricted to concrete covers.  A strong finite-etale
structure (S2103) supplies the required weak structure by forgetting; this
strong input is recorded as an explicit hypothesis, not as proved.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2284S2086QuantifierActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S2103StrongAssemblyActual

universe u

/-- Definitional audit: S2086's cospan field is the full quantifier. -/
theorem S2284CospanFullQuantifier :
    S2086CospanGMapFiniteEtale =
      (∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C),
        EtaleStackFiniteEtaleMorphism g.map) := rfl

/-- The S2103 strong input forgets to S2086's weak cospan field. -/
noncomputable def S2284StrongCospanToWeak
    (h : S2103StrongCospanGMapFiniteEtale) : S2086CospanGMapFiniteEtale :=
  fun A B C f g => (h A B C f g).toWeak

#print axioms S2284CospanFullQuantifier
#print axioms S2284StrongCospanToWeak
#check S2284CospanFullQuantifier
#check S2284StrongCospanToWeak
#check S2086CospanGMapFiniteEtale

end LeanFormal.IUT.XiFPaper.S2284S2086QuantifierActual

end
