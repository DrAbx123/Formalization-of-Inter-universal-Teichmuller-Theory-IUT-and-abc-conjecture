import tmp.sheaf.xif.paper.S2087ToAObstructionActual
import tmp.sheaf.xif.paper.S2058D6FiniteEtaleActual
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # S2088: scheme cancellation and reduction of g.map finite etaleness

Mathlib supplies both cancellation lemmas: `Etale.of_comp` and
`IsFinite.of_comp`.  Thus a morphism `f` with `f ≫ g` finite etale and `g`
finite etale is itself finite etale.  The stack-level cancellation is reduced
to an explicit Type-valued statement `S2088StackCancellation`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2088GMapCancellationActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2087ToAObstructionActual

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Scheme-level cancellation of finite-etale morphisms. -/
theorem S2088_scheme_finiteEtale_cancel
    [Etale (f ≫ g)] [LocallyOfFiniteType g] [FormallyUnramified g]
    [IsFinite (f ≫ g)] [IsSeparated g] :
    Etale f ∧ IsFinite f :=
  ⟨Etale.of_comp (f := f) g, IsFinite.of_comp f g⟩

/-- Stack-level cancellation: the exact missing ingredient for `g.map`. -/
def S2088StackCancellation : Type 1 :=
  ∀ {X Y Z : EtaleStackOverField S1726K} (f : X.Hom Y) (g : Y.Hom Z),
    EtaleStackFiniteEtaleMorphism (Pseudofunctor.StrongTrans.vcomp f g) →
    EtaleStackFiniteEtaleMorphism g →
    EtaleStackFiniteEtaleMorphism f

/-- Stack cancellation gives `S2087GMapFiniteEtaleField`, using B.finiteEtale,
C.finiteEtale and the 2-isomorphism invariance of S2058. -/
noncomputable def S2088GMapFiniteEtaleOfStackCancellation
    (hcancel : S2088StackCancellation) : S2087GMapFiniteEtaleField := by
  intro A B C g
  have hcomp : EtaleStackFiniteEtaleMorphism
      (Pseudofunctor.StrongTrans.vcomp g.map C.map) :=
    S2058IsoInvarianceFiniteEtale g.commutes.symm B.finiteEtale
  exact hcancel g.map C.map hcomp C.finiteEtale

#print axioms S2088_scheme_finiteEtale_cancel
#print axioms S2088GMapFiniteEtaleOfStackCancellation

end LeanFormal.IUT.XiFPaper.S2088GMapCancellationActual

end
