import tmp.sheaf.xif.paper.S2855A6CoreFromD6ConditionalActual
import tmp.sheaf.xif.paper.S1742HomVcompActual
import tmp.sheaf.xif.paper.S2844D6F6BaseChangeActual
import tmp.sheaf.xif.paper.S2851A6D6GeometryActual

noncomputable section
open LeanFormal.IUT CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2857StackAutoForA6Actual

open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2851A6D6GeometryActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1742HomVcompActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF

noncomputable def S2857StackAuto (α : S2844X ⟶ S2844X) :
    S2855HyperbolicOrbicurve.Hom S2855HyperbolicOrbicurve :=
  S1742StrongTransOfHom (F := S2847A6.F) α

theorem S2857HomOf_vcomp_self
    (α : S2844X ⟶ S2844X) (hα : α ≫ α = 𝟙 S2844X) :
    S1742HomOfStrongTrans (F := S2847A6.F)
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := S2847A6.F) α)
        (S1742StrongTransOfHom (F := S2847A6.F) α)) = 𝟙 S2844X := by
  rw [S1742HomOfStrongTrans_vcomp,
    S1742HomOfStrongTrans_strongTransOfHom]
  exact hα

noncomputable def S2857StackAuto_square
    (α : S2844X ⟶ S2844X) (hα : α ≫ α = 𝟙 S2844X) :
    Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp (S2857StackAuto α) (S2857StackAuto α))
      (Iut.HyperbolicOrbicurve.Hom.id S2855HyperbolicOrbicurve) := by
  change Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := S2847A6.F) α)
      (S1742StrongTransOfHom (F := S2847A6.F) α) ≅
    Pseudofunctor.StrongTrans.id
      (S1742YS (F := S2847A6.F) S2844X)
  have hcomp := S2857HomOf_vcomp_self α hα
  let A := S1742StrongTransIsoOfHom (F := S2847A6.F)
    (Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := S2847A6.F) α)
      (S1742StrongTransOfHom (F := S2847A6.F) α))
  let B := S1742StrongTransIsoOfHom (F := S2847A6.F)
    (Pseudofunctor.StrongTrans.id (S1742YS (F := S2847A6.F) S2844X))
  exact (hcomp ▸ A).symm.trans B

#check S2857StackAuto
#check S2857StackAuto_square
#print axioms S2857StackAuto_square

end LeanFormal.IUT.XiFPaper.S2857StackAutoForA6Actual
end
