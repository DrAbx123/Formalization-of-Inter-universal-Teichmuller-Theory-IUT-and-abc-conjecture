import tmp.sheaf.xif.paper.S1742HomVcompActual
import tmp.sheaf.xif.paper.S1419D6NonterminalStackActual
open LeanFormal.IUT CategoryTheory
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1742HomVcompActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
noncomputable section
variable {l : PrimeGeFive}
example :
    S1742HomOfStrongTrans (F := S1348K l)
      (Pseudofunctor.StrongTrans.id (S1742YS (F := S1348K l) (S1419AffineOver l))) =
    𝟙 (S1419AffineOver l) := by
  rw [← S1742HomOfStrongTrans_strongTransOfHom (F := S1348K l) (𝟙 (S1419AffineOver l))]
  congr 1
