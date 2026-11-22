import tmp.sheaf.xif.paper.S3121SignDataActual
import tmp.sheaf.xif.paper.S2852OrbicurveSignActionCoherentActual

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section
open LeanFormal.IUT CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans Bicategory
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119NegInvolutionOverActual
open LeanFormal.IUT.XiFPaper.S3121SignDataActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1742HomVcompActual

namespace LeanFormal.IUT.XiFPaper.S3121DiagramActual

variable {l : PrimeGeFive}

instance S3121StrongTransHomSubsingleton (F : Type) [Field F]
    {S T : Iut.SchemeOverField F}
    (eta theta : Pseudofunctor.StrongTrans (S1742YS (F := F) S)
      (S1742YS (F := F) T)) :
    Subsingleton (eta ⟶ theta) := by
  constructor
  intro m n
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro a
  apply CategoryTheory.Cat.Hom₂.ext
  apply CategoryTheory.NatTrans.ext
  funext X
  apply ULift.ext
  exact Subsingleton.elim _ _

instance S3121MapSubsingleton (l : PrimeGeFive)
    {b₀ b₁ b₂ b₃ : SingleObj Iut.SignGroup}
    (f : b₀ ⟶ b₁) (g : b₂ ⟶ b₃) :
    Subsingleton (S3121Map (l := l) f ⟶ S3121Map (l := l) g) :=
  S3121StrongTransHomSubsingleton (F := (S1280Arithmetic l).F)
    (S := S1419AffineOver l) (T := S1419AffineOver l)
    (S3121Map (l := l) f) (S3121Map (l := l) g)

noncomputable abbrev S3121Diagram :
    Iut.SignActionIndex ⥤ᵖ Iut.EtaleStackPseudofunctor (S1280Arithmetic l).F :=
  CategoryTheory.pseudofunctorOfIsLocallyDiscrete
    (fun b => S3121Obj (l := l) b.as)
    (fun {_ _} f => S3121Map (l := l) f.as)
    (fun b => S3121MapId (l := l) b.as)
    (fun {_ _ _} f g => S3121MapComp (l := l) f.as g.as)
    (fun {_ _ _ _} f g h => Subsingleton.elim _ _)
    (fun {_ _} f => Subsingleton.elim _ _)
    (fun {_ _} f => Subsingleton.elim _ _)

#check S3121Diagram
#print axioms S3121Diagram

end LeanFormal.IUT.XiFPaper.S3121DiagramActual
end
