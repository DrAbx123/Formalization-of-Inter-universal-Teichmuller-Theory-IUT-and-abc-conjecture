import tmp.sheaf.xif.paper.S3121DiagramActual
import tmp.sheaf.xif.paper.S1419D6NonterminalStackActual

noncomputable section
open LeanFormal.IUT CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119NegInvolutionOverActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S3121DiagramActual

namespace LeanFormal.IUT.XiFPaper.S3121DiagramAttempt


/-- The S1419 realized stack fiber is the 2-Yoneda representable pseudofunctor. -/
theorem S3121Fiber_eq_YS :
    (S1536XF (l := l)).stack.fiber =
      S1742YS (F := (S1280Arithmetic l).F) (S1419AffineOver l) :=
  rfl

variable {l : PrimeGeFive}

/-- The map of the sign action diagram. -/
noncomputable def S3121Map {b b' : SingleObj Iut.SignGroup}
    (f : b ⟶ b') : S3121Obj (l := l) b ⟶ S3121Obj (l := l) b' :=
  by
    classical
    exact if (f : Iut.SignGroup) = (1 : Iut.SignGroup) then
      𝟙 (S3121Obj (l := l) b)
    else cast (by rfl)
      (S1742StrongTransOfHom (F := (S1280Arithmetic l).F)
        (S3119NegOverHom (l := l)))

noncomputable def S3121MapId (b : SingleObj Iut.SignGroup) :
    S3121Map (l := l) (𝟙 b) ≅ 𝟙 (S3121Obj (l := l) b) := by
  dsimp only [S3121Map]
  rw [if_pos (by rfl)]

#check S3121Map
#check S3121MapId
#check S3121AtBase

end LeanFormal.IUT.XiFPaper.S3121DiagramAttempt
end
