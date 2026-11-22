import tmp.sheaf.xif.paper.S3127KLinearFullActual
import tmp.sheaf.xif.paper.S3127ForgetfulActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127ForgetfulActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
variable {l : PrimeGeFive}

/-- Every K-linear finite etale cover is affine: finite over the affine base S1419. -/
instance S3127FullCover_isAffine
    (Y : S3127FiniteEtaleOverKFull l) :
    IsAffine Y.obj.left.left := by
  letI : IsAffine (Over.left (S1419AffineOver l)) :=
    inferInstanceAs (IsAffine (S1419AffineScheme l))
  haveI : IsFinite (Over.Hom.left Y.obj.hom) := Y.property.1
  exact isAffine_of_isAffineHom (f := Over.Hom.left Y.obj.hom)

structure S3127FreeQuotientTarget
    (A : S3127FiniteEtaleOverKFull l) (G : Type) [Group G] [Fintype G] :
    Type 2 where
  action : G → (A ⟶ A)
  action_one : action 1 = 𝟙 A
  action_mul : ∀ g h : G, action (g * h) = action g ≫ action h
  free : ∀ (x : A.obj.left.left) (g : G),
    (action g).hom.left.left x = x → g = 1
  quotientObj : S3127FiniteEtaleOverKFull l
  quotientMap : A ⟶ quotientObj
  invariant : ∀ g : G, action g ≫ quotientMap = quotientMap

/-- Universal property of a quotient, stated separately to avoid dependent field types. -/
def S3127QuotientUniversal
    {A : S3127FiniteEtaleOverKFull l} {G : Type} [Group G] [Fintype G]
    (T : S3127FreeQuotientTarget A G) : Prop :=
  ∀ {B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B),
    (∀ g : G, T.action g ≫ f = f) →
      ∃! (v : T.quotientObj ⟶ B), T.quotientMap ≫ v = f

/-- G2 existence target: every free finite group action has quotient data with universal property. -/
def S3127FreeQuotientExists : Prop :=
  ∀ (G : Type) [Group G] [Fintype G]
    (A : S3127FiniteEtaleOverKFull l),
    ∃ T : S3127FreeQuotientTarget A G, S3127QuotientUniversal T
#check S3127FreeQuotientTarget
#check S3127FreeQuotientExists
end LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
end
