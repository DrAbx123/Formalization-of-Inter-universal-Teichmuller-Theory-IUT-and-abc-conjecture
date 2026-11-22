import tmp.sheaf.xif.paper.S3127G2TargetUnitActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2TargetUnitActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2TargetUnitFieldsActual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable [Fintype G] [DecidableEq G]
variable (hfree : ∀ (x : A.obj.left.left) (g : G),
  (S3127G2Action A act g).hom.left.left x = x → g = 1)
variable (hInv : ∀ g : G,
  S3127G2Action A act g ≫ S3127G2QuotientMap A act = S3127G2QuotientMap A act)

theorem S3127G2TargetUnitFields_action_one :
    (S3127FreeQuotientTargetUnit A act hfree hInv).action 1 = 𝟙 A :=
  (S3127FreeQuotientTargetUnit A act hfree hInv).action_one

theorem S3127G2TargetUnitFields_action_mul (g h : G) :
    (S3127FreeQuotientTargetUnit A act hfree hInv).action (g * h) =
      (S3127FreeQuotientTargetUnit A act hfree hInv).action g ≫
        (S3127FreeQuotientTargetUnit A act hfree hInv).action h :=
  (S3127FreeQuotientTargetUnit A act hfree hInv).action_mul g h

theorem S3127G2TargetUnitFields_invariant (g : G) :
    (S3127FreeQuotientTargetUnit A act hfree hInv).action g ≫
      (S3127FreeQuotientTargetUnit A act hfree hInv).quotientMap =
      (S3127FreeQuotientTargetUnit A act hfree hInv).quotientMap :=
  (S3127FreeQuotientTargetUnit A act hfree hInv).invariant g

#check S3127G2TargetUnitFields_action_one
#check S3127G2TargetUnitFields_action_mul
#check S3127G2TargetUnitFields_invariant
end LeanFormal.IUT.XiFPaper.S3127G2TargetUnitFieldsActual
end
