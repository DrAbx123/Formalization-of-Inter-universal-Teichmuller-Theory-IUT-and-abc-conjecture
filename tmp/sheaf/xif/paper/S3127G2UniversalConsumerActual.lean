import tmp.sheaf.xif.paper.S3127G2TargetActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2UniversalConsumerActual
variable {l : PrimeGeFive} {G : Type} [Group G] [Fintype G]
variable {A : S3127FiniteEtaleOverKFull l} (T : S3127FreeQuotientTarget A G)

theorem S3127G2UniversalConsumer_factor
    (h : S3127QuotientUniversal T)
    {B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B)
    (hf : ∀ g : G, T.action g ≫ f = f) :
    ∃! v : T.quotientObj ⟶ B, T.quotientMap ≫ v = f :=
  h f hf

theorem S3127G2UniversalConsumer_unique
    (h : S3127QuotientUniversal T)
    {B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B)
    (hf : ∀ g : G, T.action g ≫ f = f)
    (v w : T.quotientObj ⟶ B)
    (hv : T.quotientMap ≫ v = f)
    (hw : T.quotientMap ≫ w = f) : v = w := by
  rcases h f hf with ⟨u, hu, huniq⟩
  rw [huniq v hv, huniq w hw]

#check S3127G2UniversalConsumer_factor
#check S3127G2UniversalConsumer_unique
end LeanFormal.IUT.XiFPaper.S3127G2UniversalConsumerActual
end
