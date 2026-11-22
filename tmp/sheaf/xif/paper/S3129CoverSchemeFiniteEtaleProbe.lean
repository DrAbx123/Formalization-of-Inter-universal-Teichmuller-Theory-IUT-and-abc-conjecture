import tmp.sheaf.xif.paper.S3129CoverSchemeFiniteEtaleAttempt
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.RepresentableCoverChosenCategoryActual
open LeanFormal.IUT.XiFPaper.S3129CoverSchemeFiniteEtaleAttempt
open LeanFormal.IUT.XiFPaper.S3129RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S3128PullbackCoproductActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
namespace LeanFormal.IUT.XiFPaper.S3129CoverSchemeFiniteEtaleProbe
variable {l : PrimeGeFive}
theorem test (A : S3127Cover (l := l)) :
    AlgebraicGeometry.IsFinite
        (S3129PSnd (F := S1348K l) (S3128ToSchemeMap A)
          (S3129TestId (l := l))).left ∧
      AlgebraicGeometry.Etale
        (S3129PSnd (F := S1348K l) (S3128ToSchemeMap A)
          (S3129TestId (l := l))).left :=
  ⟨inferInstance, inferInstance⟩
end LeanFormal.IUT.XiFPaper.S3129CoverSchemeFiniteEtaleProbe
end