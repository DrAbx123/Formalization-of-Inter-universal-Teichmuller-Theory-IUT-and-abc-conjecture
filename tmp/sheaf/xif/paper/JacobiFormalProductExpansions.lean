import tmp.sheaf.xif.paper.JacobiAlignedIdentity
import tmp.sheaf.xif.paper.JacobiAlignedExpansion

noncomputable section

open LeanFormal.IUT.XiFPaper.TateJacobiHahnAttempt

namespace LeanFormal.IUT.XiFPaper.JacobiFormalProductExpansions

variable {K : Type u} [Field K]

/-- The full finite theta product expansion of `jacobiFormalProduct`. -/
theorem jacobiFormalProduct_eq_threeExpansions (z : K) (N : Nat) :
    jacobiFormalProduct z N =
      (Finset.sum (Finset.range (N + 1)) (fun k : Nat =>
          LeanFormal.IUT.XiFPaper.QBinomialCommRing.qBinoTermC
            (K := HahnSeries Int K) N k (formalR ^ 4)
            (HahnSeries.C z * formalR ^ 2))) *
        (Finset.sum (Finset.range (N + 1)) (fun k : Nat =>
          LeanFormal.IUT.XiFPaper.QBinomialCommRing.qBinoTermC
            (K := HahnSeries Int K) N k (formalR ^ 4)
            (HahnSeries.C z⁻¹ * formalR ^ 2))) *
          (Finset.sum (Finset.range (N + 1)) (fun k : Nat =>
            LeanFormal.IUT.XiFPaper.QBinomialCommRing.qBinoTermC
              (K := HahnSeries Int K) N k (formalR ^ 4)
              (-(formalR ^ 4)))) := by
  rw [LeanFormal.IUT.XiFPaper.JacobiAlignedIdentity.S3134_jacobiAlignedProduct_identity]
  unfold jacobiAlignedProduct
  rw [LeanFormal.IUT.XiFPaper.JacobiAlignedExpansion.alignedFirstProduct_expand,
    LeanFormal.IUT.XiFPaper.JacobiAlignedExpansion.alignedSecondProduct_expand,
    LeanFormal.IUT.XiFPaper.JacobiAlignedExpansion.alignedThirdProduct_expand]

#check jacobiFormalProduct_eq_threeExpansions

end LeanFormal.IUT.XiFPaper.JacobiFormalProductExpansions
