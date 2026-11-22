import tmp.sheaf.xif.paper.S1908S1280D5ImageActual
import tmp.sheaf.xif.paper.S1982D5FiveActual
import tmp.sheaf.xif.paper.S2604C9D5D7D8MinimalActual
import tmp.sheaf.xif.paper.S1637D5TorsionClauseActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.TorsionCarrierReduction
open LeanFormal.IUT.Theorem311Source

namespace LeanFormal.IUT.XiFPaper.S2605C9D5TerminalActual

open LeanFormal.IUT.XiFPaper.S1908S1280D5ImageActual
open LeanFormal.IUT.XiFPaper.S1298TorsionClauseActual
open LeanFormal.IUT.XiFPaper.S1637D5TorsionClauseActual

/-- The exact terminal form of the D5 large-image target: an `SL_2(F_l)`-containing basis. -/
theorem s2605_serre_terminal {F : Type} [Field F]
    (X : PuncturedEllipticCurve F) (l : PrimeGeFive) :
    SerreStyleLargeImageStatement X l ↔
      ∃ basis : (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] X.LTorsion l,
        Subgroup.map Matrix.SpecialLinearGroup.toGL
          (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
          (X.galoisLTorsionMatrixRepresentation l basis).range :=
  Iff.rfl

/-- On the S1280 Gaussian curve the paper's large-image field is exactly the S1908 exact missing input. -/
theorem s2605_s1280_largeImage_iff_exactMissing (l : PrimeGeFive) :
    S1298LargeImageField l ↔ S1908ExactMissing l :=
  (S1908ExactMissing_iff_serre l).symm

/-- The S1908 exact missing input decomposes into a rank-two basis and basis-free SL2 containment. -/
theorem s2605_s1280_exactMissing_decomposition (l : PrimeGeFive) :
    S1908ExactMissing l ↔
      Nonempty (S1908TorsionBasis l) ∧ S1908LargeImageInput l :=
  Iff.rfl

/-- Basis-free containment is the universal tail over all bases. -/
theorem s2605_s1280_largeImageInput_iff_forall (l : PrimeGeFive) :
    S1908LargeImageInput l ↔
      ∀ b : S1908TorsionBasis l, S1908ImageTail l b :=
  Iff.rfl

/-- Exact residual form: the D5 clause is the large-image input plus the two paper conditions. -/
theorem s2605_s1280_D5Residual_decomposition (l : PrimeGeFive) :
    S1908D5Residual l ↔
      S1908ExactMissing l ∧ S1637SixTorsionIndependent l ∧
        S1637LTorsionCompatible l :=
  S1908D5Residual_decomposition l

end LeanFormal.IUT.XiFPaper.S2605C9D5TerminalActual

end