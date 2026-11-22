import tmp.sheaf.xif.paper.Mzk1GaloisCompletionActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1GaloisCompletionActual
open LeanFormal.IUT.XiFPaper.Mzk1ObjectLockDataActual

namespace LeanFormal.IUT.XiFPaper.Mzk1GaloisToMZActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (σ : T.arithmetic.F ≃ₐ[T.arithmetic.Fmod] T.arithmetic.F)
variable (v : NumberField.FinitePlace T.arithmetic.F)

theorem withValMovedSigma_toMonoidWithZeroHom_val_eq
    (x : WithVal (Valuation.comap σ.toRingHom
      ((galoisPlaceMk (T := T) σ v).maximalIdeal.valuation T.arithmetic.F))) :
    (Valued.v (R := WithVal
        ((galoisPlaceMk (T := T) σ v).maximalIdeal.valuation T.arithmetic.F))).toMonoidWithZeroHom
        (withValMovedSigma (T := T) σ v x) =
      (Valued.v (R := WithVal (Valuation.comap σ.toRingHom
        ((galoisPlaceMk (T := T) σ v).maximalIdeal.valuation T.arithmetic.F)))).toMonoidWithZeroHom x := by
  change (Valued.v (withValMovedSigma (T := T) σ v x) : WithZero (Multiplicative ℤ)) =
    (Valued.v x : WithZero (Multiplicative ℤ))
  exact withValMovedSigma_val_eq (T := T) σ v x

end LeanFormal.IUT.XiFPaper.Mzk1GaloisToMZActual
end
