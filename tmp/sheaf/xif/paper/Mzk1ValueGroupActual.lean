import tmp.sheaf.xif.paper.Mzk1GaloisCompletionActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1GaloisCompletionActual
open LeanFormal.IUT.XiFPaper.Mzk1ObjectLockDataActual

namespace LeanFormal.IUT.XiFPaper.Mzk1ValueGroupActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (σ : T.arithmetic.F ≃ₐ[T.arithmetic.Fmod] T.arithmetic.F)
variable (v : NumberField.FinitePlace T.arithmetic.F)

/-- Exact interface still needed for the value-group transport: the two value groups of the
pulled-back and moved valuations coincide. -/
structure ValueGroupTransportData where
  valueGroup_eq :
    MonoidWithZeroHom.valueGroup
      (Valued.v (R := WithVal (Valuation.comap σ.toRingHom
        ((galoisPlaceMk (T := T) σ v).maximalIdeal.valuation T.arithmetic.F)))).toMonoidWithZeroHom =
    MonoidWithZeroHom.valueGroup
      (Valued.v (R := WithVal
        ((galoisPlaceMk (T := T) σ v).maximalIdeal.valuation T.arithmetic.F))).toMonoidWithZeroHom

end LeanFormal.IUT.XiFPaper.Mzk1ValueGroupActual
end
