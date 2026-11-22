import tmp.sheaf.xif.paper.Mzk1ValueGroupActual
import tmp.sheaf.xif.paper.Mzk1GaloisToMZActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1GaloisCompletionActual
open LeanFormal.IUT.XiFPaper.Mzk1ValueGroupActual
open LeanFormal.IUT.XiFPaper.Mzk1GaloisToMZActual
open LeanFormal.IUT.XiFPaper.Mzk1ObjectLockDataActual

namespace LeanFormal.IUT.XiFPaper.Mzk1ValueGroupProofActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (σ : T.arithmetic.F ≃ₐ[T.arithmetic.Fmod] T.arithmetic.F)
variable (v : NumberField.FinitePlace T.arithmetic.F)

theorem valueGroupTransportData :
    ValueGroupTransportData (T := T) σ v := by
  refine ⟨?valueGroup_eq⟩
  apply le_antisymm
  · rw [MonoidWithZeroHom.valueGroup_def, Subgroup.closure_le]
    intro u hu
    change u ∈ MonoidWithZeroHom.valueMonoid
      (Valued.v (R := WithVal (Valuation.comap σ.toRingHom
        ((galoisPlaceMk (T := T) σ v).maximalIdeal.valuation T.arithmetic.F)))).toMonoidWithZeroHom at hu
    have hu' : (u : (WithZero (Multiplicative ℤ))ˣ).val ∈ Set.range
        (Valued.v (R := WithVal (Valuation.comap σ.toRingHom
          ((galoisPlaceMk (T := T) σ v).maximalIdeal.valuation T.arithmetic.F)))).toMonoidWithZeroHom :=
      (MonoidWithZeroHom.mem_valueMonoid_iff (f := (Valued.v (R := WithVal (Valuation.comap σ.toRingHom
        ((galoisPlaceMk (T := T) σ v).maximalIdeal.valuation T.arithmetic.F)))).toMonoidWithZeroHom)).mp hu
    obtain ⟨a, ha⟩ := hu'
    exact MonoidWithZeroHom.mem_valueGroup (f := (Valued.v (R := WithVal
        ((galoisPlaceMk (T := T) σ v).maximalIdeal.valuation T.arithmetic.F))).toMonoidWithZeroHom)
      ⟨withValMovedSigma (T := T) σ v a, by
        rw [withValMovedSigma_toMonoidWithZeroHom_val_eq, ha]⟩
  · rw [MonoidWithZeroHom.valueGroup_def, Subgroup.closure_le]
    intro u hu
    change u ∈ MonoidWithZeroHom.valueMonoid
      (Valued.v (R := WithVal
        ((galoisPlaceMk (T := T) σ v).maximalIdeal.valuation T.arithmetic.F))).toMonoidWithZeroHom at hu
    have hu' : (u : (WithZero (Multiplicative ℤ))ˣ).val ∈ Set.range
        (Valued.v (R := WithVal
          ((galoisPlaceMk (T := T) σ v).maximalIdeal.valuation T.arithmetic.F))).toMonoidWithZeroHom :=
      (MonoidWithZeroHom.mem_valueMonoid_iff (f := (Valued.v (R := WithVal
        ((galoisPlaceMk (T := T) σ v).maximalIdeal.valuation T.arithmetic.F))).toMonoidWithZeroHom)).mp hu
    obtain ⟨b, hb⟩ := hu'
    obtain ⟨a, rfl⟩ := withValMovedSigma_surjective (T := T) σ v b
    exact MonoidWithZeroHom.mem_valueGroup (f := (Valued.v (R := WithVal (Valuation.comap σ.toRingHom
        ((galoisPlaceMk (T := T) σ v).maximalIdeal.valuation T.arithmetic.F)))).toMonoidWithZeroHom)
      ⟨a, by rw [← withValMovedSigma_toMonoidWithZeroHom_val_eq, hb]⟩

end LeanFormal.IUT.XiFPaper.Mzk1ValueGroupProofActual
end
