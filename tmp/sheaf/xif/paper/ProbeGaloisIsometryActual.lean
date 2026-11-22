import tmp.sheaf.xif.paper.Mzk1GaloisRingBridgeActual
import tmp.sheaf.xif.paper.Mzk1AdicAbvEquivActual
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.UniformRing

/-! Probe: Galois place norm equality / isometry. -/
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1GaloisRingBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1ObjectLockDataActual
open LeanFormal.IUT.XiFPaper.Mzk1AdicAbvEquivActual

namespace LeanFormal.IUT.XiFPaper.ProbeGaloisIsometryActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
#check LeanFormal.IUT.XiFPaper.Mzk1ObjectLockDataActual.galoisPlaceMk
#check NumberField.FinitePlace.mk_apply

theorem galoisPlaceMk_apply
    (σ : T.arithmetic.F ≃ₐ[T.arithmetic.Fmod] T.arithmetic.F)
    (v : NumberField.FinitePlace T.arithmetic.F)
    (x : T.arithmetic.F) :
    LeanFormal.IUT.XiFPaper.Mzk1ObjectLockDataActual.galoisPlaceMk T σ v x = v (σ.symm x) := by
  rw [LeanFormal.IUT.XiFPaper.Mzk1ObjectLockDataActual.galoisPlaceMk, NumberField.FinitePlace.mk_apply,
    NumberField.FinitePlace.norm_embedding]
  have hv : v (σ.symm x) = NumberField.HeightOneSpectrum.adicAbv T.arithmetic.F v.maximalIdeal (σ.symm x) := by
    conv_lhs => rw [← NumberField.FinitePlace.mk_maximalIdeal v]
    rw [NumberField.FinitePlace.mk_apply, NumberField.FinitePlace.norm_embedding]
  rw [hv]
  have h := adicAbv_equivOfRingEquiv (K := T.arithmetic.F) (K' := T.arithmetic.F) σ.toRingEquiv v.maximalIdeal (σ.symm x)
  simpa using h


theorem adicAbv_lt_one_iff (v : NumberField.FinitePlace T.arithmetic.F) (x : T.arithmetic.F) :
    v x < 1 ↔ v.maximalIdeal.valuation T.arithmetic.F x < 1 := by
  conv_lhs => rw [← NumberField.FinitePlace.mk_maximalIdeal v]
  rw [NumberField.FinitePlace.mk_apply, NumberField.FinitePlace.norm_embedding]
  rw [NumberField.HeightOneSpectrum.adicAbv_def]
  exact WithZeroMulInt.toNNReal_lt_one_iff
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v.maximalIdeal)

theorem valuation_isEquiv_comap
    (σ : T.arithmetic.F ≃ₐ[T.arithmetic.Fmod] T.arithmetic.F)
    (v : NumberField.FinitePlace T.arithmetic.F) :
    (v.maximalIdeal.valuation T.arithmetic.F).IsEquiv
      (Valuation.comap σ.toRingHom
        ((galoisPlaceMk (T := T) σ v).maximalIdeal.valuation T.arithmetic.F)) := by
  rw [Valuation.isEquiv_iff_val_lt_one]
  intro x
  rw [Valuation.comap_apply]
  change v.maximalIdeal.valuation T.arithmetic.F x < 1 ↔
    (galoisPlaceMk (T := T) σ v).maximalIdeal.valuation T.arithmetic.F (σ x) < 1
  rw [← adicAbv_lt_one_iff (T := T) v x,
    ← adicAbv_lt_one_iff (T := T) (galoisPlaceMk (T := T) σ v) (σ x)]
  simp [galoisPlaceMk_apply]


end LeanFormal.IUT.XiFPaper.ProbeGaloisIsometryActual
end
