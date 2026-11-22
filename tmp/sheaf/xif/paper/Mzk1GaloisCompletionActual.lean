import tmp.sheaf.xif.paper.ProbeGaloisIsometryActual
import Mathlib.Topology.Algebra.Valued.WithVal
import Mathlib.Topology.Algebra.UniformRing

/-! # WithVal Galois equivariance and completion map

The ring hom on WithVal induced by σ, factored through the valuation
`moved.valuation.comap σ`, is uniform continuous.
-/

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.ProbeGaloisIsometryActual
open LeanFormal.IUT.XiFPaper.Mzk1ObjectLockDataActual

namespace LeanFormal.IUT.XiFPaper.Mzk1GaloisCompletionActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (σ : T.arithmetic.F ≃ₐ[T.arithmetic.Fmod] T.arithmetic.F)
variable (v : NumberField.FinitePlace T.arithmetic.F)

/-- σ as a ring hom from WithVal of the pulled-back moved valuation to WithVal of the
moved valuation. -/
noncomputable def withValMovedSigma :
    WithVal (Valuation.comap σ.toRingHom
      ((galoisPlaceMk (T := T) σ v).maximalIdeal.valuation T.arithmetic.F)) →+*
      WithVal ((galoisPlaceMk (T := T) σ v).maximalIdeal.valuation T.arithmetic.F) :=
  ((WithVal.equiv ((galoisPlaceMk (T := T) σ v).maximalIdeal.valuation T.arithmetic.F)).symm.toRingHom).comp
    (σ.toRingHom.comp
      (WithVal.equiv (Valuation.comap σ.toRingHom
        ((galoisPlaceMk (T := T) σ v).maximalIdeal.valuation T.arithmetic.F))).toRingHom)



theorem withValMovedSigma_surjective :
    Function.Surjective (withValMovedSigma (T := T) σ v) := by
  have h : withValMovedSigma (T := T) σ v =
      (WithVal.congr
        (Valuation.comap σ.toRingHom
          ((galoisPlaceMk (T := T) σ v).maximalIdeal.valuation T.arithmetic.F))
        ((galoisPlaceMk (T := T) σ v).maximalIdeal.valuation T.arithmetic.F)
        σ.toRingEquiv).toRingHom := rfl
  rw [h]
  exact (WithVal.congr _ _ σ.toRingEquiv).surjective





theorem withValMovedSigma_val_eq (x : WithVal (Valuation.comap σ.toRingHom
    ((galoisPlaceMk (T := T) σ v).maximalIdeal.valuation T.arithmetic.F))) :
    (Valued.v (withValMovedSigma (T := T) σ v x) : WithZero (Multiplicative ℤ)) =
      (Valued.v x : WithZero (Multiplicative ℤ)) := by
  change (WithVal.valuation
      ((galoisPlaceMk (T := T) σ v).maximalIdeal.valuation T.arithmetic.F)
      (WithVal.congr
        (Valuation.comap σ.toRingHom
          ((galoisPlaceMk (T := T) σ v).maximalIdeal.valuation T.arithmetic.F))
        ((galoisPlaceMk (T := T) σ v).maximalIdeal.valuation T.arithmetic.F)
        σ.toRingEquiv x) : WithZero (Multiplicative ℤ)) =
    (WithVal.valuation
      (Valuation.comap σ.toRingHom
        ((galoisPlaceMk (T := T) σ v).maximalIdeal.valuation T.arithmetic.F)) x :
      WithZero (Multiplicative ℤ))
  rw [WithVal.congr_apply, WithVal.valuation_toVal,
    WithVal.valuation_apply_eq_ofVal, Valuation.comap_apply]
  rfl





end LeanFormal.IUT.XiFPaper.Mzk1GaloisCompletionActual
end
