import tmp.sheaf.xif.paper.Mzk1ObjectLockDataActual
import Mathlib.NumberTheory.RamificationInertia.Galois

/-! Bounded instance probe for the Galois/ring-of-integers route. -/
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.Mzk1ObjectLockDataActual

namespace LeanFormal.IUT.XiFPaper.ProbeGaloisRingSynthActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
noncomputable instance galoisFmodAction :
    MulSemiringAction (T.arithmetic.F ≃ₐ[T.arithmetic.Fmod] T.arithmetic.F)
      T.arithmetic.Fmod where
  smul _ r := r
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_mul _ _ _ := rfl
  smul_one _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

#synth MulSemiringAction (T.arithmetic.F ≃ₐ[T.arithmetic.Fmod] T.arithmetic.F)
  T.arithmetic.F
#synth MulSemiringAction (T.arithmetic.F ≃ₐ[T.arithmetic.Fmod] T.arithmetic.F)
  (NumberField.RingOfIntegers T.arithmetic.F)
#synth SMulDistribClass (T.arithmetic.F ≃ₐ[T.arithmetic.Fmod] T.arithmetic.F)
  (NumberField.RingOfIntegers T.arithmetic.F) T.arithmetic.F
#synth SMulDistribClass (T.arithmetic.F ≃ₐ[T.arithmetic.Fmod] T.arithmetic.F)
  (NumberField.RingOfIntegers T.arithmetic.Fmod) (NumberField.RingOfIntegers T.arithmetic.F)
#synth IsGaloisGroup (T.arithmetic.F ≃ₐ[T.arithmetic.Fmod] T.arithmetic.F)
  (NumberField.RingOfIntegers T.arithmetic.Fmod)
  (NumberField.RingOfIntegers T.arithmetic.F)

end LeanFormal.IUT.XiFPaper.ProbeGaloisRingSynthActual
end
