import tmp.sheaf.n8.closure.C7OneFactorAlgEquiv
import Mathlib.RingTheory.PiTensorProduct

/-!
# Constructed one-factor algebra equivalence

General `PiTensorProduct` singleton algebra equivalence and its application to
the paper one-factor block.  Uses `AlgEquiv.ofLinearEquiv`, `one_def`,
`subsingletonEquiv_apply_tprod`, `smul_tprod_mul_smul_tprod`, induction. -/

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.C7OneFactorAlgEquivConstructed2

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open scoped BigOperators ENNReal TensorProduct

section General

universe uR uK

variable {R : Type uR} [CommSemiring R]
variable {K : Unit → Type uK} [∀ i, CommRing (K i)] [∀ i, Algebra R (K i)]

noncomputable def piTensorSubsingletonAlgEquiv :
    (⨂[R] i : Unit, K i) ≃ₐ[R] K () := by
  let e := PiTensorProduct.subsingletonEquiv (R := R) (s := K) ()
  refine AlgEquiv.ofLinearEquiv e ?_ ?_
  · change e 1 = 1
    rw [PiTensorProduct.one_def, PiTensorProduct.subsingletonEquiv_apply_tprod]
    rfl
  · intro x y
    change e (x * y) = e x * e y
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r f =>
        induction y using PiTensorProduct.induction_on with
        | smul_tprod s g =>
            rw [PiTensorProduct.smul_tprod_mul_smul_tprod]
            rw [LinearEquiv.map_smul, LinearEquiv.map_smul, LinearEquiv.map_smul]
            rw [PiTensorProduct.subsingletonEquiv_apply_tprod,
              PiTensorProduct.subsingletonEquiv_apply_tprod,
              PiTensorProduct.subsingletonEquiv_apply_tprod]
            simp only [Pi.mul_apply, Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm, map_mul]
        | add y1 y2 h1 h2 =>
            simp only [mul_add, map_add, h1, h2]
    | add x1 x2 h1 h2 =>
        simp only [add_mul, map_add, h1, h2]

end General

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev PaperKf : Type := CommonPrimeCompletion (placeAtPrime S)

noncomputable def oneFactorAlgEquiv :
    ArithmeticTensorTupleBlock (places S) (tuple S) ≃ₐ[ℚ_[pNat S]] PaperKf S :=
  piTensorSubsingletonAlgEquiv (R := ℚ_[pNat S])
    (K := fun i : Unit => CommonPrimeCompletion (places S i (tuple S i)))

theorem oneFactorCanonicalAlgEquiv_constructed :
    Nonempty (ArithmeticTensorTupleBlock (places S) (tuple S) ≃ₐ[ℚ_[pNat S]] PaperKf S) :=
  ⟨oneFactorAlgEquiv S⟩

end LeanFormal.IUT.N8Closure.C7OneFactorAlgEquivConstructed2

end