import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceLogLinkCompatibility
import LeanFormal.IUT.IUTII.Frobenioid.Example36LogShellFrobeniusAction
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellActualTensorSpan
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIndexArithmetic
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

namespace ABCBridge.SourceLogShellScaling

noncomputable section

universe u

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped NumberField

local instance sourceLogShellScalingGaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance sourceLogShellScalingFivePrime : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

section GenericLogShellScaling

variable {K : Type u} [NormedField K] [CharZero K] [CompleteSpace K]
  [IsUltrametricDist K] [ProperSpace K]
  {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] K]

/-- The actual p-fold scaling on the scaled log-shell built from the actual
integral-scalar closure theorem. -/
noncomputable def integralLogShellPScaling :
    integralLogShell (K := K) (p := p) →+ integralLogShell (K := K) (p := p) where
  toFun x :=
    ⟨(p : K) * (x : K), by
      have h := integralLogShell_padicInt_mul_mem (K := K) (p := p)
        (z := (p : ℤ_[p])) x.property
      simpa only [PadicInt.coe_natCast, map_natCast] using h⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [mul_add]

@[simp] theorem integralLogShellPScaling_apply
    (x : integralLogShell (K := K) (p := p)) :
    (integralLogShellPScaling (K := K) (p := p) x : K) = (p : K) * (x : K) :=
  rfl

end GenericLogShellScaling

/-- The actual base rational local field below the concrete place. -/
abbrev sourceBaseLocalField : Type := PadicScalarField concretePlace

/-- The actual local field of the source theater. -/
abbrev sourceTheaterLocalField : Type := concreteLogShellField

/-- `e_L`/p-scaling compatibility: the actual source-theater log-shell
transport commutes with the p-fold scaling on the scaled log-shells. -/
theorem sourceTheaterLogShellMap_pScaling
    (x : integralLogShell (K := sourceBaseLocalField) (p := concreteRationalPrime)) :
    sourceTheaterLogShellMap
        (integralLogShellPScaling (K := sourceBaseLocalField)
          (p := concreteRationalPrime) x) =
      integralLogShellPScaling (K := sourceTheaterLocalField)
        (p := concreteRationalPrime)
        (sourceTheaterLogShellMap x) := by
  apply Subtype.ext
  simp only [integralLogShellPScaling_apply, sourceTheaterLogShellMap,
    integralLogShellTransport_apply_coe, map_mul, map_natCast]

/-- Unit scaling of the scaled log-Kummer generators under the actual
source-theater transport: powering the unit multiplies the scaled logarithm
by the exponent, and `e_L` preserves that identity. -/
theorem sourceTheaterLogShellMap_scaledLog_pow
    (u : (Integers sourceBaseLocalField)ˣ) (n : ℕ) :
    sourceTheaterLogShellMap
        ⟨(logShellScale concreteRationalPrime : sourceBaseLocalField)⁻¹ *
            unitLog (K := sourceBaseLocalField) (u ^ n),
          ⟨u ^ n, rfl⟩⟩ =
      ⟨(logShellScale concreteRationalPrime : sourceTheaterLocalField)⁻¹ *
          unitLog (K := sourceTheaterLocalField)
            (integralUnitMapOfMapsIntegers sourceTheaterScalarMap
              (fun _ hx => sourceTheaterScalarMap_mem_integers hx) (u ^ n)),
        ⟨integralUnitMapOfMapsIntegers sourceTheaterScalarMap
            (fun _ hx => sourceTheaterScalarMap_mem_integers hx) (u ^ n), rfl⟩⟩ := by
  exact sourceTheaterLogShellMap_scaledLog (u ^ n)

/-- p-fold scaling preserves the actual rational span of the integral
log-shell pure tensors in the source IQ tensor packet. -/
theorem sourceLogShellActualIQTensor_pScaling_mem {ι : Type u} [Finite ι]
    (D : ι → SourceLogShellDatum) (x : SourceLogShellActualIQTensor D) :
    (concreteRationalPrime : ℚ) • x ∈
      Submodule.span ℚ (sourceLogShellActualIntegralTensors D) := by
  rw [sourceLogShellActualIntegralTensors_span_eq_top]
  exact Submodule.mem_top


end

end ABCBridge.SourceLogShellScaling
