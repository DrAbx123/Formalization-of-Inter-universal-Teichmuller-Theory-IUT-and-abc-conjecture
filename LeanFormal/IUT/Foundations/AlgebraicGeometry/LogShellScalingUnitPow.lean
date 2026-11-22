import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceLogShellScaling
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace ABCBridge.LogShellScalingUnitPow

noncomputable section

open ABCBridge.SourceLogShellScaling
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits

/-- Unit scaling on the actual base log-shell: the `n`-th power generator
`(1/logShellScale) * unitLog (u^n)` is `n` times the generator of `u`. -/
theorem scaledLogGenerator_pow_eq_nsmul
    (u : (Integers sourceBaseLocalField)ˣ) (n : ℕ) :
    (⟨(logShellScale concreteRationalPrime : sourceBaseLocalField)⁻¹ *
        unitLog (K := sourceBaseLocalField) (u ^ n), ⟨u ^ n, rfl⟩⟩ :
      integralLogShell (K := sourceBaseLocalField) (p := concreteRationalPrime)) =
    n • (⟨(logShellScale concreteRationalPrime : sourceBaseLocalField)⁻¹ *
        unitLog (K := sourceBaseLocalField) u, ⟨u, rfl⟩⟩ :
      integralLogShell (K := sourceBaseLocalField) (p := concreteRationalPrime)) := by
  apply Subtype.ext
  change (logShellScale concreteRationalPrime : sourceBaseLocalField)⁻¹ *
      unitLog (K := sourceBaseLocalField) (u ^ n) =
    n • ((logShellScale concreteRationalPrime : sourceBaseLocalField)⁻¹ *
      unitLog (K := sourceBaseLocalField) u)
  rw [unitLog_pow (p := concreteRationalPrime)]
  simp only [nsmul_eq_mul]
  ring

/-- The unit/`nsmul` scaling identity for the actual source log-shell:
`e_L` of the `n`-th power log generator is `n` times `e_L` of the generator. -/
theorem LeanFormal.IUT.IUTII.Frobenioid.Example36.sourceTheaterLogShellMap_scaledLog_pow_nsmul
    (u : (Integers sourceBaseLocalField)ˣ) (n : ℕ) :
    LeanFormal.IUT.IUTII.Frobenioid.Example36.sourceTheaterLogShellMap
        ⟨(logShellScale concreteRationalPrime : sourceBaseLocalField)⁻¹ *
            unitLog (K := sourceBaseLocalField) (u ^ n),
          ⟨u ^ n, rfl⟩⟩ =
      n • LeanFormal.IUT.IUTII.Frobenioid.Example36.sourceTheaterLogShellMap
        ⟨(logShellScale concreteRationalPrime : sourceBaseLocalField)⁻¹ *
            unitLog (K := sourceBaseLocalField) u,
          ⟨u, rfl⟩⟩ := by
  rw [← map_nsmul]
  congr 1
  exact scaledLogGenerator_pow_eq_nsmul u n

end

end ABCBridge.LogShellScalingUnitPow
