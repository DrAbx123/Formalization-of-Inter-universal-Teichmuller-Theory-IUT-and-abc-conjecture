import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogShellVolumeConsumer
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithm
import LeanFormal.IUT.IUTIII.Theorem311.ConcreteFiniteModel

/-!
# ETA-6: actual integral structure S for etaAnab

The integral structure S is the production integral log-shell in the concrete
p-adic local field, together with the production log-shell volume container
and the actual finite-output Ind1/Ind2 invariance and Ind3 upper-semi laws.

This is not a free subset S: the integral part is literally
integralLogShell, the volume container is literally logShellVolumeConsumer, and
the Ind1/2/3 constraints are the actual fields of finiteOutput l.  No Real
adjustment or arbitrary subset is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaIntegralStructureSRoute

open scoped Padic NNReal

open LeanFormal.IUT
open LeanFormal.IUT.Foundations.LocalFields
open LeanFormal.IUT.Foundations.LocalFields.LogShellVolume
open LeanFormal.IUT.ConcreteFiniteTheorem311
open LeanFormal.IUT.LocalFieldLogarithm

variable (l : PrimeGeFive)
local instance : Fact (Nat.Prime l.value) := l.factPrime

/-- Actual integral structure S for etaAnab:
- the p-adic integral log-shell integral structure;
- the actual log-shell volume container;
- the actual finite-output Ind1/Ind2 invariance and Ind3 upper-semi laws. -/
structure EtaIntegralStructureS where
  integral : Set ℚ_[l.value]
  integral_eq_integralLogShell :
    integral = (integralLogShell (K := ℚ_[l.value]) (p := l.value) :
      Set ℚ_[l.value])
  volume : LogShellVolumeConsumer (K := ℚ_[l.value]) (p := l.value)
  finite : FiniteOutput l
  ind1_invariant : ∀ t c,
    finite.logVolume (ProcessionChoice.ind1Act t c) = finite.logVolume c
  ind2_invariant : ∀ t c,
    finite.logVolume (ProcessionChoice.ind2Act t c) = finite.logVolume c
  ind3_upper : ∀ n c,
    finite.logVolume c ≤ finite.logVolume (ProcessionChoice.ind3Lift n c)

/-- Actual S constructed from production data, with no free choice. -/
noncomputable def etaIntegralStructureS : EtaIntegralStructureS l where
  integral := (integralLogShell (K := ℚ_[l.value]) (p := l.value) :
    Set ℚ_[l.value])
  integral_eq_integralLogShell := rfl
  volume := logShellVolumeConsumer (K := ℚ_[l.value]) (p := l.value)
  finite := finiteOutput l
  ind1_invariant := (finiteOutput l).ind1_invariant
  ind2_invariant := (finiteOutput l).ind2_invariant
  ind3_upper := (finiteOutput l).ind3_upper

/-- The integral part is exactly the production integral log-shell. -/
theorem etaIntegralStructureS_integral_eq :
    (etaIntegralStructureS l).integral =
      (integralLogShell (K := ℚ_[l.value]) (p := l.value) :
        Set ℚ_[l.value]) :=
  (etaIntegralStructureS l).integral_eq_integralLogShell

/-- Ind1 invariance is the actual finite-output law. -/
theorem etaIntegralStructureS_ind1 (t : finiteLabel l)
    (c : ProcessionChoice l) :
    (etaIntegralStructureS l).finite.logVolume (ProcessionChoice.ind1Act t c) =
      (etaIntegralStructureS l).finite.logVolume c :=
  (etaIntegralStructureS l).ind1_invariant t c

/-- Ind2 invariance is the actual finite-output law. -/
theorem etaIntegralStructureS_ind2 (t : finiteLabel l)
    (c : ProcessionChoice l) :
    (etaIntegralStructureS l).finite.logVolume (ProcessionChoice.ind2Act t c) =
      (etaIntegralStructureS l).finite.logVolume c :=
  (etaIntegralStructureS l).ind2_invariant t c

/-- Ind3 upper-semi is the actual finite-output law. -/
theorem etaIntegralStructureS_ind3 (n : Nat) (c : ProcessionChoice l) :
    (etaIntegralStructureS l).finite.logVolume c ≤
      (etaIntegralStructureS l).finite.logVolume (ProcessionChoice.ind3Lift n c) :=
  (etaIntegralStructureS l).ind3_upper n c

end LeanFormal.IUT.N8Closure.EtaIntegralStructureSRoute
