import tmp.sheaf.n8.closure.NativeSourceReductionActual
import tmp.sheaf.n8.closure.NativeC3

/-! # Actual NativeBadLift from lying-over

For every bad moduli place b : Bad (nativePlaceSelection T), a finite F-place over b exists by comap_surjective. This removes NativeBadLift from the explicit source-field list; the lift is actual, not a hypothesis.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)

/-- Actual finite F-place above each bad moduli place, via lying-over. -/
noncomputable def nativeBadLift : NativeBadLift T.arithmetic (nativePlaceSelection T) where
  lift b := Classical.choose
    (NumberFieldFinitePlace.comap_surjective (K := T.arithmetic.F) b.1)
  lift_comap b := Classical.choose_spec
    (NumberFieldFinitePlace.comap_surjective (K := T.arithmetic.F) b.1)

end LeanFormal.IUT.N8Closure
end