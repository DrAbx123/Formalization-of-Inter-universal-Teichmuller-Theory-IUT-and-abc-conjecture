import tmp.sheaf.n8.closure.NativeLocalReductionDisjointAlt
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction

/-!
# Closed native bad-set finiteness

This file integrates

* NativeBadFintypeProof.nativeBadSetFinite_of_localDisjoint (finite-good-
  reduction route), and
* NativeLocalReductionDisjointAlt.nativeLocalReductionDisjoint_alt (the
  minimal-discriminant proof of presentation-independent local disjointness).

The result is the unconditional-in-source theorem
  X.S.tuple.source.V_mod_bad.Finite
and the corresponding actual Fintype construction. No arbitrary Fintype,
axiom, True, PUnit, or sorry is introduced; the Fintype is obtained by
Classical.choice from the proved Nonempty.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.N8Closure
namespace NativeBadFintypeClosed

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeReductionFieldsActual
open LeanFormal.IUT.N8Closure.NativeBadFintypeProof
open LeanFormal.IUT.N8Closure.NativeLocalReductionDisjointAlt
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction

variable {l : PrimeGeFive}
universe u

/-- Unconditional-in-source finiteness of the native bad moduli set. -/
theorem nativeBadSetFinite
    (X : N8NativeInput l) :
    X.S.tuple.source.V_mod_bad.Finite :=
  nativeBadSetFinite_of_localDisjoint X
    nativeLocalReductionDisjoint_alt

/-- Unconditional-in-source existence of a Fintype on the native bad places. -/
theorem nativeBadFintype_nonempty
    (X : N8NativeInput l) :
    Nonempty (Fintype (Bad (nativePlaceSelection X.S))) :=
  nativeBadFintype_of_localDisjoint X
    nativeLocalReductionDisjoint_alt

/-- The actual Fintype construction on the native bad places. -/
noncomputable def nativeBadFintype
    (X : N8NativeInput l) :
    Fintype (Bad (nativePlaceSelection X.S)) :=
  Classical.choice (nativeBadFintype_nonempty X)

/-- The same finiteness as a direct theorem on a native source datum. -/
theorem nativeBadSetFinite_source
    (X : N8NativeInput l) :
    Set.Finite X.S.tuple.source.V_mod_bad :=
  nativeBadSetFinite X

end NativeBadFintypeClosed
end LeanFormal.IUT.N8Closure
end
