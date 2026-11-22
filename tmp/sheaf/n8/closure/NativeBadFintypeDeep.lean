import tmp.sheaf.n8.closure.NativeBadFintypeSourceAttempt
import tmp.sheaf.n8.closure.NativeContractFieldsActualAttempt
import LeanFormal.IUT.IUTI.InitialTheta.SourceCompletion
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

/-!
# Deep audit: native bad-set finiteness

Task-521 searches SourceCompletion/signQuotient/tuple fields for a genuine
finiteness proof for V_mod_bad.  The search is negative.

Exact audited source fields:

1. SourceCompletionSignQuotient (SourceCompletion.lean:73-85):
   V                 : Set (NumberFieldPlace A.K)
   V_mod_bad         : Set (NumberField.FinitePlace A.Fmod)
   V_mod_bad_odd_residue_characteristic ...
   V_mod_bad_nonempty : V_mod_bad.Nonempty
   V_section, V_eq_section, V_mod_bijection, V_place_comap
   No Fintype/Set.Finite field for V_mod_bad.

2. SourceCompletionRecord (SourceCompletion.lean:488-543) / tuple
   (SourceDefinition31Quantifiers.lean:1581-1587):
   V, V_mod_bad, V_mod_bad_eq_source, epsilon; no finite field.

3. SourceNativeInitialThetaData (SourceDefinition31Quantifiers.lean:1640-1648):
   arithmetic, tuple, clauseA..clauseF only; no finite field.

4. SourceDefinition31NativeContractBridgeReduction.lean:135-140 explicitly:
   the contract SourcePlacePartition asks for Fintype Bad and Nat labels,
   "none of those is derivable from the native carriers".

5. SourcePlacePartition.badFinite (SourceDefinition31Boundary.lean:42) is a
   contract field, not a native field.  SourceDefinition31D4D9Supply.lean:248
   takes [Fintype (Bad selection)] as an explicit hypothesis.

Therefore the exact missing source theorem is

  Set.Finite X.S.tuple.source.V_mod_bad

or equivalently Nonempty (Fintype (NativeBadPlaces X)).  Neither is proved in
the audited native source.  No arbitrary Fintype, True, PUnit, axiom or sorry is
introduced.  This file only records the conditional constructor and the exact
gap; no source theorem is fabricated.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.NativeBadFintypeDeep

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeBadFintypeSourceAttempt
open LeanFormal.IUT.N8Closure.NativeContractFieldsActualAttempt
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace

variable {l : PrimeGeFive}

/-- The exact missing source finiteness card, stated directly on the completion
field rather than on the derived bad subtype. -/
def SourceBadFiniteMissing (X : N8NativeInput l) : Prop :=
  X.S.tuple.source.V_mod_bad.Finite

/-- Equality with the existing exact source-finiteness predicate. -/
theorem sourceBadFiniteMissing_iff (X : N8NativeInput l) :
    SourceBadFiniteMissing X ↔ NativeBadSetFiniteSource X := Iff.rfl

/-- The missing finite card is exactly equivalent to a native bad Fintype. -/
theorem nativeBadFintype_iff_missing (X : N8NativeInput l) :
    Nonempty (Fintype (NativeBadPlaces X)) ↔ SourceBadFiniteMissing X := by
  rw [sourceBadFiniteMissing_iff]
  exact nativeBadFintype_iff_sourceFinite X

/-- Exact conditional input card.  Supplying this card is an extra source
hypothesis; it is not derived from the native fields audited above. -/
structure SourceBadFiniteCard (X : N8NativeInput l) where
  finite : SourceBadFiniteMissing X

/-- The conditional card yields the exact source finite statement. -/
theorem sourceBadFinite_of_card (X : N8NativeInput l)
    (C : SourceBadFiniteCard X) : SourceBadFiniteMissing X :=
  C.finite

/-- The conditional card yields the native bad Fintype. -/
theorem nativeBadFintype_of_card (X : N8NativeInput l)
    (C : SourceBadFiniteCard X) :
    Nonempty (Fintype (NativeBadPlaces X)) :=
  (nativeBadFintype_iff_missing X).mpr C.finite

/-- The exact gap: no native field produces the finite card. -/
def NativeBadFintypeDeepGap (X : N8NativeInput l) : Prop :=
  SourceBadFiniteMissing X

/-- If the card is supplied, the existing source attempt supplies the actual
NativeBadPlaces Fintype construction. -/
theorem nativeBadFintypeDeep_of_card (X : N8NativeInput l)
    (C : SourceBadFiniteCard X) :
    Nonempty (Fintype (NativeBadPlaces X)) :=
  nativeBadFintype_of_card X C

end LeanFormal.IUT.N8Closure.NativeBadFintypeDeep
