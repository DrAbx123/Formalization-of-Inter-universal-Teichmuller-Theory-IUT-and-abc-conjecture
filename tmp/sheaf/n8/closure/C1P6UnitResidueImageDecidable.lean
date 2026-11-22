import tmp.sheaf.n8.closure.C1P6UnitResidueComparison

/-!
# C1P6UnitResidueImageDecidable

Decidability analysis of `unitResidue ∈ base residue image`.

The comparison is a membership in the range of the actual production
`residueMap`.  If the two residue fields are finite (as they are for local
fields of number fields), the membership is decidable by finite enumeration
of the base residue field.  The file proves this conditional decidability and
records the exact missing source theorem needed to decide the actual case: a
finite/enumerated residue-extension comparison.  It does not assume an
arbitrary residue map; the production `residueMap` is used.

No production `Finite`/`Fintype` instance for the completion residue fields is
currently exposed, so the actual comparison is not decided here.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1P6UnitResidueImageDecidable

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C1P6RamificationTransport
open LeanFormal.IUT.N8Closure.C1P6QUniformizerNormalization
open LeanFormal.IUT.N8Closure.C1P6UnitResidueComparison
open LeanFormal.IUT.NumberFieldFinitePlace
open IsDedekindDomain
open scoped NumberField

variable {l : PrimeGeFive} (X : N8NativeInput l)

abbrev TopResidueField (X : N8NativeInput l) : Type :=
  IsLocalRing.ResidueField (TopIntegers X)

abbrev BaseResidueField (X : N8NativeInput l) : Type :=
  IsLocalRing.ResidueField
    ((basePlace X).maximalIdeal.adicCompletionIntegers X.S.arithmetic.Fmod)

/-- Conditional decidability: finite base/top residue fields decide the actual
range membership by finite enumeration. -/
noncomputable def c1P6UnitResidueComparison_decidable_of_finite
    [Finite (TopResidueField X)] [Finite (BaseResidueField X)] :
    Decidable (C1P6UnitResidueComparison X) := by
  classical
  haveI : Fintype (TopResidueField X) := Fintype.ofFinite _
  haveI : Fintype (BaseResidueField X) := Fintype.ofFinite _
  infer_instance

end LeanFormal.IUT.N8Closure.C1P6UnitResidueImageDecidable