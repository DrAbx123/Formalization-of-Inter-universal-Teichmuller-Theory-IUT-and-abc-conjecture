import tmp.sheaf.n8.closure.C1P6QUniformizerNormalization
import tmp.sheaf.n8.closure.C1P6RamificationTransportCondition
import LeanFormal.IUT.Foundations.NumberField.FinitePlaceExtension

/-!
# C1P6UnitResidueComparison

Using the actual q = π^n * unit normalization, define the residue comparison
of the normalized unit to the image of the base completion residue field.

`residueMap` is the production residue-field embedding of the finite-place
extension.  The necessary criterion is: if the chosen uniformizer itself lies
in the completion-map image, then `C1P6RangeCondition` forces the normalized
unit residue into the base residue image.  Its contrapositive is an exact
obstruction to the range condition.

The implication is the sole named gap; no arbitrary residue map is used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1P6UnitResidueComparison

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.C1P6RamificationTransport
open LeanFormal.IUT.N8Closure.C1P6RamificationTransportCondition
open LeanFormal.IUT.N8Closure.C1P6QUniformizerNormalization
open LeanFormal.IUT.NumberFieldFinitePlace
open IsDedekindDomain
open scoped NumberField

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual normalization data. -/
noncomputable def normData : C1P6QUniformizerNormalization X :=
  c1P6QUniformizerNormalization X

/-- Residue of the normalized unit in the top completion-integer residue field. -/
noncomputable def unitResidue : IsLocalRing.ResidueField (TopIntegers X) :=
  IsLocalRing.residue (TopIntegers X) ((normData X).unit : TopIntegers X)

/-- Exact unit residue comparison to the production base residue-field image. -/
def C1P6UnitResidueComparison : Prop :=
  unitResidue X ∈ Set.range
    (NumberFieldFinitePlace.residueMap (k := X.S.arithmetic.Fmod) (topPlace X))

end LeanFormal.IUT.N8Closure.C1P6UnitResidueComparison