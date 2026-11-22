import tmp.sheaf.xif.paper.C3TensorIndexBadEquivConcreteActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Source-level C3 tensor index / native bad map: actual data and obstruction

The previous file constructed only a cardinality-based equivalence. That is not
the paper's source index map, so it is NOT used here.

This file records the actual source-level data available from the concrete C3
donor and the native bad family:

* c3SourceBasePlace i := A.tensorPlaces i (A.tensorTuple i);
* c3SourceThetaValue j := A.thetaPacket.scale j;
* badSourceBasePlace b := b.1.

A source-level map would require an actual map
  Bad (nativePlaceSelection T) -> A.tensorIndex
together with a comparison of the two base fields, base places, and theta
values. None of these comparisons is constructed by the concrete donor: the C3
base field is I.initial.arithmetic.Fmod while the native bad base field is
T.arithmetic.Fmod, and the native initial-Theta data has no theta-value field.

Accordingly the map is kept as exact obstruction data, not fabricated. No
Fintype.equivOfCardEq or arbitrary index equivalence is used.

No True/PUnit, empty type, axiom, or sorry is used.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.C3TensorIndexBadSourceMapActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.ConcreteC3DonorAssemblyActual
open LeanFormal.IUT.XiFPaper.C3TensorIndexBadEquivConcreteActual

universe ua upi umon ui

variable {l : PrimeGeFive}
variable {I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7)}
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
variable (A : ConcreteC3DonorAssemblyActual (I := I) place)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual source base finite place of a concrete C3 tensor index. -/
noncomputable def c3SourceBasePlace (i : A.tensorIndex) :
    FinitePlaceAtPrime I.initial.arithmetic.Fmod A.p :=
  A.tensorPlaces i (A.tensorTuple i)

/-- The actual source theta value of a concrete C3 donor. -/
noncomputable def c3SourceThetaValue (j : SignedLabel l.value) : Real :=
  A.thetaPacket.scale j

/-- The actual native bad base finite place. -/
noncomputable def badSourceBasePlace (b : Bad (nativePlaceSelection T)) :
    NumberField.FinitePlace T.arithmetic.Fmod :=
  b.1

/-- The actual source-level map data required by the paper: an index map, a
base-field comparison, base-place compatibility, and theta-value compatibility.
The compatibility fields are exact propositions, not asserted. -/
structure C3TensorIndexBadSourceMapData where
  toIndex : Bad (nativePlaceSelection T) → A.tensorIndex
  baseField_compat : Prop
  basePlace_compat : Prop
  thetaValue_compat : Prop

/-- The exact obstruction: no source-level map with the required comparisons is
constructed. -/
def C3TensorIndexBadSourceMapObstruction : Prop :=
  Nonempty (C3TensorIndexBadSourceMapData (I := I) place A T)

/-- The exact base-field obstruction: the concrete C3 base field and the native
bad base field are not identified in the concrete data. -/
def C3TensorIndexBadBaseFieldObstruction : Prop :=
  Nonempty (I.initial.arithmetic.Fmod ≃+* T.arithmetic.Fmod)

/-- The actual C3 base-place projection is the donor tensor place. -/
theorem c3SourceBasePlace_apply (i : A.tensorIndex) :
    c3SourceBasePlace (I := I) place A i =
      A.tensorPlaces i (A.tensorTuple i) :=
  rfl

/-- The actual C3 theta-value projection is the donor theta packet scale. -/
theorem c3SourceThetaValue_apply (j : SignedLabel l.value) :
    c3SourceThetaValue (I := I) place A j = A.thetaPacket.scale j :=
  rfl

/-- The actual native bad base-place projection is b.1. -/
theorem badSourceBasePlace_apply (b : Bad (nativePlaceSelection T)) :
    badSourceBasePlace (l := l) T b = b.1 :=
  rfl

end LeanFormal.IUT.XiFPaper.C3TensorIndexBadSourceMapActual

end
