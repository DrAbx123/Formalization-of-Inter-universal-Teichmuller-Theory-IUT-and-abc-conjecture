import tmp.sheaf.xif.paper.C3TensorIndexBadSourceMapActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Base field comparison: concrete C3 donor vs native source arithmetic

The concrete C3 donor uses the base field
  I.initial.arithmetic.Fmod,
while the native initial-Theta source uses
  T.arithmetic.Fmod.

Both are actual NumberField types with their actual arithmetic data. What the
tree does not provide is an actual comparison between them: neither a type
equality nor a ring equivalence is constructed by the concrete donor or by the
native source data. This file records that exact situation:

* actual projections of the two base fields and their NumberField instances;
* the conditional construction of a ring equivalence from an explicit actual
  field equality;
* exact obstruction propositions for field equality and ring equivalence.

No cardinality equivalence, arbitrary ring isomorphism, or fake equality is
used. No True/PUnit, empty type, axiom, or sorry is used.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.BaseFieldComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.ConcreteC3DonorAssemblyActual

universe ua upi umon ui

variable {l : PrimeGeFive}
variable {I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7)}
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
variable (A : ConcreteC3DonorAssemblyActual (I := I) place)
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The actual concrete C3 base field. -/
abbrev C3BaseField : Type :=
  I.initial.arithmetic.Fmod

/-- The actual native source base field. -/
abbrev NativeBaseField : Type :=
  T.arithmetic.Fmod

/-- The actual NumberField structure on the concrete C3 base field. -/
theorem c3BaseField_numberField : NumberField (C3BaseField (I := I)) :=
  inferInstance

/-- The actual NumberField structure on the native base field. -/
theorem nativeBaseField_numberField : NumberField (NativeBaseField (l := l) T) :=
  inferInstance

/-- Exact obstruction: the two actual base fields are not known to be equal. -/
def BaseFieldEqualityObstruction : Prop :=
  Nonempty (C3BaseField (I := I) = NativeBaseField (l := l) T)

/-- Exact obstruction: no actual ring equivalence between the two base fields is
constructed by the source data. -/
def BaseFieldRingEquivObstruction : Prop :=
  Nonempty (C3BaseField (I := I) ≃+* NativeBaseField (l := l) T)

/-- A ring equivalence between the two base fields, conditional on an explicit
actual type equality. -/
noncomputable def baseFieldRingEquivOfEq
    (h : C3BaseField (I := I) = NativeBaseField (l := l) T) :
    C3BaseField (I := I) ≃+* NativeBaseField (l := l) T :=
  h ▸ RingEquiv.refl (C3BaseField (I := I))

/-- The actual base-field comparison data, when an explicit ring equivalence is
available. The field records the actual equivalence; it is not asserted to
exist. -/
structure BaseFieldComparisonData where
  fieldEquiv : C3BaseField (I := I) ≃+* NativeBaseField (l := l) T

/-- Exact source obstruction: existence of an actual base-field comparison. -/
def BaseFieldComparisonObstruction : Prop :=
  Nonempty (BaseFieldComparisonData (I := I) T)

/-- The conditional comparison from an explicit actual ring equivalence. -/
noncomputable def baseFieldComparisonOfEquiv
    (e : C3BaseField (I := I) ≃+* NativeBaseField (l := l) T) :
    BaseFieldComparisonData (I := I) T where
  fieldEquiv := e

/-- The conditional comparison from an explicit actual field equality. -/
noncomputable def baseFieldComparisonOfEq
    (h : C3BaseField (I := I) = NativeBaseField (l := l) T) :
    BaseFieldComparisonData (I := I) T :=
  baseFieldComparisonOfEquiv (I := I) T (baseFieldRingEquivOfEq (I := I) T h)

end LeanFormal.IUT.XiFPaper.BaseFieldComparisonActual

end
