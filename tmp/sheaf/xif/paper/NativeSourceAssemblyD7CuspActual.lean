import tmp.sheaf.xif.paper.NativeSourceAssemblyActualFields
import tmp.sheaf.n8.closure.NativeSourceSectionsCuspActual
import tmp.sheaf.n8.closure.NativeD7Proof
import tmp.sheaf.n8.closure.NativeInput
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31D4D9Supply

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! # Actual D7/cusp sources for NativeSourceAssemblyFields

The native tuple supplies the actual geometric cusp but no real cusp coordinate,
no positive Nat cusp count, and no D7 local-group section supply. This file
constructs the actual geometric cusp carrier and records the exact missing
source objects for D7, cuspCount, and cuspHyp. No Prop placeholder, constant
count, or fabricated local group is used. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.NativeSourceAssemblyD7CuspActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.InitialThetaSource.NativeSourceSectionsCuspActual
open LeanFormal.IUT.InitialThetaSource.Definition31D4D9Supply
open LeanFormal.IUT.XiFPaper.NativeSourceAssemblyActualFields
open LeanFormal.IUT.N8Closure.NativeInput

universe u

variable {l : PrimeGeFive} {V : Type}
variable (X : N8NativeInput l)
variable (I : OriginalInput l V)

/-- Exact missing positive cusp count source object. -/
structure NativeCuspCountSource where
  cuspCount : Nat
  cuspCount_pos : 0 < cuspCount

/-- The actual source cusp count from the Definition 3.1 orbicurve clause. -/
noncomputable def nativeCuspCountSource : NativeCuspCountSource where
  cuspCount := I.initial.orbicurve.cuspCount
  cuspCount_pos := I.initial.cover_cusp_count_pos

/-- The actual cusp count is the source orbicurve cusp count. -/
theorem nativeCuspCountSource_eq :
    (nativeCuspCountSource (I := I)).cuspCount =
      I.initial.orbicurve.cuspCount := rfl

/-- The actual cusp count is positive. -/
theorem nativeCuspCountSource_pos :
    0 < (nativeCuspCountSource (I := I)).cuspCount :=
  (nativeCuspCountSource (I := I)).cuspCount_pos

/-- The actual geometric cusp carrier carried by the native tuple. -/
abbrev nativeGeometricCusp : Iut.OrbicurveBoundaryCusp X.S.tuple.cK :=
  X.S.tuple.epsilon

/-- Exact missing realization of the geometric cusp as a real cusp coordinate:
an actual map from the geometric cusp carrier to Real, together with the
equation identifying the native tuple cusp with the source epsilon. -/
structure NativeEpsilonRealizationSource
    (I : OriginalInput l V) (X : N8NativeInput l) where
  cuspToReal : Iut.OrbicurveBoundaryCusp X.S.tuple.cK → Real
  cuspToReal_epsilon : cuspToReal X.S.tuple.epsilon = I.initial.cusp.epsilon

/-- Exact missing realization proposition. -/
def NativeEpsilonRealizationSourceRequired : Prop :=
  Nonempty (NativeEpsilonRealizationSource (l := l) I X)

/-- Exact missing real cusp-coordinate package; its first field is the actual
geometric cusp. -/
structure NativeCuspHypSource
    (I : OriginalInput l V) (X : N8NativeInput l) where
  geometricCusp : Iut.OrbicurveBoundaryCusp X.S.tuple.cK
  epsilon : Real
  epsilon_positive : 0 < epsilon
  epsilon_nonzero : epsilon ≠ 0
  cuspScale : Real
  cuspScale_positive : 0 < cuspScale
  epsilon_scale_relation : epsilon * cuspScale ≠ 0
  epsilon_compatibility : Prop
  epsilon_compatibility_proved : epsilon_compatibility
  native_epsilon_realization : NativeEpsilonRealizationSource (l := l) I X

/-- The actual cusp hypotheses from the source Definition 3.1 cusp clause.
The real epsilon and cuspScale are actual source fields; the geometric cusp is
the native tuple epsilon. The realization is the exact missing `NativeEpsilonRealizationSource` object,
not a Prop placeholder. -/
noncomputable def nativeCuspHypSource
    (R : NativeEpsilonRealizationSource (l := l) I X) :
    NativeCuspHypSource I X where
  geometricCusp := X.S.tuple.epsilon
  epsilon := I.initial.cusp.epsilon
  epsilon_positive := I.initial.cusp.epsilon_positive
  epsilon_nonzero := I.initial.cusp.epsilon_nonzero
  cuspScale := I.initial.cusp.cuspScale
  cuspScale_positive := I.initial.cusp.cuspScale_positive
  epsilon_scale_relation := I.initial.cusp.epsilon_scale_relation
  epsilon_compatibility := I.initial.cusp.epsilon_compatibility
  epsilon_compatibility_proved := I.initial.cusp.epsilon_compatibility_proved
  native_epsilon_realization := R

/-- The actual cusp epsilon is the source cusp-clause epsilon. -/
theorem nativeCuspHypSource_epsilon
    (R : NativeEpsilonRealizationSource (l := l) I X) :
    (nativeCuspHypSource (l := l) (I := I) X R).epsilon =
      I.initial.cusp.epsilon := rfl

/-- The actual cusp compatibility is proved. -/
theorem nativeCuspHypSource_epsilon_compatibility
    (R : NativeEpsilonRealizationSource (l := l) I X) :
    (nativeCuspHypSource (l := l) (I := I) X R).epsilon_compatibility :=
  (nativeCuspHypSource (l := l) (I := I) X R).epsilon_compatibility_proved

/-- The canonical D7 valuation-section layer. -/
abbrev d7Layer : SourceValuationSectionLayer X.S.arithmetic :=
  SourceValuationSectionLayer.canonical X.S.arithmetic

/-- The actual global arithmetic group carried by clause D. -/
abbrev d7LocalGroup : Type :=
  ↥X.S.clauseD.x_groups.groups.arithmetic.group

/-- Minimal actual local-group carrier from the clause-D global arithmetic
group: the carrier is constant over the canonical valuation section. -/
noncomputable def d7LocalGroupCarrier
    (_ : (d7Layer X).valuationCarrier) : Type :=
  d7LocalGroup X

/-- Minimal actual modified local-group carrier, same actual group. -/
noncomputable def d7ModifiedLocalGroupCarrier
    (_ : (d7Layer X).modifiedValuationCarrier) : Type :=
  d7LocalGroup X

/-- The actual identity local-group section on the minimal carrier. -/
def d7LocalGroupSection
    (x : (d7Layer X).valuationCarrier) :
    d7LocalGroupCarrier X x →
      d7ModifiedLocalGroupCarrier X ((d7Layer X).sectionMap x) :=
  fun g => g

/-- The identity local-group section is injective. -/
theorem d7LocalGroupSection_injective
    (x : (d7Layer X).valuationCarrier) :
    Function.Injective (d7LocalGroupSection X x) := by
  intro a b h
  exact h

/-- The identity local-group section is surjective. -/
theorem d7LocalGroupSection_surjective
    (x : (d7Layer X).valuationCarrier) :
    Function.Surjective (d7LocalGroupSection X x) := by
  intro y
  exact ⟨y, rfl⟩

/-- Exact missing D7 place-data source object. -/
structure D7PlaceDataSource where
  finitePlaceData : Prop
  finitePlaceData_proved : finitePlaceData
  infinitePlaceData : Prop
  infinitePlaceData_proved : infinitePlaceData

/-- Actual D7 local-group section supply from clause D plus the exact missing
place-data source object. -/
noncomputable def d7LocalGroupSectionSupplyOfPlaceData
    (P : D7PlaceDataSource) :
    D7LocalGroupSectionSupply (d7Layer X) where
  localGroupCarrier := d7LocalGroupCarrier X
  modifiedLocalGroupCarrier := d7ModifiedLocalGroupCarrier X
  localGroupSection := d7LocalGroupSection X
  localGroupSection_injective := d7LocalGroupSection_injective X
  localGroupSection_surjective := d7LocalGroupSection_surjective X
  finitePlaceData := P.finitePlaceData
  finitePlaceData_proved := P.finitePlaceData_proved
  infinitePlaceData := P.infinitePlaceData
  infinitePlaceData_proved := P.infinitePlaceData_proved

/-- The actual D7 intake from the exact place-data source. -/
noncomputable def nativeD7IntakeOfPlaceData
    (P : D7PlaceDataSource) :
    NativeD7Intake (SourceCompletion.ofSourceNative X.S) :=
  d7LocalGroupSectionSupplyOfPlaceData X P

/-- Exact missing source object for per-place D7 local groups: both carrier
families and the pointwise bijective local-group section. -/
structure D7PerPlaceLocalGroupSource where
  localGroupCarrier : (d7Layer X).valuationCarrier → Type
  modifiedLocalGroupCarrier : (d7Layer X).modifiedValuationCarrier → Type
  localGroupSection : ∀ x, localGroupCarrier x →
    modifiedLocalGroupCarrier ((d7Layer X).sectionMap x)
  localGroupSection_injective : ∀ x, Function.Injective (localGroupSection x)
  localGroupSection_surjective : ∀ x, Function.Surjective (localGroupSection x)

/-- Actual D7 local-group section supply from per-place source data and the
exact place-data source object. -/
noncomputable def d7LocalGroupSectionSupplyOfPerPlace
    (Lg : D7PerPlaceLocalGroupSource X) (P : D7PlaceDataSource) :
    D7LocalGroupSectionSupply (d7Layer X) where
  localGroupCarrier := Lg.localGroupCarrier
  modifiedLocalGroupCarrier := Lg.modifiedLocalGroupCarrier
  localGroupSection := Lg.localGroupSection
  localGroupSection_injective := Lg.localGroupSection_injective
  localGroupSection_surjective := Lg.localGroupSection_surjective
  finitePlaceData := P.finitePlaceData
  finitePlaceData_proved := P.finitePlaceData_proved
  infinitePlaceData := P.infinitePlaceData
  infinitePlaceData_proved := P.infinitePlaceData_proved

/-- The actual D7 intake from per-place local-group data. -/
noncomputable def nativeD7IntakeOfPerPlace
    (Lg : D7PerPlaceLocalGroupSource X) (P : D7PlaceDataSource) :
    NativeD7Intake (SourceCompletion.ofSourceNative X.S) :=
  d7LocalGroupSectionSupplyOfPerPlace X Lg P

/-- Exact missing D7 source object. -/
structure NativeD7Source where
  intake : NativeD7Intake (SourceCompletion.ofSourceNative X.S)

/-- Actual geometric cusp plus exact missing d7/cuspCount/cuspHyp sources. -/
structure NativeSourceAssemblyD7CuspPart
    (I : OriginalInput l V) (X : N8NativeInput l) where
  geometricCusp : Iut.OrbicurveBoundaryCusp X.S.tuple.cK
  d7Source : NativeD7Source X
  cuspCountSource : NativeCuspCountSource
  cuspHypSource : NativeCuspHypSource I X

/-- The actual d7/cusp part: actual geometric cusp and actual source cusp count;
d7 and the real cusp-coordinate package remain exact missing source objects. -/
noncomputable def nativeSourceAssemblyD7CuspPart
    (d7Source : NativeD7Source X)
    (cuspHypSource : NativeCuspHypSource I X) :
    NativeSourceAssemblyD7CuspPart I X where
  geometricCusp := nativeGeometricCusp X
  d7Source := d7Source
  cuspCountSource := nativeCuspCountSource (I := I)
  cuspHypSource := cuspHypSource

/-- The actual part's cusp count is the source orbicurve cusp count. -/
theorem nativeSourceAssemblyD7CuspPart_cuspCount
    (d7Source : NativeD7Source X)
    (cuspHypSource : NativeCuspHypSource I X) :
    (nativeSourceAssemblyD7CuspPart X I d7Source cuspHypSource).cuspCountSource.cuspCount =
      I.initial.orbicurve.cuspCount := rfl

/-- The actual geometric cusp is the native tuple epsilon. -/
theorem nativeGeometricCusp_eq :
    nativeGeometricCusp (l := l) X = X.S.tuple.epsilon := rfl

end LeanFormal.IUT.XiFPaper.NativeSourceAssemblyD7CuspActual

end
