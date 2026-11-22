import tmp.sheaf.n8.closure.EtaTorsionSourceQualification

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# Remaining Definition 3.1 donors: orbicurve, sections, cusp, compatibility

Native data does not construct the orbicurve/sections/cusp clauses or the five
arithmetic compatibility slots.  This file splits them into explicit source
subcards (`RemainingSourceCards`) and proves the corrected target with the four
qualification layers is equivalent to the torsion-qualified target.  Given the
subcards, `NativeDefinition31Objects` and `SourceDefinition31Data` are assembled
actually.  No arbitrary donor is fabricated.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeContractFieldsActualAttempt
open LeanFormal.IUT.N8Closure.NativeBadFintypeSourceAttempt
open LeanFormal.IUT.N8Closure.NativeBadFiniteTargetCorrection
open LeanFormal.IUT.N8Closure.NativeReductionRestActual
open LeanFormal.IUT.N8Closure.NativeQParameterActual
open LeanFormal.IUT.N8Closure.NativeSplitMultiplicativeAttempt
open LeanFormal.IUT.N8Closure.NativeTorsionClauseActual
open LeanFormal.IUT.N8Closure.EtaBadFiniteSourceActual
open LeanFormal.IUT.N8Closure.EtaNativeDefinition31ObjectsAssembly
open LeanFormal.IUT.N8Closure.EtaSourceWithBadFiniteCondition
open LeanFormal.IUT.N8Closure.EtaReductionRestAssemblyActual
open LeanFormal.IUT.N8Closure.EtaSplitCardSourceQualification
open LeanFormal.IUT.N8Closure.EtaSourceDefinition31NativeAttempt
open LeanFormal.IUT.N8Closure.EtaTorsionSourceQualification

namespace LeanFormal.IUT.N8Closure.EtaRemainingDonorsAssembly

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Explicit source subcards for the remaining contract fields. -/
structure RemainingSourceCards (X : N8NativeInput l) where
  /-- SOURCE subcard: orbicurve clause. -/
  orbicurve : SourceOrbicurveClause.{0, 0, 0}
  /-- SOURCE subcard: sections clause. -/
  sections : SourceSectionClause.{0, 0, 0}
  /-- SOURCE subcard: cusp clause. -/
  cusp : SourceCuspClause
  /-- SOURCE subcards: the five arithmetic compatibility slots. -/
  compatibility : NativeArithmeticCompatibilityTarget

/-- Actual target package from the subcards. -/
def remainingTargetsOfCards
    (torsion : SourceTorsionClause.{0, 0, 0} l)
    (C : RemainingSourceCards (X := X)) :
    NativeDefinition31RemainingTargets X where
  torsion := ⟨torsion⟩
  orbicurve := ⟨C.orbicurve⟩
  sections := ⟨C.sections⟩
  cusp := ⟨C.cusp⟩
  compatibility := C.compatibility

/-- Actual extraction of the subcards from the exact remaining targets. -/
noncomputable def cardsOfRemaining
    (R : NativeDefinition31RemainingTargets (X := X)) :
    RemainingSourceCards (X := X) where
  orbicurve := Classical.choice R.orbicurve
  sections := Classical.choice R.sections
  cusp := Classical.choice R.cusp
  compatibility := R.compatibility

/-- Corrected input with four qualification layers: bad-finite, split card,
full torsion clause, remaining source subcards. -/
structure SourceWithFourQualifications (X : N8NativeInput l) where
  badFinite : RequiredBadFiniteness (X := X)
  splitCard : NativeSplitMultiplicativeCard X
  torsion : SourceTorsionClause.{0, 0, 0} l
  cards : RemainingSourceCards (X := X)

def CorrectedDefinition31TargetWithRemainingCards : Prop :=
  Nonempty (SourceWithFourQualifications (l := l) X)

noncomputable def threeOfFour
    (I : SourceWithFourQualifications (X := X)) :
    SourceWithThreeQualifications (X := X) where
  badFinite := I.badFinite
  splitCard := I.splitCard
  torsion := I.torsion
  remaining := remainingTargetsOfCards (X := X) I.torsion I.cards

noncomputable def fourOfThree
    (I : SourceWithThreeQualifications (X := X)) :
    SourceWithFourQualifications (X := X) where
  badFinite := I.badFinite
  splitCard := I.splitCard
  torsion := I.torsion
  cards := cardsOfRemaining (X := X) I.remaining

theorem correctedTargetWithRemainingCards_iff_torsion :
    CorrectedDefinition31TargetWithRemainingCards (X := X) ↔
      CorrectedDefinition31TargetWithTorsion (X := X) := by
  constructor
  · rintro ⟨I⟩
    exact ⟨threeOfFour (X := X) I⟩
  · rintro ⟨I⟩
    exact ⟨fourOfThree (X := X) I⟩

/-- Actual assembly of NativeDefinition31Objects directly from the four
qualification layers. -/
noncomputable def nativeObjectsOfFour
    (I : SourceWithFourQualifications (X := X)) :
    NativeDefinition31Objects X where
  selectedPlaces := NativeSelectedPlaces X
  badPlaces := NativeBadPlaces X
  reduction := nativeReductionClauseOf X
    (nativeSourceWithBadFiniteOfSetFinite X I.badFinite)
    (reductionRestRemainingOfAssembly X I.splitCard)
  torsion := I.torsion
  orbicurve := I.cards.orbicurve
  sections := I.cards.sections
  cusp := I.cards.cusp
  arithmetic_reduction_compatibility :=
    I.cards.compatibility.arithmetic_reduction_compatibility
  arithmetic_reduction_compatibility_proved :=
    I.cards.compatibility.arithmetic_reduction_compatibility_proved
  arithmetic_torsion_compatibility :=
    I.cards.compatibility.arithmetic_torsion_compatibility
  arithmetic_torsion_compatibility_proved :=
    I.cards.compatibility.arithmetic_torsion_compatibility_proved
  arithmetic_orbicurve_compatibility :=
    I.cards.compatibility.arithmetic_orbicurve_compatibility
  arithmetic_orbicurve_compatibility_proved :=
    I.cards.compatibility.arithmetic_orbicurve_compatibility_proved
  arithmetic_section_compatibility :=
    I.cards.compatibility.arithmetic_section_compatibility
  arithmetic_section_compatibility_proved :=
    I.cards.compatibility.arithmetic_section_compatibility_proved
  arithmetic_cusp_compatibility :=
    I.cards.compatibility.arithmetic_cusp_compatibility
  arithmetic_cusp_compatibility_proved :=
    I.cards.compatibility.arithmetic_cusp_compatibility_proved

noncomputable def sourceDefinition31DataOfFour
    (I : SourceWithFourQualifications (X := X)) :
    SourceDefinition31Data.{0} l :=
  sourceDefinition31DataOfNativeObjects (X := X)
    (nativeObjectsOfFour (X := X) I)

theorem fourQualifications_assemble_sourceDefinition31Data
    (h : CorrectedDefinition31TargetWithRemainingCards (X := X)) :
    Nonempty (SourceDefinition31Data.{0} l) := by
  rcases h with ⟨I⟩
  exact ⟨sourceDefinition31DataOfFour (X := X) I⟩

/-- Exact source gaps for the remaining subcards.  They are not constructed by
native data; they are explicit source cards in the corrected target. -/
def OrbicurveSourceGap : Prop :=
  ¬ Nonempty (SourceOrbicurveClause.{0, 0, 0})

def SectionsSourceGap : Prop :=
  ¬ Nonempty (SourceSectionClause.{0, 0, 0})

def CuspSourceGap : Prop :=
  ¬ Nonempty (SourceCuspClause)

def ArithmeticCompatibilitySourceGap : Prop :=
  ¬ Nonempty (NativeArithmeticCompatibilityTarget)

end LeanFormal.IUT.N8Closure.EtaRemainingDonorsAssembly

end