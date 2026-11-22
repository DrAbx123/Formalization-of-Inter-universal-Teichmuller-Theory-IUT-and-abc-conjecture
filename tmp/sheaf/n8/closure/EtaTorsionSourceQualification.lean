import tmp.sheaf.n8.closure.EtaSplitCardSourceQualification
import tmp.sheaf.n8.closure.NativeTorsionClauseActual
import tmp.sheaf.n8.closure.EtaSourceDefinition31NativeAttempt

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# Third source qualification: full torsion clause

Only `SourceTorsionDatum` is actual from native Clause C; the full
`SourceTorsionClause` (six-torsion carrier, GL2 surjectivity, independence,
l-compatibility) is missing.  It is added as the third explicit source
qualification/card.  With the three cards plus the exact remaining targets,
the actual `NativeDefinition31Objects` and `SourceDefinition31Data` are
assembled; no arbitrary clause is fabricated.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.TorsionCarrierReduction
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

namespace LeanFormal.IUT.N8Closure.EtaTorsionSourceQualification

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual torsion datum from native Clause C (partial: not the full clause). -/
noncomputable def torsionDatumActual :
    SourceTorsionDatum l X.S.arithmetic :=
  nativeTorsionDatum X

/-- Corrected Definition 3.1 input with three explicit source cards. -/
structure SourceWithThreeQualifications (X : N8NativeInput l) where
  /-- SOURCE card 1: `V_mod_bad` is finite. -/
  badFinite : RequiredBadFiniteness (X := X)
  /-- SOURCE card 2: split-multiplicative reduction. -/
  splitCard : NativeSplitMultiplicativeCard X
  /-- SOURCE card 3: full torsion clause. -/
  torsion : SourceTorsionClause.{0, 0, 0} l
  /-- Exact remaining full-clause targets. -/
  remaining : NativeDefinition31RemainingTargets X

def CorrectedDefinition31TargetWithTorsion : Prop :=
  Nonempty (SourceWithThreeQualifications (l := l) X)

theorem threeQualifications_badFinite
    (h : CorrectedDefinition31TargetWithTorsion (X := X)) :
    RequiredBadFiniteness (X := X) := h.some.badFinite

theorem threeQualifications_split
    (h : CorrectedDefinition31TargetWithTorsion (X := X)) :
    NativeSplitMultiplicativeTarget X := h.some.splitCard.splitMultiplicativeReduction

def threeQualifications_torsion
    (h : CorrectedDefinition31TargetWithTorsion (X := X)) :
    SourceTorsionClause.{0, 0, 0} l := h.some.torsion

noncomputable def twoOfThree
    (I : SourceWithThreeQualifications (X := X)) :
    SourceWithTwoQualifications (X := X) where
  badFinite := I.badFinite
  splitCard := I.splitCard
  remaining := I.remaining

noncomputable def threeOfTwo
    (I : SourceWithTwoQualifications (X := X)) :
    SourceWithThreeQualifications (X := X) where
  badFinite := I.badFinite
  splitCard := I.splitCard
  torsion := Classical.choice I.remaining.torsion
  remaining := I.remaining

theorem correctedTargetWithTorsion_iff_twoQualifications :
    CorrectedDefinition31TargetWithTorsion (X := X) ↔
      CorrectedDefinition31TargetWithSplit (X := X) := by
  constructor
  · rintro ⟨I⟩
    exact ⟨twoOfThree (X := X) I⟩
  · rintro ⟨I⟩
    exact ⟨threeOfTwo (X := X) I⟩

/-- Actual assembly of NativeDefinition31Objects from the three cards and the
remaining target proofs. -/
noncomputable def nativeObjectsOfThree
    (I : SourceWithThreeQualifications (X := X)) :
    NativeDefinition31Objects X where
  selectedPlaces := NativeSelectedPlaces X
  badPlaces := NativeBadPlaces X
  reduction := nativeReductionClauseOf X
    (nativeSourceWithBadFiniteOfSetFinite X I.badFinite)
    (reductionRestRemainingOfAssembly X I.splitCard)
  torsion := I.torsion
  orbicurve := Classical.choice I.remaining.orbicurve
  sections := Classical.choice I.remaining.sections
  cusp := Classical.choice I.remaining.cusp
  arithmetic_reduction_compatibility :=
    I.remaining.compatibility.arithmetic_reduction_compatibility
  arithmetic_reduction_compatibility_proved :=
    I.remaining.compatibility.arithmetic_reduction_compatibility_proved
  arithmetic_torsion_compatibility :=
    I.remaining.compatibility.arithmetic_torsion_compatibility
  arithmetic_torsion_compatibility_proved :=
    I.remaining.compatibility.arithmetic_torsion_compatibility_proved
  arithmetic_orbicurve_compatibility :=
    I.remaining.compatibility.arithmetic_orbicurve_compatibility
  arithmetic_orbicurve_compatibility_proved :=
    I.remaining.compatibility.arithmetic_orbicurve_compatibility_proved
  arithmetic_section_compatibility :=
    I.remaining.compatibility.arithmetic_section_compatibility
  arithmetic_section_compatibility_proved :=
    I.remaining.compatibility.arithmetic_section_compatibility_proved
  arithmetic_cusp_compatibility :=
    I.remaining.compatibility.arithmetic_cusp_compatibility
  arithmetic_cusp_compatibility_proved :=
    I.remaining.compatibility.arithmetic_cusp_compatibility_proved

/-- Actual SourceDefinition31Data assembly from the three cards. -/
noncomputable def sourceDefinition31DataOfThree
    (I : SourceWithThreeQualifications (X := X)) :
    SourceDefinition31Data.{0} l :=
  sourceDefinition31DataOfNativeObjects (X := X)
    (nativeObjectsOfThree (X := X) I)

theorem threeQualifications_assemble_sourceDefinition31Data
    (h : CorrectedDefinition31TargetWithTorsion (X := X)) :
    Nonempty (SourceDefinition31Data.{0} l) := by
  rcases h with ⟨I⟩
  exact ⟨sourceDefinition31DataOfThree (X := X) I⟩

/-- Exact gap: no full SourceTorsionClause is constructed from native data;
only the datum is actual. -/
def TorsionClauseSourceGap : Prop :=
  ¬ Nonempty (SourceTorsionClause.{0, 0, 0} l)

end LeanFormal.IUT.N8Closure.EtaTorsionSourceQualification

end