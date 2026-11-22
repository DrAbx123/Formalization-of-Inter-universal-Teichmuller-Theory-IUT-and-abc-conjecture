import tmp.sheaf.xif.paper.S1686HDDProvenanceActual
import tmp.sheaf.xif.paper.S1669HDDOutputDependenceActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionBoundary

/-! # S1688: faithful HDD source provenance from q-pilot/theta data

S1686 proved that the raw output record has no honest output-to-section
variation and that S1513/S1551/S1630/S1638 accept junk point families.
This file defines the faithful provenance object: an actual q-pilot/theta
output-to-section map from the source input to the HDD dependent local-field
points, with integral nonzero values and output dependence.  No inhabitant is
asserted; the current SourceDefinition31Data/Input data carry q-pilot/theta
scalars, not a local-field section map.

The q/theta scalar data (target_q, packetVolume) are output-independent, so
any section map factoring only through those scalars is constant in the
output; this is proved.  The exact first missing source field is the actual
q-pilot/theta output-to-section map. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1688HDDProvenanceSourceActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1513HDDOutputBindingActual
open LeanFormal.IUT.XiFPaper.S1630HDDOutputImageActual
open LeanFormal.IUT.XiFPaper.S1669HDDOutputDependenceActual
open LeanFormal.IUT.XiFPaper.S1686HDDProvenanceActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable (s : Finset (NumberField.FinitePlace ℚ))

/-- Any section map read from the source q/theta packet-profile scalars
is output-independent. -/
noncomputable def S1688ScalarSectionMap
    (factor : Real × Real → S1513DependentPoint s) :
    Theorem311Output I → S1513DependentPoint s :=
  fun _ => factor
    (I.packet.logVolume I.prime.base, I.packet.logVolume I.core.base)

theorem s1688ScalarSectionMap_output_independent
    (factor : Real × Real → S1513DependentPoint s)
    (o o' : Theorem311Output I) :
    S1688ScalarSectionMap I s factor o =
      S1688ScalarSectionMap I s factor o' :=
  rfl

/-- Exact faithful provenance object: an actual q-pilot/theta output-to-section
map from the source input, not the raw output record, with nonzero integral
HDD local-field values and output dependence.  No inhabitant is asserted. -/
structure S1688HDDSourceProvenance where
  /-- The actual q-pilot/theta output-to-section map supplied by the source. -/
  qPilotThetaSection : Theorem311Output I → S1513DependentPoint s
  /-- The induced HDD image section. -/
  outputSection : Theorem311Output I → S1513DependentPoint s
  /-- The HDD section is exactly the q-pilot/theta source section. -/
  outputSection_eq : outputSection = qPilotThetaSection
  point_ne_zero : ∀ (o) (v : {v : NumberField.FinitePlace ℚ // v ∈ s}),
    outputSection o v ≠ 0
  integral : ∀ (o) (v : {v : NumberField.FinitePlace ℚ // v ∈ s}),
    outputSection o v ∈ (CompletionIntegers v.1 : Set (Completion v.1))
  output_dependent : ∃ o o' : Theorem311Output I, outputSection o ≠ outputSection o'

/-- Exact first missing source field: the actual q-pilot/theta output-to-section
map.  This is not the minimal nondegeneracy predicate of S1669; it is the
source-side map itself. -/
def S1688QThetaOutputSectionMapMissing : Prop :=
  ¬ ∃ (F : Theorem311Output I → S1513DependentPoint s),
    (∀ (o) (v : {v : NumberField.FinitePlace ℚ // v ∈ s}),
      F o v ∈ (CompletionIntegers v.1 : Set (Completion v.1))) ∧
    (∃ o o' : Theorem311Output I, F o ≠ F o')

/-- The honest-output record supplies no such map; the source q/theta map is
the missing datum. -/
theorem s1688_outputRecord_provenance_missing :
    ¬ S1686HonestOutputProvenance (I := I) (s := s) :=
  s1686HonestOutputProvenance_false (I := I) (s := s)

#check s1688ScalarSectionMap_output_independent
#check S1688HDDSourceProvenance
#check S1688QThetaOutputSectionMapMissing
#check s1688_outputRecord_provenance_missing

end LeanFormal.IUT.XiFPaper.S1688HDDProvenanceSourceActual
end
