import tmp.sheaf.xif.paper.NativeSourceAssemblyFieldsActual
import tmp.sheaf.n8.closure.NativeSourceOrbicurveActual
import tmp.sheaf.n8.closure.NativeOrbicurveCountProof

/-!
# Actual exact-sequence data and the missing splitting section

Clause D supplies the actual profinite fundamental exact sequence
  Ggeom >-> Garith ->> Galois
with its injection, projection, and exactness. The source exact-sequence
clause additionally requires a splitting section
  sectionMap : Galois ->* Garith
with projection (sectionMap x) = x. Clause D/E do not construct this
section. This file packages the actual exact-sequence data and constructs
the source clause only from the exact missing section. No arbitrary
section/axiom/sorry. WRITE-ONLY: no lake.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.InitialThetaSource.ExactSequenceSplittingActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.NativeSourceOrbicurveActual
open LeanFormal.IUT.Theorem311Source

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The actual clause-D profinite exact sequence. -/
abbrev actualSequence :=
  T.clauseD.x_groups.sequence

/-- Actual exactness/injectivity/surjectivity data of the clause-D sequence. -/
structure ActualExactSequenceData where
  injectionInjective : Function.Injective (actualSequence (l := l) T).inclusion
  projectionSurjective : Function.Surjective (actualSequence (l := l) T).projection
  exactAtCover : forall x,
    x ∈ (actualSequence (l := l) T).projection.hom.ker ↔
      x ∈ (actualSequence (l := l) T).inclusion.hom.range

/-- The actual exactness data, constructed from clause D. -/
def actualExactSequenceData : ActualExactSequenceData (l := l) T where
  injectionInjective := (actualSequence (l := l) T).inclusion_injective
  projectionSurjective := (actualSequence (l := l) T).projection_surjective
  exactAtCover := fun x => (actualSequence (l := l) T).exact x

/-- The exact missing splitting section for the actual clause-D sequence. -/
def ExactSequenceSplittingSection : Prop :=
  ∃ sectionMap : ↥(Iut.AbsoluteGaloisProfinite T.arithmetic.K) →*
      ↥T.clauseD.x_groups.groups.arithmetic.group,
    ∀ x : ↥(Iut.AbsoluteGaloisProfinite T.arithmetic.K),
      T.clauseD.x_groups.groups.projection (sectionMap x) = x

/-- Construct the actual source exact-sequence clause from the missing
splitting section. -/
noncomputable def sourceExactSequence_of_section
    (h : ExactSequenceSplittingSection (l := l) T) :
    SourceExactSequenceClause := by
  classical
  choose sectionMap hright using h
  exact sourceExactSequenceOfGroups (actualSequence (l := l) T)
    sectionMap hright

/- Exact missing object: ExactSequenceSplittingSection (l := l) T, i.e. a
/- continuous group section of the actual projection. The actual
/- injection/projection/exactness data are constructed above; no section is. -/

#check actualSequence
#check ActualExactSequenceData
#check actualExactSequenceData
#check ExactSequenceSplittingSection
#check sourceExactSequence_of_section

end LeanFormal.IUT.InitialThetaSource.ExactSequenceSplittingActualAdapted

end
