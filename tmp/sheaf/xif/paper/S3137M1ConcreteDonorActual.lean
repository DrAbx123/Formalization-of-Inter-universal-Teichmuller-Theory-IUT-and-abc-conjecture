import LeanFormal.IUT.Audit.Status
import tmp.sheaf.xif.paper.S3133M1ContractObstructionActual

/-!
# S3137: M1 concrete donor assistance — bad index set + exact obstruction

Assist for qpilot/mainline M1: the concrete finite type of actual native bad
places and the constructible-equivalence recipe are provided here; the M1
wiring lemmas are qpilot's already-green declarations (cited, not re-proved):

* `badIndexSet T := Bad (nativePlaceSelection T)` — concrete finite type;
* `badIndexSet_equiv_of_card_eq`: an explicit equivalence from a cardinality
  equality via `Fintype.equivOfCardEq` (constructible; no extra choice);
* qpilot green wiring (cited): `S3133BadToAllPlaceIndexInjection_of_indexEquivalence`
  (S3133M1InjectionReductionActual), `S3131BadTensorPrimeMatch_of_basePlace`
  (S3133S3131PlaceIndexComparisonActual), `S3131BadTensorIndexEquivalence`;
* EXACT REMAINING OBSTRUCTION: the bad<->C3.tensorIndex equivalence and the
  base-place equality (placeToMod provenance; frozen OriginalInput contract does
  not expose it; qpilot S3133M1ContractSeparatedMissing / S3133M1Remaining).
Data + generic constructs; no sorry/axiom.  WRITE-ONLY.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3137M1ConcreteDonorActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.Audit

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- **Concrete finite type of actual native bad places** (M1 index-set half). -/
abbrev badIndexSet : Type := Bad (nativePlaceSelection T)

/-- **Constructible equivalence from a cardinality equality**
(`Fintype.equivOfCardEq`; no arbitrary extra choice). -/
theorem badIndexSet_equiv_of_card_eq {ι : Type*} [Fintype (badIndexSet T)]
    [Fintype ι] (h : Fintype.card (badIndexSet T) = Fintype.card ι) :
    Nonempty (badIndexSet T ≃ ι) :=
  ⟨Fintype.equivOfCardEq h⟩

/-- **Constructible equivalence to any finite type of equal cardinality.** -/
noncomputable def badIndexEquivOfCardEq {ι : Type*} [Fintype (badIndexSet T)]
    [Fintype ι] (h : Fintype.card (badIndexSet T) = Fintype.card ι) :
    badIndexSet T ≃ ι :=
  Fintype.equivOfCardEq h

end LeanFormal.IUT.XiFPaper.S3137M1ConcreteDonorActual

namespace LeanFormal.IUT.Audit

/-- **Tool: concrete bad index set** (finite type of actual bad places). -/
def S3137BadIndexSetTool : Obligation :=
  { id := "TOOL.bad-index-set"
    source := "VbadPlaceIndexingActual / nativePlaceSelection; IUT I Definition 3.1(b),(e)"
    status := VerificationStatus.interface
    note := "CONSTRUCTIBLE TOOL: badIndexSet (T) := Bad (nativePlaceSelection T) (concrete finite type of actual native bad places; Fintype supplied per T); badIndexEquivOfCardEq / badIndexSet_equiv_of_card_eq give an explicit equivalence from a cardinality equality (Fintype.equivOfCardEq). File S3137M1ConcreteDonorActual EXIT0 + probe. Not a residual."
    dependsOn := ["S3137M1ConcreteDonorActual"] }

/-- **INDEX node: M1 concrete donor (constructible part + exact obstruction)**. -/
def S3137M1ConcreteDonorRecord : Obligation :=
  { id := "INDEX.R1.M1.concrete-donor"
    source := "IUT I Definition 3.1(b),(e); IUT III Proposition 3.4(ii); qpilot S3133M1ContractSeparatedMissing/S3133M1Remaining; S3133BadToAllPlaceIndexInjectionActual; S3133S3131PlaceIndexComparisonActual"
    status := VerificationStatus.pending
    note := "OWNER lattice+qpilot. CONSTRUCTIBLE: concrete bad index set + equivalence-from-cardinality recipe (S3137M1ConcreteDonorActual); qpilot green wiring cited: S3133BadToAllPlaceIndexInjection_of_indexEquivalence (bad->all-place injection data from equivalence), S3131BadTensorPrimeMatch_of_basePlace (prime match from base-place equality), S3131BadTensorIndexEquivalence Prop. EXACT REMAINING OBSTRUCTION: bad<->C3.tensorIndex equivalence + base-place equality (placeToMod provenance absent from frozen OriginalInput contract; contract-separated, qpilot S3133M1ContractSeparatedMissing). NOT ABC-strength. PARENT: R1.M1.bad-tensor-index."
    dependsOn := ["R1.M1.bad-tensor-index", "S3137M1ConcreteDonorActual", "S3133M1InjectionReductionActual", "S3133S3131PlaceIndexComparisonActual"] }

end LeanFormal.IUT.Audit