import tmp.sheaf.xif.paper.S3137M1ConcreteDonorActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.Audit.Status

/-!
# S3137: from-scratch model supply (task-72 readiness)

Index arithmetic data, bad-index donor, and INDEX/TOOL ids for the from-scratch
model.  Registry frozen; INDEX/TOOL are data-only records.

* `fromScratchIndexEquiv` / `fromScratchIndexEquiv_refl`:
  `SourceTheorem311Index := Int × Int` and its identity equivalence;
  horizontal/vertical index shifts + equivalences are the production
  `SourceOriginalInput` definitions (proved, citable);
* `badSelfTensorIndexDonor`: concrete donor with
  `tensorIndex := Bad (nativePlaceSelection T)` and `equiv := Equiv.refl`
  (the bad<->C3 tensor index half is CONSTRUCTIBLE);
* `TensorIndexPlaceCompatibility`: the explicit placeToMod field shape
  (per-bad-place rational prime = C3.p); the genuine source missing;
* `TOOL.realified-generator-degree`: citable existing tools
  (`globalRealifiedPrimePowerHom_degree_faithful`, `lgpRealifiedDegree`, stage4).
Data + generic constructs; no sorry/axiom.  WRITE-ONLY.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3137FromScratchModelSupplyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.Audit

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- **Index arithmetic (1)**: the source index is `Int × Int`, with the
identity equivalence (horizontal/vertical shifts are the production
`SourceOriginalInput` definitions). -/
def fromScratchIndexEquiv : SourceTheorem311Index ≃ Int × Int :=
  Equiv.refl _

@[simp] theorem fromScratchIndexEquiv_apply (p : SourceTheorem311Index) :
    fromScratchIndexEquiv p = p :=
  rfl

/-- **Bad tensor-index donor (2)**: concrete donor whose tensorIndex is the
actual bad index set, with the identity equivalence. -/
structure BadSelfTensorIndexDonor [Fintype (Bad (nativePlaceSelection T))] where
  tensorIndex : Type
  fintype : Fintype tensorIndex
  equiv : Bad (nativePlaceSelection T) ≃ tensorIndex

/-- The concrete donor with `tensorIndex := Bad (nativePlaceSelection T)` and
`equiv := Equiv.refl` (constructible; Fintype supplied per T). -/
def badSelfTensorIndexDonor [Fintype (Bad (nativePlaceSelection T))] :
    BadSelfTensorIndexDonor (l := l) T where
  tensorIndex := Bad (nativePlaceSelection T)
  fintype := inferInstance
  equiv := Equiv.refl _

/-- **Explicit placeToMod field shape (residual datum, not asserted).**  The
per-bad-place rational prime equals the C3 residue prime; this is the
place-compatibility that the frozen OriginalInput contract does not expose. -/
def TensorIndexPlaceCompatibility : Prop :=
  ∀ b : Bad (nativePlaceSelection T), (completionRationalPrime b.1).val = C3.p

end LeanFormal.IUT.XiFPaper.S3137FromScratchModelSupplyActual

namespace LeanFormal.IUT.Audit

/-- **INDEX: from-scratch index arithmetic** (constructible part). -/
def S3137FromScratchIndexArithmetic : Obligation :=
  { id := "INDEX.MODEL.from-scratch-index-arithmetic"
    source := "IUT I Definition 3.1; LeanFormal/IUT/IUTIII/Theorem311/SourceOriginalInput.lean:39 (SourceTheorem311Index := Int × Int); horizontal/vertical shifts :277-332"
    status := VerificationStatus.interface
    note := "CONSTRUCTIBLE: SourceTheorem311Index is definitionally Int × Int (abbrev, production line 39); fromScratchIndexEquiv = Equiv.refl; horizontalIndex/verticalIndex/horizontalIndexEquiv/verticalIndexEquiv are production-proved.  File S3137FromScratchModelSupplyActual EXIT0 + probe. Not a residual."
    dependsOn := ["S3137FromScratchModelSupplyActual"] }

/-- **INDEX: from-scratch bad tensor-index donor** (constructible index half + placeToMod residual). -/
def S3137FromScratchBadTensorDonor : Obligation :=
  { id := "INDEX.MODEL.from-scratch-bad-index-donor"
    source := "IUT I Definition 3.1(b),(e); IUT III Proposition 3.4(ii); VbadPlaceIndexingActual"
    status := VerificationStatus.interface
    note := "CONSTRUCTIBLE: BadSelfTensorIndexDonor with tensorIndex := Bad (nativePlaceSelection T) and equiv := Equiv.refl (badSelfTensorIndexDonor).  RESIDUAL: TensorIndexPlaceCompatibility (explicit placeToMod field shape: per-bad-place rational prime = C3.p; placeToMod provenance contract-separated).  Consumers: from-scratch model (task-72), qpilot M1.  Not ABC-strength."
    dependsOn := ["S3137FromScratchModelSupplyActual", "S3137M1ConcreteDonorActual"] }

/-- **TOOL: realified generator degree** (existing citable tools; no manufacture needed). -/
def S3137RealifiedGeneratorDegreeTool : Obligation :=
  { id := "TOOL.realified-generator-degree"
    source := "stage4: S3136LGPRealifiedValueTransportActual (lgpRealifiedLogValue, lgpRealifiedLogValue_of_single, lgpRealifiedValueTransport_compat); qpilot S3133ValueGroupDegreeActual (globalRealifiedPrimePowerHom_degree_faithful)"
    status := VerificationStatus.interface
    note := "EXISTING TOOL: lgpRealifiedLogValue (realified log-value = ofAdd of lgpRealifiedDegree) with lgpRealifiedLogValue_of_single / lgpRealifiedValueTransport_compat (stage4, EXIT0 + trio), and globalRealifiedPrimePowerHom_degree_faithful (qpilot S3133ValueGroupDegreeActual, EXIT0 + trio).  Use for realified generator degree in the from-scratch model; no manufacture needed."
    dependsOn := ["S3136LGPRealifiedValueTransportActual", "S3133ValueGroupDegreeActual"] }

end LeanFormal.IUT.Audit
