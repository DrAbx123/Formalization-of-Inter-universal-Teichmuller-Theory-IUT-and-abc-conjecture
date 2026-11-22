import tmp.sheaf.xif.paper.S3137ResidualIndexParentMapActual
import LeanFormal.IUT.Audit.Status

/-!
# S3137: canonical residual index usage contract (task-59)

For mainline's registry, shehdd's gate, and stream owners:
* reference sub-residuals by `INDEX.*` id from `S3137CanonicalResidualIndexPart1/2/3`
  (or `S3137ResidualIndexParentMap`);
* keep `dependsOn` edges as in the parent map (sub-node -> parent registry id);
* do NOT add the `INDEX.*` ids to the 14-entry mainline registry (they are
  sub-nodes, not registry rows);
* if a stream renames a residual declaration, message lattice and only the
  index entry note is updated (ids are stable).

Classification: every `INDEX.*` entry in parts 1-3 is a strictly narrower
structural/normalization/input component (NONE is ABC-strength); the only
ABC-strength residual in the mainline registry remains `F4.c.cardP-ABC-strength`.
Data only; no proof content. -/

namespace LeanFormal.IUT.Audit

/-- Usage contract for the canonical residual index (data record). -/
def S3137ResidualIndexUsageContract : Obligation :=
  { id := "S3137.index.usage-contract"
    source := "S3137CanonicalResidualIndexActual / Part2 / Part3; S3131FinalResidualRegistryActual"
    status := VerificationStatus.interface
    note := "Reference sub-residuals by INDEX.* ids; dependsOn goes sub-node -> parent registry id; INDEX.* ids are NOT extra registry rows; renaming a declaration changes only the index note, not the id.  None of the 29 entries is ABC-strength."
    dependsOn := ["S3137CanonicalResidualIndexActual", "S3137CanonicalResidualIndexPart2Actual", "S3137CanonicalResidualIndexPart3Actual", "S3131FinalResidualRegistryActual"] }

end LeanFormal.IUT.Audit
