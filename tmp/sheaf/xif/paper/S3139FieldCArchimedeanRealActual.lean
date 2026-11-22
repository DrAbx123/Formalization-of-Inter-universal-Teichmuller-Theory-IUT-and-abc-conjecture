import tmp.sheaf.xif.paper.S3139FieldCArchimedeanLogActual
import tmp.sheaf.xif.paper.S3139FieldCConjugateActual
import tmp.sheaf.xif.paper.S3139FieldCCopyActionActual
import tmp.sheaf.xif.paper.S3139FieldCArchimedeanBundleActual
import tmp.sheaf.xif.paper.S3139FieldCArchimedeanConsumerActual
import tmp.sheaf.xif.paper.S3139FieldCConjugateConsumerActual
import tmp.sheaf.xif.paper.S3139FieldCResidualSummaryActual

/-!
# S3139: field (C) umbrella — paper-faithful realified copy channel

Aggregate import of the field-(C) components (IUT III:616-620, Fig. I.5):

* @S3139FieldCArchimedeanLogActual@: actual archimedean additive log and Real
  scalar character of @F_mod^x@, plus the choice datum.
* @S3139FieldCArchimedeanBundleActual@: choice + actual character bundle.
* @S3139FieldCCopyActionActual@: paper-faithful @SourceInd2CopyActionData@
  built from the actual archimedean character (tensor-level action laws for
  @ind2TensorEquiv@ proved), i.e. the realified copy action preserving the
  splitting-monoid scalar action.
* @S3139FieldCConjugateActual@: exact missing finite-place conjugate datum
  @SourceConjugateLocalUnitMap@ + actual local Frobenius action/readouts +
  minimal (Ind1) bridge dependency @SourceInd1BridgeDependency@.
* @S3139FieldCArchimedeanConsumerActual@, @S3139FieldCConjugateConsumerActual@,
  @S3139FieldCResidualSummaryActual@: consumer interfaces and residual summary.

**Component, not paper object.**  Named consumers: first-triangle mutation
(@SourceMultiradialRepresentation@), lattice/mainline q/Theta comparison.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139FieldCArchimedeanRealActual

end LeanFormal.IUT.XiFPaper.S3139FieldCArchimedeanRealActual
