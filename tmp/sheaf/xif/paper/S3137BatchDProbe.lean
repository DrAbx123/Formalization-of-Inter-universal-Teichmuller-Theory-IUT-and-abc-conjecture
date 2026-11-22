import tmp.sheaf.xif.paper.S3137PaperRouteComparisonDataActual
import tmp.sheaf.xif.paper.S3137GenEllCorpusAssetActual
import tmp.sheaf.xif.paper.S3137HullThetaSideIdsNoteActual

/-! Axiom probe: paper-route comparison data + GenEll corpus asset + hull ThetaSide ids. -/
open LeanFormal.IUT.XiFPaper.S3137PaperRouteComparisonDataActual
open LeanFormal.IUT.XiFPaper.S3137GenEllCorpusAssetActual
open LeanFormal.IUT.Audit

#print axioms S3137GenEllCorpusAsset
#print axioms S3137NoncriticalBelyiCorpusAsset
#print axioms INDEX_PAPER_GENELL
#print axioms INDEX_PAPER_NONCRITICAL_BELYI
#print axioms S3137HullThetaSideIds
#print axioms S3137HullThetaSideBatchRecord
#check S3137Corollary312ComparisonData.corollary312
