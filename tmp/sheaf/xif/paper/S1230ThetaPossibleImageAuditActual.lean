import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2ActualTuplePacket
import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2HullPresentationFamilyCutActual
import LeanFormal.IUT.IUTIII.Theorem311.HullDirectednessCovolumeSignProbe
import LeanFormal.IUT.IUTIII.Theorem311.SourceHodgeTheaterBridge

/-! # S1230: possibleImage for I.family.index — audit

Read-only type report.  No weak interface and no constant possibleImage is
invented.

* `SourcePacketRealization.possibleImage : Choice → Set Real` is the required
  source-indexed family, together with nonemptiness and Ind1/2/3 image laws.
* `actualTuplePossibleImage (p := p) places tuple μ n` is an actual set of
  real hull log-volumes, but it lives on an independently supplied finite
  tensor tuple/places/measure/scale; it is not indexed by `I.family.index`.
* `actualTuplePacket` builds an actual `SourcePacketRealization` only for
  `actualTupleProcession`, whose Choice is `Nat`, not `I.family.index`.
* `possibleImageUnion Q` and `FiniteRayUnionPresentation Q L` are generic
  constructions over a `SourcePacketRealization Q`; without Q on
  `I.family.index` they give no actual source possible-image set.

The first exact gap is a source packet realization on Choice = I.family.index
(with its actual tuple/place/scale map), not another generic set construction.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S1230ThetaPossibleImageAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.NumberFieldFinitePlace

#check SourcePacketRealization
#check SourcePacketRealization.possibleImage
#check SourcePacketRealization.possibleImage_nonempty
#check actualTuplePossibleImage
#check actualTuplePossibleImage_nonempty
#check actualTuplePossibleImage_subset_logVolumeSet
#check actualTuplePacket
#check actualTupleProcession
#check possibleImageUnion
#check possibleImage_subset_union
#check FiniteRayUnionPresentation
#check finiteRayUnionPresentation_iff_exists_rayPresentation

end LeanFormal.IUT.XiFPaper.S1230ThetaPossibleImageAuditActual
end
