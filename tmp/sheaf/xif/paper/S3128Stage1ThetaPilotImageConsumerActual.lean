import tmp.sheaf.xif.paper.ThetaPilotObjectActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.ThetaPilotObjectActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1ThetaPilotImageConsumerActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

theorem S3128Stage1ThetaPilotImage_subset_hull
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    (thetaPilotImageHullAt (I := I) v R n).imageSet ⊆
      (thetaPilotImageHullAt (I := I) v R n).hull :=
  thetaPilotImage_subset_hull (I := I) v R n

theorem S3128Stage1QPilotPoint_mem_thetaPilotHull
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceQPilotPoint v R n ∈
      (thetaPilotImageHullAt (I := I) v R n).hull :=
  qPilotPoint_mem_thetaPilotHull (I := I) v R n

noncomputable def S3128Stage1ThetaPilotImageHullAt
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    ThetaPilotImageHullAt (I := I) v R n :=
  thetaPilotImageHullAt (I := I) v R n

#check S3128Stage1ThetaPilotImage_subset_hull
#check S3128Stage1QPilotPoint_mem_thetaPilotHull
#check S3128Stage1ThetaPilotImageHullAt
end LeanFormal.IUT.XiFPaper.S3128Stage1ThetaPilotImageConsumerActual