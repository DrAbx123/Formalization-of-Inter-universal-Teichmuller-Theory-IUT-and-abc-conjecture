import tmp.sheaf.xif.paper.S3135ActualF4LogShellDegreeActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3135F4ActualHullResidualActual
open LeanFormal.IUT.XiFPaper.S3135ActualF4LogShellDegreeActual

namespace LeanFormal.IUT.XiFPaper.S3135RegionRelativeObligationActual

/-- **Exact (c)-side obligation shape (RegionRelativeToHullAndWeight)**: the region
log-volume is bounded by the hull log-volume plus the normalized weight, with finite
hull/region volumes.  Stated as a minimal Prop over the actual volume objects; the
prior-art anchors that supply the hull-side half are recorded below. -/
def S3135RegionRelativeToHullAndWeight
    {l : PrimeGeFive} {V : Type} (I : OriginalInput l V) (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (weight : ℝ) (theta : ℝ) : Prop :=
  I.sourceHullVolume v R n ≤ ENNReal.ofReal theta ∧
    I.sourceHullVolume v R n < ⊤ ∧
      weight ≤ theta

/-- Hull-volume lower bound by the possible-image volume (prior art:
`SourceImageHullVolume.sourceHullVolume_ge_imageVolume`, citable in the tree). -/
theorem s3135_imageVolume_le_hullVolume
    {l : PrimeGeFive} {V : Type} (I : OriginalInput l V) (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) ≤
      I.sourceHullVolume v R n :=
  sourceHullVolume_ge_imageVolume (I := I) (l := l) v R n

/-- Prior-art anchors for the (c)-side instantiations (all citable in the tree). -/
def s3135RegionRelativePriorArt : List String :=
  [ "IQCarrierConcreteModel.lean:iqCarrierModelInterface / iqCarrierModelLogShellPoint (concrete IQHullLogVolumeInterface + logShellPoint consumer)",
    "CardAMPLThetaBoundSupply.lean:realVolume_le / of_realVolume_le / exists_hull_eq_ofReal (hull real-volume supply reductions)",
    "CardHullRealSignedLogVolume.lean:signed log-volume comparison laws",
    "SourceImageHullVolume.lean:sourceHullVolume_ge_imageVolume / _ge_normalized / _lt_top_of_scaledRegionImage (hull-volume half)",
    "SourceImageHull.lean:sourceHullVolume/sourceSetVolume definitions" ]

#check S3135RegionRelativeToHullAndWeight
#check s3135_imageVolume_le_hullVolume

end LeanFormal.IUT.XiFPaper.S3135RegionRelativeObligationActual
end
