import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullInterfaceDischarge

/-! # S3131 instantiation attempt: SourceImageHullVolume vs (b) UndilatedHeightBound -/

namespace LeanFormal.IUT.XiFPaper.S3131SourceImageHullVolumeAttemptActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

def S3131HeightDictionaryRemaining : List String :=
  [ "sourceLocalLogDegree/sourcePointVolume provide the log-volume dictionary on the source image hull (REUSE for the volume side)",
    "UNDILATED height bound (b) additionally needs the height/log-volume dictionary link (RationalPointDictionary logHeight1 = log c) and a uniform comparison; under pointwise degree faithfulness sourceHullVolume is top (sourceHullVolume_eq_top_of_degreeFaithful), so the theta-upper-bound slot is unsatisfiable at this realization layer",
    "remaining hypothesis: hull volume finite + region volume finite + uniform height-vs-volume comparison (Cor 3.12 Step (xi) content, class B)" ]

theorem S3131HeightDictionaryRemaining_length : S3131HeightDictionaryRemaining.length = 3 := rfl

#check sourceLocalLogDegree
#check sourcePointVolume
#check sourceLocalLogDegree_one

end LeanFormal.IUT.XiFPaper.S3131SourceImageHullVolumeAttemptActual