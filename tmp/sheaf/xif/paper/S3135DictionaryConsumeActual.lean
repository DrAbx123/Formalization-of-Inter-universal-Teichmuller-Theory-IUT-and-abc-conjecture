import tmp.sheaf.xif.paper.S3131HeightVolumeDictionaryAttemptActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3131HeightVolumeDictionaryAttemptActual

namespace LeanFormal.IUT.XiFPaper.S3135DictionaryConsumeActual

/-- The tree's exact (b)-dictionary piece list, re-exported with its length fact. -/
theorem s3135_heightVolumePieces_length :
    S3131HeightVolumePieces.length = 4 :=
  S3131HeightVolumePieces_length

/-- Doc map: each of the 4 pieces is one of the two (b)-shape hypothesis families of
`heightWeightBound_of_normalizedVolumeComparison` (height<=volume, volume<=weight+
theta+D, uniformity in delta, and the weight nonnegativity), and the height/weight
function layer is `ArithmeticDivisorDegree` heightWeight/hTerm/toricHeightWeight. -/
def s3135DictionaryConsumeReport : Audit.Obligation :=
  { id := "IUT-IV.height-volume-dictionary-consume"
    source :=
      "S3131HeightVolumeDictionaryAttemptActual (exact remaining (b) hypothesis); " ++
        "ThetaBoundToHeightWeight.lean:67; ArithmeticDivisorDegree.lean:1214/1221/" ++
        "1225/1310/1613; IUT IV Theorem 1.10 :1255-1385"
    status := Audit.VerificationStatus.interface
    note :=
      "CONSUMED PRIOR ART: S3131HeightVolumePieces (4 pieces) supplies the exact " ++
        "remaining (b) dictionary list; our S3135HeightWeightAtPaperActual." ++
        "s3135_heightWeightBound_atPaperFunctions reduces the (b) comparison to the " ++
        "same two families specialized to Height.logHeight1(abcRationalPoint) / " ++
        "arithmeticWeight / IsABCTriple.  No discharge claim: the four pieces remain " ++
        "hypotheses of the uniform comparison (IUT IV Thm 1.10 shape); vendor " ++
        "Iut/Stage1/IUTStage1IUTIVAlgebra.lean:8056 height_le_weighted_logDiff_logCond_" ++
        "minus_lowerBound is SOURCE REFERENCE ONLY (not importable), shape noted for " ++
        "the dictionary.  Registry untouched."
    dependsOn := [ "IUT-III.cor312-to-ABC-conditional-interface" ]
    sorryItems := [ "(b) four height/volume dictionary pieces (S3131HeightVolumePieces)" ] }

#check s3135_heightVolumePieces_length
#check s3135DictionaryConsumeReport
end LeanFormal.IUT.XiFPaper.S3135DictionaryConsumeActual
end