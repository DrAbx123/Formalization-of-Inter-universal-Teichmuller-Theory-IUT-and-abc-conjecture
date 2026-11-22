import tmp.sheaf.xif.paper.S3131PaperRouteHeightReductionActual

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.S3135PaperRouteHeightConsumeActual

/-- Doc consumption of the tree's (b) reduction: undilated height bound =>
height comparison family (prior art S3131PaperRouteHeightReductionActual:21/27). -/
def s3135PaperRouteHeightConsumeReport : Audit.Obligation :=
  { id := "IUT-IV.paper-route-height-reduction-consume"
    source :=
      "S3131PaperRouteHeightReductionActual:21 UndilatedHeightBound; :27 " ++
        "heightComparisonFamily_of_undilated; IUT IV Theorem 1.10 :1255-1385; " ++
        "[GenEll] Theorem 2.1 (corpus Arithmetic Elliptic Curves in General " ++
        "Position.txt:615-687, class B reduction equivalence)"
    status := Audit.VerificationStatus.interface
    note :=
      "CONSUMED PRIOR ART (reuse, no re-proof): the tree already reduces the " ++
        "undilated height bound to the height comparison family " ++
        "(heightComparisonFamily_of_undilated).  Our (b) work therefore only needs " ++
        "the two undilated hypothesis families (height<=volume on the actual " ++
        "delta-indexed volume; volume<=weight+thetaBound+D), specialized at the paper " ++
        "height/weight functions by S3135HeightWeightAtPaperActual." ++
        "s3135_heightWeightBound_atPaperFunctions.  No discharge claim; GenEll Thm 2.1 " ++
        "is a proved reduction equivalence (class B), not the ABC proof.  No registry " ++
        "edit."
    dependsOn := [ "IUT-III.cor312-to-ABC-conditional-interface" ]
    sorryItems := [ "(b) undilated height/volume families (S3131HeightVolumePieces)" ] }

#check s3135PaperRouteHeightConsumeReport
end LeanFormal.IUT.XiFPaper.S3135PaperRouteHeightConsumeActual
end
