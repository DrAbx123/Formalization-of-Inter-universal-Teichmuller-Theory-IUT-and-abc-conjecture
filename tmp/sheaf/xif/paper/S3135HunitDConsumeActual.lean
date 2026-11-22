import tmp.sheaf.xif.paper.S2722HunitDActual

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.S3135HunitDConsumeActual

/-- Doc consumption of the tree's hunit D0=0 supply (`S2722HunitDActual`): the
Cor 3.12 gap-2 hunit row is available with D0 = 0; this is the F5 card-U-side prior art
to consume for the concrete carrier (card P remains ABC-strength, unchanged). -/
def s3135HunitDConsumeReport : Audit.Obligation :=
  { id := "IUT-IV.hunitD-consume"
    source :=
      "S2722HunitDActual (S2722D0_nonneg/S2722_hunitD/S2722_gap2_with_D0); " ++
        "IUT III Corollary 3.12 :10324-10353; IUT III Remark 3.9.5(i)"
    status := Audit.VerificationStatus.interface
    note :=
      "CONSUMED PRIOR ART: S2722_hunitD / S2722_gap2_with_D0 give the hunit row with " ++
        "D0 = 0 on the concrete carrier; our S3135F5ActualReductionActual consumes the " ++
        "same row through cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_" ++
        "hullVolume.  Card U is already PROVED unconditionally in our chain; card P " ++
        "remains exactly ABC-strength (tightness).  No new paper input claimed; no " ++
        "registry edit."
    dependsOn := [ "IUT-III.cor312-to-ABC-conditional-interface" ]
    sorryItems := [ "card P = ABCHeightWeightAdditiveBoundV2 (unchanged, ABC-strength)" ] }

#check s3135HunitDConsumeReport
end LeanFormal.IUT.XiFPaper.S3135HunitDConsumeActual
end
