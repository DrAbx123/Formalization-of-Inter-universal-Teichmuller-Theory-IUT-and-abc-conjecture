import tmp.sheaf.xif.paper.S3131PaperRouteRegionReductionActual

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.S3135PaperRouteRegionConsumeActual

/-- Doc consumption of the tree's (c) reduction: raw/undilated region volume bound =>
region volume family (prior art S3131PaperRouteRegionReductionActual:20/27/43), to be
paired with our concrete IQ-carrier instantiation (S3135RegionRelativeIQActual). -/
def s3135PaperRouteRegionConsumeReport : Audit.Obligation :=
  { id := "IUT-IV.paper-route-region-reduction-consume"
    source :=
      "S3131PaperRouteRegionReductionActual:20 UndilatedRegionBound; :27 " ++
        "regionVolumeFamily_of_raw; :43 regionVolumeFamily_of_undilated; IUT IV " ++
        "section 2 :2329-2340; [GenEll] Definition 1.5"
    status := Audit.VerificationStatus.interface
    note :=
      "CONSUMED PRIOR ART (reuse, no re-proof): UndilatedRegionBound + " ++
        "regionVolumeFamily_of_raw/of_undilated provide the (c) reduction.  The " ++
        "remaining (c) data are exactly: weight <= theta (our RegionRelativeIQ " ++
        "instantiation discharges hull<=theta and finiteness from " ++
        "CardAMPLThetaBoundSupply; weight<=theta remains), plus the hpoint/dictionary " ++
        "row.  Hull half is free (CardAMPL + CertificateHullWiring hull_le_theta " ++
        "equivalence).  No registry edit."
    dependsOn := [ "IUT-III.cor312-to-ABC-conditional-interface" ]
    sorryItems := [ "(c) remaining weight <= theta + hpoint/dictionary row" ] }

#check s3135PaperRouteRegionConsumeReport
end LeanFormal.IUT.XiFPaper.S3135PaperRouteRegionConsumeActual
end
