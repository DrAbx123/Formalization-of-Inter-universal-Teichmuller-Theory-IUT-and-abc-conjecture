import tmp.sheaf.xif.paper.S3132IVGenEllShadowAdapterActual

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.S3135GenEllConsumeActual

/-- Doc consumption of the tree's GenEll shadow adapter: AdaptedIVGenEllShadow carries
the exact GenEll form as the field genEll_transfer (prior art
S3132IVGenEllShadowAdapterActual:23/43), whose compactSubsetTheoremA field is the
[GenEll] Theorem 2.1 compact-subset input (corpus lines 615-687, proved reduction
equivalence, class B). -/
def s3135GenEllConsumeReport : Audit.Obligation :=
  { id := "IUT-IV.genell-shadow-consume"
    source :=
      "S3132IVGenEllShadowAdapterActual:23 AdaptedIVGenEllShadow; :39 " ++
        "compactSubsetTheoremA; :43 genEll_transfer; [GenEll] Theorem 2.1 " ++
        "papers/motizuki_corpus/text/Arithmetic Elliptic Curves in General " ++
        "Position.txt:615-687 (class B proved reduction); IUT IV section 2 :2329-2340"
    status := Audit.VerificationStatus.interface
    note :=
      "CONSUMED PRIOR ART: the exact GenEll statement form is already declared as the " ++
        "explicit field genEll_transfer of AdaptedIVGenEllShadow (with " ++
        "compactSubsetTheoremA input), so no GenEll statement formalization is needed " ++
        "anew - the remaining work is instantiating the adapted shadow's fields from " ++
        "the (b)/(c) data (dictionary pieces, uniform height comparison, region " ++
        "relative to hull and weight).  GenEll Thm 2.1 is a REDUCTION equivalence " ++
        "(class B), not an ABC proof.  No discharge claim; no registry edit."
    dependsOn := [ "IUT-III.cor312-to-ABC-conditional-interface" ]
    sorryItems := [ "[GenEll] shadow instantiation from (b)/(c) data" ] }

#check s3135GenEllConsumeReport
end LeanFormal.IUT.XiFPaper.S3135GenEllConsumeActual
end
