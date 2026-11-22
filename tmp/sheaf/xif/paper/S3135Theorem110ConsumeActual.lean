import tmp.sheaf.xif.paper.S3131IUTIVTheorem110InputActual

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.S3135Theorem110ConsumeActual

/-- Doc consumption of the tree's IUT IV Theorem 1.10 input shape: the theorem-level
statement is parameterized by the theta-log-volume and q-log-volume functions, and the
height dictionary class by height/log-diff/log-cond; these are exactly the function
slots our (b) comparison needs. -/
def s3135Theorem110ConsumeReport : Audit.Obligation :=
  { id := "IUT-IV.theorem110-input-consume"
    source :=
      "S3131IUTIVTheorem110InputActual (Theorem110Statement/HeightDictionaryIsBDClass); " ++
        "IUT IV Theorem 1.10 :1255-1385; IUT IV section 2 :2329-2340; [GenEll] Def 1.5"
    status := Audit.VerificationStatus.interface
    note :=
      "CONSUMED PRIOR ART: the tree already carries the IUT IV Theorem 1.10 statement " ++
        "shape (Theorem110Statement over theta/q log-volume functions) and the height " ++
        "dictionary class shape (HeightDictionaryIsBDClass over height/logDiff/logCond). " ++
        "These are the exact function slots of the (b) uniform height-vs-volume " ++
        "comparison; INSTANTIATION still requires the four dictionary pieces and the " ++
        "(b)-shape families, which remain the named remaining hypotheses (see " ++
        "S3135HeightWeightAtPaperActual / S3135DictionaryConsumeActual).  No discharge " ++
        "claim; no registry edit."
    dependsOn := [ "IUT-III.cor312-to-ABC-conditional-interface" ]
    sorryItems := [ "(b) Theorem 1.10 statement instantiation at the actual dictionary" ] }

#check s3135Theorem110ConsumeReport
end LeanFormal.IUT.XiFPaper.S3135Theorem110ConsumeActual
end
