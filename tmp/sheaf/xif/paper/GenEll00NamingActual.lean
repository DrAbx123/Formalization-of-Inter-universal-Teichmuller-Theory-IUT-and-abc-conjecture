import LeanFormal.IUT.Audit.Status

/-! # GenEll00: naming/coordination map (P0 files + existing assets) - data only -/

namespace LeanFormal.IUT.XiFPaper.GenEll00NamingActual

def GenEllNamingMap : List (String × String) :=
  [ ("LeanFormal.IUT.XiFPaper.GenEll01BasicActual", "P0 §1 basic definitions (PaperHeight/PaperLogDiff/PaperLogCond/BDClassOn/CompactlyBoundedSubset) - mainline"),
    ("LeanFormal.IUT.XiFPaper.GenEll02Prop14Actual", "P0 Prop 1.4 statement+elementary (abc)"),
    ("LeanFormal.IUT.XiFPaper.GenEll03Prop16Actual", "P0 Prop 1.6 statement (abc)"),
    ("LeanFormal.IUT.XiFPaper.GenEll04Prop17Actual", "P0 Prop 1.7 statement (abc)"),
    ("LeanFormal.IUT.XiFPaper.GenEll05Theorem21Actual", "P0 Theorem 2.1 statement + (i)=> (ii) proved + (ii)=> (i) reduction skeleton (mainline)"),
    ("LeanFormal.IUT.XiFPaper.GenEll06Section3StatementsActual", "P0 §3 statements (stage4)"),
    ("LeanFormal.IUT.XiFPaper.GenEll07Section4StatementsActual", "P0 §4 statements (stage4)"),
    ("LeanFormal.IUT.XiFPaper.GenEll08MainReductionActual", "P0 main reduction assembly + IUT IV §2 consumer interface (mainline)"),
    ("reused assets", "S3131BDClassCompositionActual (IsBDLe); S3136BDClassChainToolActual; S3131GenEllPaperInputActual; S3131GenEllInputDetailedActual; S3131GenEllEquivalenceShapeActual; S3131GenEllShapeStatementsActual; S3131IUTIVTheoremAInputActual; ArithmeticDivisorDegree:1214+; RationalPointDictionary; S3132IVGenEllShadowAdapterActual.genEll_transfer") ]

theorem GenEllNamingMap_length : GenEllNamingMap.length = 9 := rfl

end LeanFormal.IUT.XiFPaper.GenEll00NamingActual