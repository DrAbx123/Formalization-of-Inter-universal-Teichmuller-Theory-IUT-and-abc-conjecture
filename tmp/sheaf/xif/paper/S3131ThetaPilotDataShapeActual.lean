import LeanFormal.IUT.Audit.Status

/-! # S3131 Theta-pilot data shape mapping (data only) -/

namespace LeanFormal.IUT.XiFPaper.S3131ThetaPilotDataShapeActual

def S3131ThetaPilotDataShape : List (String × String) :=
  [ ("SourceNativeInitialThetaData T", "IUT I Def 3.1 hypothesis of Thm 1.10"),
    ("lgpModelThetaPacket (FiniteThetaPacket.ofQ gaussianFiveThetaQ)", "Theta-pilot/Theta values (Thm 1.10 p.1255; Cor 3.12)"),
    ("lgpNativeHaarFamily / IsAddHaarMeasure / compact-region finiteness", "additive Haar + log-volume normalization (IV Prop 1.4 p.656; Thm 1.10 Steps (iv)-(vi) p.1586-1680)"),
    ("thetaTensorScaledRegion / thetaTensorHull", "region family in the holomorphic-hull log-volume estimate"),
    ("(c) inequality", "Thm 1.10 final display p.1363-1385 + Cor 2.2(ii) p.2426-2444 (class B)"),
    ("BD-class height comparisons", "Cor 2.2(i) p.2404-2428 / p.2506-2529 (class A)"),
    ("split point bound", "Thm 1.10 (R1)-(R3) p.1523-1545 + weighted averages p.1710-1783 (class B)"),
    ("[GenEll]/[Mzk1]", "Cor 2.3/Thm A reduction p.3117 (class A)") ]

theorem S3131ThetaPilotDataShape_length : S3131ThetaPilotDataShape.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.S3131ThetaPilotDataShapeActual