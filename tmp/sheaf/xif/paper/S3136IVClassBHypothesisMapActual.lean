import tmp.sheaf.xif.paper.S3136RegionEstimateSourceClassificationActual
import tmp.sheaf.xif.paper.S3136ModelThetaPacketActual
import tmp.sheaf.xif.paper.S3136NativeHaarFamilyActual
import tmp.sheaf.xif.paper.S3136ModelThetaTensorVolumeFiniteActual

/-! # Stage-4 host: (c) construction-to-IV-hypothesis map (class-B alignment)

TEXT: papers/motizuki_corpus/text/Inter-universal Teichmuller Theory IV.txt;
papers/motizuki_corpus/text/Arithmetic Elliptic Curves in General Position.txt.

CONSUMER: mainline's IUT IV statement skeleton. This file maps the (c) split
(split point bound + unit-region bound, Cor312 Gap 2 form) to the EXACT
statements of IUT IV Thm A / Thm 1.10 / Prop 1.4 / Cor 3.12-shape pieces, and
shows which constructible pieces of this stream instantiate which hypothesis:
* SourceNativeInitialThetaData T (from the model clause-data route)
  <-> IUT I, Definition 3.1 initial Theta-data hypothesis of Thm 1.10;
* lgpModelThetaPacket (FiniteThetaPacket.ofQ gaussianFiveThetaQ)
  <-> Theta-pilot data (Thm 1.10 / Cor 3.12 Theta values);
* lgpNativeHaarFamily + IsAddHaarMeasure + compact-region finiteness
  <-> additive Haar / log-volume normalization used in Prop 1.4 and the
  holomorphic-hull log-volume estimate of Thm 1.10 (Steps (iv)-(vi));
* thetaTensorScaledRegion / thetaTensorHull (ThetaTensorScaledImageActual)
  <-> region family whose log-volume is bounded in the (c) unit-region bound;
* the (c) inequality itself (regionVolume <= normalizedWeight) <-> Thm 1.10
  final display p.1363-1385 and Cor 2.2 (ii) p.2426-2444: CLASS B target.

LABEL: hypothesis map (data rows) + class A/B flags. Registry frozen; new file only. -/

namespace LeanFormal.IUT.XiFPaper.S3136IVClassBHypothesisMapActual

structure LGPIVHypothesisRow where
  ourPiece : String
  constructibleStatus : String
  instantiates : String
  corpusCitation : String
  sourceClass : String

def lgpIVClassBHypothesisMap : List LGPIVHypothesisRow :=
  [ ⟨"native initial Theta datum T", "conditional (LGPModelSourceClauseMissing / LGPConcreteClauseData)", "Thm 1.10 initial Theta-data hypothesis; Cor 3.12 situation", "IUT IV Thm 1.10 p.1255; IUT I Def 3.1", "classB-interface"⟩,
    ⟨"model Theta packet FiniteThetaPacket.ofQ gaussianFiveThetaQ", "concrete (checker CITABLE)", "Theta values used by the Theta-pilot object and Cor 3.12 signed comparison", "IUT IV Thm 1.10 p.1255; IUT III Cor 3.12", "classA-concrete"⟩,
    ⟨"native additive Haar family lgpNativeHaarFamily", "concrete (checker CITABLE)", "log-volume normalization and compact-region finite volume in Prop 1.4 / Thm 1.10 Steps (iv)-(vi)", "IUT IV Prop 1.4 p.656; Thm 1.10 Steps p.1586-1680", "classA-concrete"⟩,
    ⟨"theta tensor scaled regions/hulls (thetaTensorScaledRegion, thetaTensorHull)", "concrete region definitions; compactness providers exist", "region family whose log-volume is bounded by the unit-region bound", "IUT IV Thm 1.10 holomorphic-hull estimate p.1586-1680; IUT III Prop 3.2", "classB-input-region"⟩,
    ⟨"regionVolume <= normalizedWeight (c) inequality", "MISSING (class B formalization target)", "Thm 1.10 final display / Cor 2.2 (ii) main estimate; split point + unit-region bounds", "IUT IV Thm 1.10 p.1363-1385; Cor 2.2 p.2426-2444; (C1),(C2) p.2475-2493", "classB"⟩,
    ⟨"BD-class height comparisons (1/6 log q ~ ht_inf ~ ht_omega)", "formalizable now (class A: IsBDLe chain tool)", "Cor 2.2 (i) equalities and Cor 2.3 reduction step", "IUT IV Cor 2.2 (i) p.2404-2428; proof p.2506-2529", "classA"⟩,
    ⟨"split point bound", "MISSING (class B)", "Thm 1.10 Steps (iii)-(v): (R1)-(R3) prime-splitting/rounding estimates + weighted averages", "IUT IV (R1)-(R3) p.1523-1545; weighted averages p.1710-1783", "classB"⟩,
    ⟨"[GenEll] Thm 2.1 reduction + [Mzk1] noncritical Belyi input", "paper theorems (class A reduction)", "Cor 2.3/Thm A reduction to the compactly bounded case", "GenEll Thm 2.1 p.615; [Mzk1] Thm 2.5 p.207; IUT IV Cor 2.3 p.3117", "classA"⟩ ]

theorem lgpIVClassBHypothesisMap_length : lgpIVClassBHypothesisMap.length = 8 := rfl

#check lgpIVClassBHypothesisMap
#check lgpIVClassBHypothesisMap_length

end LeanFormal.IUT.XiFPaper.S3136IVClassBHypothesisMapActual