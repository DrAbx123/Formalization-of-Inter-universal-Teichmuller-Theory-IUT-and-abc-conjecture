/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import Mathlib.Tactic

/-! # A2 node03: groups/extension fields interface -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1A2Node03GroupsExtensionActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}

/-- A2 node03 group and K-extension fields exactly as consumed by
`SourceSignQuotientData`; no inhabitant is supplied. -/
structure A2Node03GroupsExtensionData
    (xF cF : Iut.HyperbolicOrbicurve A.F) where
  xFGroups : SourceOrbicurveGroupData xF (Iut.AbsoluteGaloisProfinite A.F)
  cFGroups : SourceOrbicurveGroupData cF (Iut.AbsoluteGaloisProfinite A.F)
  fGroupInclusion : Iut.ProfiniteFundamentalGroupInclusion
    xFGroups.sequence.geometric xFGroups.sequence.arithmetic
    cFGroups.sequence.geometric cFGroups.sequence.arithmetic
    (Iut.AbsoluteGaloisProfinite A.F)
    xFGroups.sequence cFGroups.sequence
  xK : Iut.HyperbolicOrbicurve A.K
  cK : Iut.HyperbolicOrbicurve A.K
  xKExtension : SourceOrbicurveScalarExtension A.F A.K xF
  cKExtension : SourceOrbicurveScalarExtension A.F A.K cF
  xKType : xK.signature = sourceTypeOneLTorsion l
  cKType : cK.signature = sourceTypeOneLTorsionPlusMinus l
  xK_eq_extension : xK = xKExtension.result
  cK_eq_extension : cK = cKExtension.result

def A2Node03GroupsExtensionRequired
    (xF cF : Iut.HyperbolicOrbicurve A.F) : Prop :=
  Nonempty (A2Node03GroupsExtensionData (A := A) xF cF)

end LeanFormal.IUT.XiFPaper.Mzk1A2Node03GroupsExtensionActual
