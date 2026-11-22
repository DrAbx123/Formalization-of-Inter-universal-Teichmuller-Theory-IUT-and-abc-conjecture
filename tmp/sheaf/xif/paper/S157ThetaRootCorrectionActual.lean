import tmp.sheaf.xif.paper.PaperC3ThetaRootActual

/-! # S157: paper root theta power correction

thetaPacket.scale j is the q-parameter power q^(j^2).  The paper theta value
uses the double-underlined 2l-th root q_v, so the correct object is the actual
paperRootThetaUnit / its power in the algebraic closure.

This file records the actual root theta power and its defining 2l-th power
relation, without identifying it with thetaPacket.scale.

No fake root/parameter equality/sorry/axiom/True/PUnit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S157ThetaRootCorrectionActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual

universe u v

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

/-- Corrected paper root theta value: the actual root theta unit at label j. -/
noncomputable def paperRootThetaPower
    (j : SignedLabel l.value) : RootThetaCarrier (l := l) (G := G) :=
  paperRootThetaImagePoint (G := G) j

/-- The corrected root theta power has the defining 2l-th power relation. -/
theorem paperRootThetaPower_pow_twoL
    (j : SignedLabel l.value) (v : V) :
    (paperRootThetaPower (G := G) j v) ^ (2 * l.value) =
      (unitToAlgClosed (G.qUnit v)) ^ (gaussExponent j.1).toNat :=
  paperRootThetaUnit_pow_twoL (G := G) j v

/-- Exact gap: thetaPacket.scale is a q-parameter power in the completion,
while paperRootThetaPower is a root unit in the algebraic closure.  No map or
equality between them is asserted. -/
structure ThetaPacketScaleRootRelationGap where
  qParameterScale : Real
  rootCarrier : Type v
  bridge : Prop

end LeanFormal.IUT.XiFPaper.S157ThetaRootCorrectionActual

end
