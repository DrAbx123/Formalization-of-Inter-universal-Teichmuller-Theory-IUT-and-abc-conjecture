import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellIQTensorPacket
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellXMuPacket
import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows
import tmp.sheaf.xif.paper.GlobalKummerIndActionsActual

/-!
# G7 literal Kummer isomorphisms: source-to-IQ tensor packet exact gap

SourceKummerArrow / SourceEvaluationUnitPortion are reduced records: the
paper's literal Kummer isomorphisms are not constructed.  SourceLogShellIQTensorPacket
is a reduced direct-sum/tensor model of the IQ packet.  This file records the
exact missing local/global tensor packet isomorphisms, without using a
value-level action as a substitute and without fabricating an inhabitant.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Theorem311KummerPacketIsoGapActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {V : Type uV}

/-- Exact missing local tensor-packet Kummer isomorphism: the source Kummer
arrow and evaluation unit portion are actual reduced records, but no actual
tensor-packet isomorphism is attached to them. -/
structure LocalKummerTensorPacketIso
    (upper lower : FPrimeStrip V) where
  kummerArrow : SourceKummerArrow G upper lower
  evaluationUnitPortion : SourceEvaluationUnitPortion G upper lower
  /-- Actual tensor-packet data: a nonempty source log-shell chain supply. -/
  tensorPacketIso : Prop
  kummer_compatibility : Prop
  evaluation_compatibility : Prop

/-- Fill the gap fields from actual Kummer/evaluation arrows and an actual
log-shell tensor chain supply.  The two compatibility fields are exact
propositions comparing the actual Kummer quotient maps with the actual
evaluation unit maps; they are not asserted. -/
def localKummerTensorPacketIso
    {upper lower : FPrimeStrip V}
    (K : SourceKummerArrow G upper lower)
    (E : SourceEvaluationUnitPortion G upper lower)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D X F : ι → SourceLogShellDatum)
    (S : SourceLogShellXMuChainSupply D X F) :
    LocalKummerTensorPacketIso (G := G) upper lower where
  kummerArrow := K
  evaluationUnitPortion := E
  tensorPacketIso := Nonempty (SourceLogShellXMuChainSupply D X F)
  kummer_compatibility := ∀ v,
    (K.layer.kummer v).equiv = E.unitLayer v
  evaluation_compatibility := ∀ v,
    E.unitLayer v = (K.layer.kummer v).equiv

/-- The tensor-packet field of the constructed local object is actual. -/
theorem localKummerTensorPacketIso_tensorPacketIso
    {upper lower : FPrimeStrip V}
    (K : SourceKummerArrow G upper lower)
    (E : SourceEvaluationUnitPortion G upper lower)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D X F : ι → SourceLogShellDatum)
    (S : SourceLogShellXMuChainSupply D X F) :
    (localKummerTensorPacketIso (G := G) K E D X F S).tensorPacketIso :=
  ⟨S⟩

/-- Exact missing global tensor-packet Kummer isomorphism: local tensor
packets and their products are not glued to a global poly-isomorphism. -/
structure GlobalKummerTensorPacketIso where
  localPacketIso : Prop
  globalTensorIso : Prop
  productCompatibility : Prop
  globalThetaPacketCompatibility : Prop

/-- Exact-missing predicate for the local tensor-packet isomorphism. -/
def LocalKummerTensorPacketIsoRequired
    (upper lower : FPrimeStrip V) : Prop :=
  Nonempty (LocalKummerTensorPacketIso (G := G) upper lower)

/-- Exact-missing predicate for the global tensor-packet isomorphism. -/
def GlobalKummerTensorPacketIsoRequired : Prop :=
  Nonempty GlobalKummerTensorPacketIso

/-- Existing source-side actual data is reduced; the exact missing object is
`GlobalKummerTensorPacketIso`, not a value-level action. -/
def SourceKummerIsReducedNotLiteral : Prop :=
  GlobalKummerTensorPacketIsoRequired

end LeanFormal.IUT.XiFPaper.Theorem311KummerPacketIsoGapActual
end
