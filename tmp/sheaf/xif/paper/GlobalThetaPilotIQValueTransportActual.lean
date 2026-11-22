import tmp.sheaf.xif.paper.GlobalThetaPilotIQEmbeddingFromPrimeStripActual

/-!
# Global Theta-pilot IQ value transport

The global Theta-pilot carrier is

  GlobalThetaPilotCarrier = (v : V) -> I.ThetaPilotPoint v,

and
  I.ThetaPilotPoint v = (ThetaPilotCarrier x SignedLabel) -> I.ValueMonoidAt 0 0 v.

The global IQ ambient is the actual tensor packet
  LiteralIQAmbient C3 j = ArithmeticPacketTensor (literalIQPlaces C3 j),
whose factors are completion packets.

A value transport would need, for every v, a map

  I.ValueMonoidAt 0 0 v -> CompletionPacket (C3 tensor place at v),

plus the tensor assembly into LiteralIQAmbient.  The actual source prime strip
carries the value monoid I.ValueMonoidAt 0 0 v and its degree homomorphism
Mon v ->* Multiplicative Real, but no monoid map from that value monoid to the
p-adic completion packet.  The degree is only a real-valued homomorphism.

This file constructs the actual log-degree projections on the global carrier and
records the exact missing mono-analytic/value-to-completion transport.  It does
not fabricate an embedding into the tensor ambient.

No PUnit/True, arbitrary data, axiom or sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.GlobalThetaPilotIQValueTransportActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.XiFPaper.LiteralIQCarrierConstruction
open LeanFormal.IUT.XiFPaper.GlobalIQHullThetaPilotActual
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotIQEmbeddingFromPrimeStripActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [forall i, Fintype (C3.tensorPlaceIndex i)]
variable (j : Nat)
variable (P : PrimeStripC3PlaceComparison (V := V) (I := I) C3)

/-- Actual global log-degree projection of a Theta-pilot point at a chosen
component n,j and place v. -/
def globalThetaPilotLogDegree
    (n : ThetaPilotCarrier l) (s : SignedLabel l.value)
    (x : GlobalThetaPilotCarrier (I := I)) (v : V) : Real :=
  I.logDegreeAt 0 0 v (x v (n, s))

/-- The actual global log-degree profile. -/
def globalThetaPilotLogDegreeProfile
    (n : ThetaPilotCarrier l) (s : SignedLabel l.value)
    (x : GlobalThetaPilotCarrier (I := I)) : V → Real :=
  fun v => globalThetaPilotLogDegree (I := I) n s x v

/-- The actual log-degree at one place is the source logDegreeAt. -/
theorem globalThetaPilotLogDegree_eq
    (n : ThetaPilotCarrier l) (s : SignedLabel l.value)
    (x : GlobalThetaPilotCarrier (I := I)) (v : V) :
    globalThetaPilotLogDegree (I := I) n s x v =
      I.logDegreeAt 0 0 v (x v (n, s)) := rfl

/-- Exact missing value-to-completion transport at one aligned place. -/
structure GlobalThetaPilotValueToCompletion
    (v : V) where
  toCompletion : I.ValueMonoidAt 0 0 v →
    CommonPrimeCompletion (P.stripPlace v)

/-- Exact missing tensor assembly from the completion-valued factors into the
literal IQ ambient. -/
structure GlobalThetaPilotIQTensorAssembly where
  assemble : ((v : V) → CommonPrimeCompletion (P.stripPlace v)) →
    LiteralIQAmbient (C3 := C3) j

/-- Exact obstruction: no mono-analytic value-to-completion map and no tensor
assembly are supplied by the actual prime-strip/place data. -/
def GlobalThetaPilotIQValueTransportObstruction : Prop :=
  (∀ v : V, Nonempty (GlobalThetaPilotValueToCompletion (I := I) C3 P v)) ∧
    Nonempty (GlobalThetaPilotIQTensorAssembly (I := I) C3 j P)

/-- Exact value-transport datum from the actual global Theta-pilot carrier to the
literal IQ ambient. -/
structure GlobalThetaPilotIQValueTransportActual where
  embed : GlobalThetaPilotCarrier (I := I) → LiteralIQAmbient (C3 := C3) j

/-- The exact value-transport obstruction is exactly the missing map. -/
def GlobalThetaPilotIQValueTransportActualObstruction : Prop :=
  Nonempty (GlobalThetaPilotIQValueTransportActual (I := I) C3 j)

/-- Conditional construction: any actual value transport gives the embedding
data of the previous layer. -/
noncomputable def globalThetaPilotIQEmbeddingOfValueTransport
    (T : GlobalThetaPilotIQValueTransportActual (I := I) C3 j) :
    GlobalThetaPilotIQEmbeddingData (I := I) C3 j where
  embed := T.embed

/-- The embedding map is the value-transport map. -/
theorem globalThetaPilotIQEmbeddingOfValueTransport_embed
    (T : GlobalThetaPilotIQValueTransportActual (I := I) C3 j) :
    (globalThetaPilotIQEmbeddingOfValueTransport (I := I) C3 j T).embed =
      T.embed := rfl

end LeanFormal.IUT.XiFPaper.GlobalThetaPilotIQValueTransportActual

end
