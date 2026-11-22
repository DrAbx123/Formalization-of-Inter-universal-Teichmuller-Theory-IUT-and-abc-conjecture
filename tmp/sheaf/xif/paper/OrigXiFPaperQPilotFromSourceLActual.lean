import tmp.sheaf.xif.paper.S1391C3LSourcePilotActual
import tmp.sheaf.xif.PaperQPilotObject
import tmp.sheaf.xif.paper.PaperQPilotObjectSourceActual
import tmp.sheaf.xif.paper.PaperQPilotObjectConcreteActual
import tmp.sheaf.xif.paper.OneColumnFinitePrimePlaceActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

/-!
# OrigXiF: the paper q-pilot object from the S1391 actual L-side source pilot

Layer: **O** (原文 Θ-link xi-f / 原文 q-pilot object).  This file does not touch
the normalized model (N), the native target (T), the `SourceDefinition31Data`
contract (S), or the D4-D9 assembly (D).  Name prefix: `OrigXiF`.

## What is used as input

S1391 (`S1391C3LSourcePilotActual`) supplies the actual L-carrier replacement
`SourcePilotRegionDataL` for the *old* completion-valued `SourcePilotRegionData`:
the L-side q (`FinitePlaceQCandidate place.val`), the source theta packet
(`FiniteThetaPacket l`), the Galois-indexed root/Kummer block over the algebraic
closure, and the actual diagonal tensor unit/landing.  The old completion-valued
`SourcePilotRegionData` is **not** constructed and **not** consumed in this file.

## What this file attaches

`PaperQPilotObject` (`tmp/sheaf/xif/PaperQPilotObject.lean`) has five data
fields.  Their sources in this file are:

| field | term used here |
|---|---|
| `boundary` | the **exact first field**; not supplied by S1391 (see below) |
| `strip` | `sourceQPilotStrip boundary` (forced by `strip_eq_source`) |
| `oneColumn` | `actualOneColumnFinitePrimePlace` (actual 1-column AS of `Fmod`) |
| `lineBundle` | `OrigXiFSourceLLineBundleCarrier` (actual carrier over the L base field, read at the L place) |
| `logKummer` | `selfKummerArrow (sourceQPilotStrip boundary)` (actual self Kummer arrow) |
| `qPilotLogVolume` | `sourceQPilotSignedLog I.initial` (forced by `qPilotLogVolume_eq`) |

## The exact first field

The first field of `PaperQPilotObject` is

  boundary : SourceProcessionBoundary.Input (l := l) (V := FinitePrimePlace 2 7)
    (Label := ConcreteFiniteTheorem311.finiteLabel l)
    (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)

a Hodge theater together with its dependent history.  The S1391 L record carries
no Hodge theater and no history: its fields are the completion q, the theta
packet, the Galois-indexed root/Kummer block and the tensor block.  It therefore
supplies **no term** of this type, and no carrier-level Hodge theater is
fabricated here.  §1 records the exact first-field type and its projection, §2-§3
record the actual L-side anchors, §4 constructs the paper q-pilot object from a
term of exactly that type, and §5 records the L-side attachments.

The four `paper_*_identification` fields are inherited unchanged from
`paperQPilotObjectSourceActual` (the uninhabited paper target records); turning
them into concrete propositions is a separate obligation
(coord/XI_F_ORIGINAL_ROUTE.md §4.1) and is not claimed here.

## Actual versus open

Actual (proved here): the L place is a finite place of the base field and the
line-bundle fiber ring at the L place is exactly the completion carrying the L q
unit, with the L q nonzero in that fiber; the L q scalar is
`localSignedLog D.q = log ‖q‖ < 0`; the actual L record's theta packet is the
concrete source theater theta packet and its q unit is the concrete q unit; the
L tensor landing law holds.  The paper q-pilot object's five data fields are
actual and are functions of the exact first field and of `I`.

Open (recorded as exact propositions, no inhabitant): the L-side q scalar equals
the source q-pilot scalar `sourceQPilotSignedLog I.initial`, and the L theta
packet's q equals the boundary's target q.  Their consequences are proved.

No `sorry`, `admit`, `axiom`, `True`, `PUnit`, or arbitrary inhabitant is used.
-/

noncomputable section
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.OrigXiFPaperQPilotFromSourceLActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
open LeanFormal.IUT.XiFPaper.PaperLineBundleCarrierActual
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual
open LeanFormal.IUT.XiFPaper.S1219ConcreteTensorLandingActual
open LeanFormal.IUT.Theorem311Source.IPLAPTDataActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.SourceProcessionBoundary

universe upi umon ui

variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

/-! ## 1. The exact first field -/

/-- The exact type of the first field of the paper q-pilot object at the source-L
configuration: a Hodge theater with its dependent history.  The S1391 actual L
record supplies no term of it, so §4 takes a term of this type as the single
external input of the construction. -/
abbrev OrigXiFQPilotFirstFieldType : Type _ :=
  SourceProcessionBoundary.Input (l := l) (V := FinitePrimePlace 2 7)
    (Label := ConcreteFiniteTheorem311.finiteLabel l)
    (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)

/-- The first-field projection of a paper q-pilot object at the source-L
configuration. -/
def OrigXiFQPilotFirstField
    {G : Type _} [Group G] [TopologicalSpace G]
    {envStrip : FPrimeStrip (FinitePrimePlace 2 7)}
    (O : PaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l) I G envStrip) :
    OrigXiFQPilotFirstFieldType (l := l) :=
  O.boundary

/-- The first-field projection is exactly the object's `boundary` field. -/
theorem OrigXiFQPilotFirstField_eq
    {G : Type _} [Group G] [TopologicalSpace G]
    {envStrip : FPrimeStrip (FinitePrimePlace 2 7)}
    (O : PaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l) I G envStrip) :
    OrigXiFQPilotFirstField (I := I) O = O.boundary := rfl

/-- The dependent `strip` law of the paper q-pilot object is stated on the exact
first field: the strip is the first field's Hodge-theater prime strip. -/
theorem OrigXiFQPilotFirstField_strip
    {G : Type _} [Group G] [TopologicalSpace G]
    {envStrip : FPrimeStrip (FinitePrimePlace 2 7)}
    (O : PaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l) I G envStrip) :
    O.strip = sourceQPilotStrip (OrigXiFQPilotFirstField (I := I) O) :=
  O.strip_eq_source

/-- The exact first field is inhabited by the actual concrete source boundary.
The concrete source boundary lives at the trivial universe instantiation of the
first-field type; the instantiation does not involve the S1391 L record. -/
theorem OrigXiFQPilotFirstFieldType_nonempty :
    Nonempty (OrigXiFQPilotFirstFieldType.{0, 0, 0} (l := l)) :=
  ⟨SourceProcessionBoundary.Input.concreteInput l⟩

/-! ## 2. The L-side q scalar of the S1391 actual record -/

/-- The L-side q scalar of the actual S1391 L record: the signed log of the L q.
This is the actual completion logarithm of `localSignedLog`, not a normalized or
source-assembly scalar. -/
noncomputable def OrigXiFSourceLQScalar (D : SourcePilotRegionDataL (I := I)) : Real :=
  localSignedLog D.q

/-- The L-side q scalar is the logarithm of the norm of the L q. -/
theorem OrigXiFSourceLQScalar_eq_log_norm (D : SourcePilotRegionDataL (I := I)) :
    OrigXiFSourceLQScalar (I := I) D = Real.log ‖D.q.q‖ := rfl

/-- The L-side q scalar is negative (the L q is contracting). -/
theorem OrigXiFSourceLQScalar_neg (D : SourcePilotRegionDataL (I := I)) :
    OrigXiFSourceLQScalar (I := I) D < 0 :=
  localSignedLog_neg D.q

/-- The L-side q scalar is the negative of the local log magnitude. -/
theorem OrigXiFSourceLQScalar_eq_neg_magnitude (D : SourcePilotRegionDataL (I := I)) :
    OrigXiFSourceLQScalar (I := I) D = -localLogMagnitude D.q :=
  localSignedLog_eq_neg_magnitude D.q

/-- The L-side q scalar has the local log magnitude as absolute value. -/
theorem OrigXiFSourceLQScalar_abs (D : SourcePilotRegionDataL (I := I)) :
    |OrigXiFSourceLQScalar (I := I) D| = localLogMagnitude D.q :=
  abs_localSignedLog D.q

/-- The actual S1391 L record's q is the concrete q candidate. -/
theorem OrigXiFActualSourceL_q :
    (actualSourcePilotRegionDataL (I := I) place).q =
      concreteQCandidate (I := I) place := rfl

/-- The actual S1391 L record's completion q unit is the concrete q unit. -/
theorem OrigXiFActualSourceL_qUnit :
    (actualSourcePilotRegionDataL (I := I) place).qUnit =
      concreteQUnit (I := I) place := rfl

/-- The actual S1391 L record's theta packet is the concrete source theater
theta packet. -/
theorem OrigXiFActualSourceL_thetaPacket :
    (actualSourcePilotRegionDataL (I := I) place).thetaPacket =
      concreteThetaPacket (I := I) := rfl

/-- The actual S1391 L record's q scalar is the concrete q scalar. -/
theorem OrigXiFActualSourceL_qScalar :
    OrigXiFSourceLQScalar (I := I) (actualSourcePilotRegionDataL (I := I) place) =
      localSignedLog (concreteQCandidate (I := I) place) := rfl

/-! ## 3. The L-side line-bundle anchor -/

/-- The actual pole-allowing paper line-bundle carrier over the L record's base
field `Fmod`: total `Fmod`, localizations into the completion fields.  The
S1391 L record anchors this carrier through its place (theorems below identify
the fiber ring at that place with the completion carrying the L q unit). -/
noncomputable def OrigXiFSourceLLineBundleCarrier :
    PaperLineBundleCarrier (k := I.initial.arithmetic.Fmod) where
  total := I.initial.arithmetic.Fmod
  localization v x :=
    algebraMap (I.initial.arithmetic.Fmod)
      (NumberFieldFinitePlace.Completion v) x

/-- The carrier's localization at the L place is the completion map of `Fmod`. -/
theorem OrigXiFSourceLLineBundleCarrier_localization
    (D : SourcePilotRegionDataL (I := I)) (x : I.initial.arithmetic.Fmod) :
    (OrigXiFSourceLLineBundleCarrier (I := I)).localization D.place.val x =
      algebraMap (I.initial.arithmetic.Fmod)
        (NumberFieldFinitePlace.Completion D.place.val) x := rfl

/-- The fiber ring of the line-bundle carrier at the L place is exactly the
common prime completion that carries the L q unit. -/
theorem OrigXiFSourceLLineBundle_fiber_ring (D : SourcePilotRegionDataL (I := I)) :
    NumberFieldFinitePlace.Completion D.place.val = CommonPrimeCompletion D.place :=
  rfl

/-- The L q is nonzero in the line-bundle fiber at the L place. -/
theorem OrigXiFSourceLLineBundle_fiber_q_ne_zero
    (D : SourcePilotRegionDataL (I := I)) :
    (D.q.q : CommonPrimeCompletion D.place) ≠ 0 :=
  D.q.q_ne_zero

/-- The L q unit is nonzero in the line-bundle fiber at the L place. -/
theorem OrigXiFSourceLLineBundle_fiber_qUnit_ne_zero
    (D : SourcePilotRegionDataL (I := I)) :
    (D.qUnit : CommonPrimeCompletion D.place) ≠ 0 := by
  rw [D.qUnit_eq]
  exact D.q.q_ne_zero

/-! ## 4. The actual paper q-pilot object from the exact first field -/

/-- The actual paper q-pilot object of the source-L configuration, built from the
exact first field.  The `strip` is forced by the first field, the one-column
structure and the line-bundle carrier are the actual ones, the Kummer arrow is
the actual self arrow on the q-pilot strip, and the q-pilot log-volume is the
actual source scalar. -/
noncomputable def OrigXiFPaperQPilotOfBoundary
    (b : OrigXiFQPilotFirstFieldType (l := l)) :
    PaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      I (SelfGroup (sourceQPilotStrip b)) (sourceQPilotStrip b) :=
  paperQPilotObjectSourceActual (I := I) (G := SelfGroup (sourceQPilotStrip b))
    (envStrip := sourceQPilotStrip b) b actualOneColumnFinitePrimePlace
    (OrigXiFSourceLLineBundleCarrier (I := I))
    (selfKummerArrow (sourceQPilotStrip b))

/-- The boundary field of the constructed object is the exact first field. -/
theorem OrigXiFPaperQPilotOfBoundary_boundary
    (b : OrigXiFQPilotFirstFieldType (l := l)) :
    (OrigXiFPaperQPilotOfBoundary (I := I) b).boundary = b := rfl

/-- The strip field is the source q-pilot strip of the exact first field. -/
theorem OrigXiFPaperQPilotOfBoundary_strip
    (b : OrigXiFQPilotFirstFieldType (l := l)) :
    (OrigXiFPaperQPilotOfBoundary (I := I) b).strip = sourceQPilotStrip b := rfl

/-- The strip field is the Hodge-theater prime strip of the exact first field. -/
theorem OrigXiFPaperQPilotOfBoundary_strip_theater
    (b : OrigXiFQPilotFirstFieldType (l := l)) :
    (OrigXiFPaperQPilotOfBoundary (I := I) b).strip = b.theater.primeStrip := rfl

/-- The one-column field is the actual one-column arithmetic holomorphic
structure of the L base field. -/
theorem OrigXiFPaperQPilotOfBoundary_oneColumn
    (b : OrigXiFQPilotFirstFieldType (l := l)) :
    (OrigXiFPaperQPilotOfBoundary (I := I) b).oneColumn =
      actualOneColumnFinitePrimePlace := rfl

/-- The line-bundle field is the actual carrier over the L base field. -/
theorem OrigXiFPaperQPilotOfBoundary_lineBundle
    (b : OrigXiFQPilotFirstFieldType (l := l)) :
    (OrigXiFPaperQPilotOfBoundary (I := I) b).lineBundle =
      OrigXiFSourceLLineBundleCarrier (I := I) := rfl

/-- The log-Kummer field is the actual self Kummer arrow on the q-pilot strip. -/
theorem OrigXiFPaperQPilotOfBoundary_logKummer
    (b : OrigXiFQPilotFirstFieldType (l := l)) :
    (OrigXiFPaperQPilotOfBoundary (I := I) b).logKummer =
      selfKummerArrow (sourceQPilotStrip b) := rfl

/-- The q-pilot log-volume field is the actual source q-pilot scalar. -/
theorem OrigXiFPaperQPilotOfBoundary_qPilotLogVolume
    (b : OrigXiFQPilotFirstFieldType (l := l)) :
    (OrigXiFPaperQPilotOfBoundary (I := I) b).qPilotLogVolume =
      sourceQPilotSignedLog I.initial := rfl

/-- The five data fields of the paper q-pilot object, all actual, as functions of
the exact first field and of the source input `I`.  The S1391 L record enters no
data field; it enters through the identifications and fiber theorems of §5. -/
theorem OrigXiFPaperQPilotOfBoundary_data
    (b : OrigXiFQPilotFirstFieldType (l := l)) :
    (OrigXiFPaperQPilotOfBoundary (I := I) b).strip = sourceQPilotStrip b ∧
    (OrigXiFPaperQPilotOfBoundary (I := I) b).oneColumn =
      actualOneColumnFinitePrimePlace ∧
    (OrigXiFPaperQPilotOfBoundary (I := I) b).lineBundle =
      OrigXiFSourceLLineBundleCarrier (I := I) ∧
    (OrigXiFPaperQPilotOfBoundary (I := I) b).logKummer =
      selfKummerArrow (sourceQPilotStrip b) ∧
    (OrigXiFPaperQPilotOfBoundary (I := I) b).qPilotLogVolume =
      sourceQPilotSignedLog I.initial :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## 5. The L-side attachments to the paper q-pilot fields -/

/-- The open identification between the L-side q scalar of the S1391 record and
the source q-pilot log-volume forced by `qPilotLogVolume_eq`.  No inhabitant is
constructed: `sourceQPilotSignedLog` aggregates the bad q-parameters of
`I.initial`, while the L-side scalar is the completion logarithm of one L q. -/
def OrigXiFQPilotLogVolumeIdentification (D : SourcePilotRegionDataL (I := I)) : Prop :=
  OrigXiFSourceLQScalar (I := I) D = sourceQPilotSignedLog I.initial

/-- The identification is exactly the equality of the two scalars. -/
theorem OrigXiFQPilotLogVolumeIdentification_iff
    (D : SourcePilotRegionDataL (I := I)) :
    OrigXiFQPilotLogVolumeIdentification (I := I) D ↔
      OrigXiFSourceLQScalar (I := I) D = sourceQPilotSignedLog I.initial :=
  Iff.rfl

/-- Under the exact identification, the paper object's `qPilotLogVolume` field is
the L-side q scalar of the S1391 record. -/
theorem OrigXiFPaperQPilotOfBoundary_qPilotLogVolume_eq_sourceL
    (D : SourcePilotRegionDataL (I := I))
    (b : OrigXiFQPilotFirstFieldType (l := l))
    (h : OrigXiFQPilotLogVolumeIdentification (I := I) D) :
    (OrigXiFPaperQPilotOfBoundary (I := I) b).qPilotLogVolume =
      OrigXiFSourceLQScalar (I := I) D := by
  rw [OrigXiFPaperQPilotOfBoundary_qPilotLogVolume]
  exact h.symm

/-- The open identification between the L-side theta packet q of the S1391 record
and the Hodge-theater theta packet q of the exact first field. -/
def OrigXiFThetaPacketIdentification (D : SourcePilotRegionDataL (I := I))
    (b : OrigXiFQPilotFirstFieldType (l := l)) : Prop :=
  D.thetaPacket.q = b.theater.thetaPacket.q

/-- The theta-packet identification is exactly the identification with the
boundary's actual target q. -/
theorem OrigXiFThetaPacketIdentification_iff_target_q
    (D : SourcePilotRegionDataL (I := I))
    (b : OrigXiFQPilotFirstFieldType (l := l)) :
    OrigXiFThetaPacketIdentification (I := I) D b ↔ D.thetaPacket.q = b.target_q := by
  unfold OrigXiFThetaPacketIdentification
  rw [b.target_q_eq_source]

/-- Under the theta-packet identification, the L theta packet's q is the
boundary's target q. -/
theorem OrigXiFThetaPacketIdentification_target_q
    (D : SourcePilotRegionDataL (I := I))
    (b : OrigXiFQPilotFirstFieldType (l := l))
    (h : OrigXiFThetaPacketIdentification (I := I) D b) :
    D.thetaPacket.q = b.target_q :=
  (OrigXiFThetaPacketIdentification_iff_target_q (I := I) D b).mp h

/-- The L tensor landing law of the S1391 record: the completion q lands at the
tensor unit.  No paper q-pilot field consumes the tensor block, so this law is
recorded on the L record itself. -/
theorem OrigXiFSourceLTensorLanding (D : SourcePilotRegionDataL (I := I)) :
    D.tensorLanding
        (D.q.q : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) D.place) =
      (D.tensorUnit : ArithmeticTensorTupleBlock D.tensorPlaces D.tensorTuple) :=
  D.tensorLanding_q

/-- The actual S1391 L record's tensor landing is the concrete diagonal landing. -/
theorem OrigXiFActualSourceL_tensorLanding :
    (actualSourcePilotRegionDataL (I := I) place).tensorLanding =
      concreteTensorLanding (I := I) place := rfl

/-! ## 6. Axiom check -/

#print axioms OrigXiFPaperQPilotOfBoundary
#print axioms OrigXiFPaperQPilotOfBoundary_data
#print axioms OrigXiFPaperQPilotOfBoundary_qPilotLogVolume_eq_sourceL
#print axioms OrigXiFSourceLLineBundle_fiber_qUnit_ne_zero
#print axioms OrigXiFQPilotFirstFieldType_nonempty

end LeanFormal.IUT.XiFPaper.OrigXiFPaperQPilotFromSourceLActual

end
