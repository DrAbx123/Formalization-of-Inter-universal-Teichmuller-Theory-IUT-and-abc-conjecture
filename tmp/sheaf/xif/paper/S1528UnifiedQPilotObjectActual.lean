import tmp.sheaf.xif.paper.OrigXiFPaperLineBundleODActual
import tmp.sheaf.xif.paper.OneColumnFinitePrimePlaceActual
import tmp.sheaf.xif.paper.IPLAPTDataActual
import LeanFormal.IUT.IUTIII.Theorem311.ConcreteFiniteModel
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionBoundary

/-! # S1528 unified q-pilot object on the canonical lowercase core

**Canonical core.**  This file uses exactly one PaperQPilotObject core,
tmp.sheaf.xif.paper.PaperQPilotObject (via
tmp.sheaf.xif.paper.OrigXiFPaperLineBundleActual and
OrigXiFPaperLineBundleODActual).  It does **not** import the duplicate
tmp.sheaf.xif.PaperQPilotObject (S1479's core), does not declare a second
core, and introduces no completion carrier.

## What is constructed

For a paper original input I : OriginalInput l (FinitePrimePlace 2 7) and a
native totalization datum

  D : OrigXiFPaperLineBundleData I   (the exact first field of S1480:
  X : N8NativeInput l together with X.S.arithmetic = I.initial.arithmetic),

this file builds the unified object

  s1528UnifiedQPilotObject I D : PaperQPilotObject ...

on the concrete finite model, with:

1. the **actual** procession preorder: Choice := ProcessionChoice l ordered by
   the upper semi-level progression Ind3Step (not le := True);
2. lineBundle := OrigXiFPaperLineBundleCarrier I D, the actual q-pilot
   fractional-ideal O(-D) carrier of S1480 (its sections are the actual
   q-pilot O(-D), not PUnit, and its localizations are the actual completion
   embeddings; no completion-localized trivial carrier is used);
3. the four identification fields instantiated by concrete propositions about
   the actual data, each of which is proved below:
   * OrigXiFPaperStripIdentified (strip anchor + boundary theta-q agreement),
   * OrigXiFPaperLineBundleODIdentified I D (the carrier is exactly the
     O(-D) carrier of S1480),
   * OrigXiFPaperLogKummerIdentified (IUT II Def. 4.9(i) invariant-image law
     and degree preservation of the actual self Kummer arrow),
   * OrigXiFPaperQPilotScalarIdentified (the scalar is the actual bad-place
     absolute-log sum and is nonpositive).

The construction is **conditional on D**: no inhabitant of
OrigXiFPaperLineBundleData I is asserted or produced here.  This is the
"missing first field" recorded since S1499; everything else is actual.

## Relation to S1479 / S1516

The preorder instance, the strip / log-Kummer / scalar propositions and the
concrete data are copied from
tmp.sheaf.xif.paper.OrigXiFPaperQPilotObjectPreorderActual (S1479) and
rebased onto the canonical lowercase core.  S1479's completion-localized
trivial carrier is **not** copied; the line-bundle slot and its identification
come from S1480.

No sorry, axiom, True, PUnit, arbitrary inhabitant or Nonempty witness is used
for any object or identification.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.S1528Unified

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.IPLAPTDataActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperLineBundleCarrierActual
open LeanFormal.IUT.XiFPaper.OrigXiFPaperLineBundle
open LeanFormal.IUT.XiFPaper.OrigXiFPaperLineBundleODActual
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual

universe ua uv upi umon ui uG uL uC

/-! ## 1. Concrete identification propositions

These four propositions instantiate the four paper_*_identification Prop
fields of the canonical core.  They are copied from S1479, except that the
line-bundle proposition is S1480's actual O(-D) identification. -/

/-- The actual bad-place q-parameter absolute-log sum of the source contract. -/
noncomputable def OrigXiFPaperBadQAbsLog {l : PrimeGeFive}
    (S : SourceDefinition31Data l) : Real :=
  letI := S.bad_finite
  ∑ b : S.badPlaces, |Real.log (S.reduction.qParameter b)|

/-- The sum is definitionally the source candidate sourceBadQAbsLog. -/
theorem OrigXiFPaperBadQAbsLog_eq_source {l : PrimeGeFive}
    (S : SourceDefinition31Data l) :
    OrigXiFPaperBadQAbsLog S = sourceBadQAbsLog S := rfl

/-- Concrete q-pilot scalar identification: the object scalar is the actual
bad-place absolute-log sum, and it is nonpositive. -/
def OrigXiFPaperQPilotScalarIdentified {l : PrimeGeFive}
    (S : SourceDefinition31Data l) (x : Real) : Prop :=
  x = -OrigXiFPaperBadQAbsLog S ∧ x ≤ 0

/-- The source signed scalar is the negated bad-place absolute-log sum. -/
theorem sourceQPilotSignedLog_eq_neg_badQAbsLog {l : PrimeGeFive}
    (S : SourceDefinition31Data l) :
    sourceQPilotSignedLog S = -OrigXiFPaperBadQAbsLog S :=
  congrArg Neg.neg (OrigXiFPaperBadQAbsLog_eq_source S).symm

/-- Concrete strip identification: the q-pilot strip is the F-prime-strip of the
actual input Hodge theater, and the boundary's target q is that theater's
theta-q. -/
def OrigXiFPaperStripIdentified {l : PrimeGeFive} {V : Type uv}
    {Label : Type uL} {Choice : Type uC} [AddGroup Label]
    (boundary : SourceProcessionBoundary.Input (l := l) (V := V)
      (Label := Label) (Choice := Choice))
    (strip : FPrimeStrip V) : Prop :=
  strip = boundary.theater.primeStrip ∧
    boundary.target_q = boundary.theater.thetaPacket.q

/-- The strip anchor of every source boundary satisfies the concrete strip
identification. -/
theorem OrigXiFPaperStripIdentified_anchor {l : PrimeGeFive} {V : Type uv}
    {Label : Type uL} {Choice : Type uC} [AddGroup Label]
    (boundary : SourceProcessionBoundary.Input (l := l) (V := V)
      (Label := Label) (Choice := Choice)) :
    OrigXiFPaperStripIdentified boundary
      (sourceQPilotStrip boundary) :=
  ⟨rfl, boundary.target_q_eq_source⟩

/-- Concrete log-Kummer identification: the x-mu layer of the arrow satisfies
the IUT II Definition 4.9(i) invariant-image law at every place and open
subgroup, and the strip representative preserves degrees. -/
def OrigXiFPaperLogKummerIdentified {G : Type uG} [Group G]
    [TopologicalSpace G] {V : Type uv} {upper lower : FPrimeStrip V}
    (K : SourceKummerArrow G upper lower) : Prop :=
  (∀ (v : V) (H : OpenSubgroup G),
      (K.layer.kummer v).equiv ''
          (TimesMuKummer.invariantImage (K.layer.sourceAction v) H :
            Set (TimesMuQuotient ((upper.Mon v)ˣ))) =
        (TimesMuKummer.invariantImage (K.layer.targetAction v) H :
          Set (TimesMuQuotient ((lower.Mon v)ˣ)))) ∧
    (∀ (v : V) (x : upper.Mon v),
      lower.degree v (K.stripIso.isoMon v x) = upper.degree v x)

/-- Every actual reduced Kummer arrow satisfies the concrete log-Kummer
identification: the invariant-image law is the Definition 4.9(i) field of its
x-mu layer, and degree preservation is the field of its strip representative. -/
theorem OrigXiFPaperLogKummerIdentified_of_arrow {G : Type uG} [Group G]
    [TopologicalSpace G] {V : Type uv} {upper lower : FPrimeStrip V}
    (K : SourceKummerArrow G upper lower) :
    OrigXiFPaperLogKummerIdentified K :=
  ⟨fun v H => (K.layer.kummer v).invariantImage H,
    fun v x => K.stripIso.compatDegree v x⟩

/-! ## 2. Actual Ind3Step preorder on the concrete procession choices -/

/-- Actual paper preorder on procession choices: the upper semi-level
progression Ind3Step of the concrete finite model.  This is the source
upper-procession order, not a le := True placeholder. -/
instance s1528ProcessionPreorder (l : PrimeGeFive) :
    Preorder (ConcreteFiniteTheorem311.ProcessionChoice l) where
  le a b := ConcreteFiniteTheorem311.ProcessionChoice.Ind3Step a b
  lt a b := ConcreteFiniteTheorem311.ProcessionChoice.Ind3Step a b ∧
    ¬ ConcreteFiniteTheorem311.ProcessionChoice.Ind3Step b a
  le_refl a := ConcreteFiniteTheorem311.ProcessionChoice.ind3Step_refl a
  le_trans := fun _ _ _ h1 h2 =>
    ConcreteFiniteTheorem311.ProcessionChoice.ind3Step_trans h1 h2
  lt_iff_le_not_ge := fun _ _ => Iff.rfl

/-- The instance's order is exactly the actual Ind3Step progression. -/
theorem s1528ProcessionPreorder_le_iff (l : PrimeGeFive)
    (a b : ConcreteFiniteTheorem311.ProcessionChoice l) :
    (s1528ProcessionPreorder l).le a b ↔
      ConcreteFiniteTheorem311.ProcessionChoice.Ind3Step a b :=
  Iff.rfl

/-! ## 3. Actual source data of the concrete finite model -/

/-- The actual source procession boundary of the concrete finite model. -/
noncomputable abbrev OrigXiFPaperSourceBoundary (l : PrimeGeFive) :
    SourceProcessionBoundary.Input (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l) :=
  SourceProcessionBoundary.Input.concreteInput l

/-- The actual source q-pilot strip anchor. -/
noncomputable abbrev OrigXiFPaperSourceStrip (l : PrimeGeFive) :
    FPrimeStrip (FinitePrimePlace 2 7) :=
  sourceQPilotStrip (OrigXiFPaperSourceBoundary l)

/-- The canonical product group of the q-pilot strip (supplied kappa-orbit units
action datum). -/
abbrev OrigXiFPaperSourceKummerGroup (l : PrimeGeFive) : Type _ :=
  SelfGroup (OrigXiFPaperSourceStrip l)

/-- The actual self Kummer arrow on the q-pilot strip, with the supplied
kappa-orbit units actions and the identity strip representative. -/
noncomputable def OrigXiFPaperSourceKummerArrow (l : PrimeGeFive) :
    SourceKummerArrow (OrigXiFPaperSourceKummerGroup l)
      (OrigXiFPaperSourceStrip l) (OrigXiFPaperSourceStrip l) :=
  selfKummerArrow (OrigXiFPaperSourceStrip l)

/-! ## 4. The unified object on the canonical lowercase core, conditional on D -/

variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))

/-- **The unified paper q-pilot object** on the canonical lowercase core.

lineBundle is the actual q-pilot O(-D) carrier OrigXiFPaperLineBundleCarrier I D
of S1480 (conditional exactly on D), the preorder is the actual Ind3Step
progression, and the four paper_*_identification Prop fields are the concrete
propositions of section 1, instantiated by the actual data. -/
noncomputable def s1528UnifiedQPilotObject
    (D : OrigXiFPaperLineBundleData I) :
    PaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      I (OrigXiFPaperSourceKummerGroup l) (OrigXiFPaperSourceStrip l) where
  boundary := OrigXiFPaperSourceBoundary l
  strip := OrigXiFPaperSourceStrip l
  strip_eq_source := rfl
  oneColumn := actualOneColumnFinitePrimePlace
  lineBundle := OrigXiFPaperLineBundleCarrier I D
  logKummer := OrigXiFPaperSourceKummerArrow l
  qPilotLogVolume := sourceQPilotSignedLog I.initial
  qPilotLogVolume_eq := rfl
  paper_strip_identification :=
    OrigXiFPaperStripIdentified (OrigXiFPaperSourceBoundary l)
      (OrigXiFPaperSourceStrip l)
  paper_lineBundle_identification :=
    OrigXiFPaperLineBundleODIdentified I D
      (OrigXiFPaperLineBundleCarrier I D)
  paper_logKummer_identification :=
    OrigXiFPaperLogKummerIdentified (OrigXiFPaperSourceKummerArrow l)
  paper_qPilot_log_identification :=
    OrigXiFPaperQPilotScalarIdentified I.initial
      (sourceQPilotSignedLog I.initial)

/-- The line-bundle slot is exactly S1480's actual O(-D) carrier; no
completion-localized trivial carrier is used. -/
theorem s1528UnifiedQPilotObject_lineBundle_eq
    (D : OrigXiFPaperLineBundleData I) :
    (s1528UnifiedQPilotObject I D).lineBundle =
      OrigXiFPaperLineBundleCarrier I D := rfl

/-- The section type of the line-bundle slot is the actual q-pilot O(-D)
fractional ideal, not a completion-localized trivial section type. -/
theorem s1528UnifiedQPilotObject_lineBundle_total
    (D : OrigXiFPaperLineBundleData I) :
    (s1528UnifiedQPilotObject I D).lineBundle.total =
      ↥(OrigXiFPaperQPilotLineBundle I D) := rfl

/-! ## 5. The four identification fields hold for the constructed object -/

/-- The object's strip placeholder is the concrete strip proposition, and it
holds. -/
theorem s1528UnifiedQPilotObject_paper_strip
    (D : OrigXiFPaperLineBundleData I) :
    (s1528UnifiedQPilotObject I D).paper_strip_identification :=
  OrigXiFPaperStripIdentified_anchor (OrigXiFPaperSourceBoundary l)

/-- The object's line-bundle placeholder is S1480's actual O(-D)
identification, and it holds. -/
theorem s1528UnifiedQPilotObject_paper_lineBundle
    (D : OrigXiFPaperLineBundleData I) :
    (s1528UnifiedQPilotObject I D).paper_lineBundle_identification :=
  OrigXiFPaperLineBundleODCarrier_identified I D

/-- The object's log-Kummer placeholder is the concrete log-Kummer
proposition, and it holds. -/
theorem s1528UnifiedQPilotObject_paper_logKummer
    (D : OrigXiFPaperLineBundleData I) :
    (s1528UnifiedQPilotObject I D).paper_logKummer_identification :=
  OrigXiFPaperLogKummerIdentified_of_arrow
    (OrigXiFPaperSourceKummerArrow l)

/-- The object's q-pilot scalar placeholder is the concrete scalar proposition,
and it holds. -/
theorem s1528UnifiedQPilotObject_paper_qPilot_log
    (D : OrigXiFPaperLineBundleData I) :
    (s1528UnifiedQPilotObject I D).paper_qPilot_log_identification :=
  ⟨sourceQPilotSignedLog_eq_neg_badQAbsLog I.initial,
    sourceQPilotSignedLog_nonpos I.initial⟩

/-- All four identification fields of the constructed object are concrete
propositions about the actual data, and all four hold. -/
theorem s1528UnifiedQPilotObject_identifications
    (D : OrigXiFPaperLineBundleData I) :
    (s1528UnifiedQPilotObject I D).paper_strip_identification ∧
    (s1528UnifiedQPilotObject I D).paper_lineBundle_identification ∧
    (s1528UnifiedQPilotObject I D).paper_logKummer_identification ∧
    (s1528UnifiedQPilotObject I D).paper_qPilot_log_identification :=
  ⟨s1528UnifiedQPilotObject_paper_strip I D,
    s1528UnifiedQPilotObject_paper_lineBundle I D,
    s1528UnifiedQPilotObject_paper_logKummer I D,
    s1528UnifiedQPilotObject_paper_qPilot_log I D⟩

/-- The object's log-volume is the negated actual bad-place absolute-log sum. -/
theorem s1528UnifiedQPilotObject_qPilotLogVolume
    (D : OrigXiFPaperLineBundleData I) :
    (s1528UnifiedQPilotObject I D).qPilotLogVolume =
      -OrigXiFPaperBadQAbsLog I.initial :=
  sourceQPilotSignedLog_eq_neg_badQAbsLog I.initial

/-- The object's log-volume is nonpositive. -/
theorem s1528UnifiedQPilotObject_qPilotLogVolume_nonpos
    (D : OrigXiFPaperLineBundleData I) :
    (s1528UnifiedQPilotObject I D).qPilotLogVolume ≤ 0 :=
  sourceQPilotSignedLog_nonpos I.initial

/-! ## 6. Type / axiom gates -/

#check @s1528UnifiedQPilotObject
#check @s1528UnifiedQPilotObject_paper_lineBundle
#check @s1528UnifiedQPilotObject_identifications

#print axioms s1528UnifiedQPilotObject
#print axioms s1528UnifiedQPilotObject_paper_lineBundle
#print axioms s1528UnifiedQPilotObject_identifications

end LeanFormal.IUT.XiFPaper.S1528Unified

end
