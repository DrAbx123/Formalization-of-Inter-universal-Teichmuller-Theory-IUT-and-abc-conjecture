import tmp.sheaf.xif.PaperQPilotObject
import tmp.sheaf.xif.paper.PaperLineBundleCarrierBase
import tmp.sheaf.xif.paper.OneColumnFinitePrimePlaceActual
import tmp.sheaf.xif.paper.IPLAPTDataActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionBoundary
import LeanFormal.IUT.Foundations.NumberField.PlaceCompletionCarrier

/-! # OrigXiF: actual paper q-pilot object (original Theta-link layer, O)

This file is in the **original Theta-link layer (O)**, not the normalized
model (N), the native target (T), the SourceDefinition31Data contract (S), or
the D4D9Supply assembly (D).  It does not use ActualPaperXiFTarget, the
normalized qVFam scalar, SourceNativeInitialThetaData, or any D5--D9 data.

## What is constructed

An actual OrigXiFPaperQPilotObject on the concrete finite-place carrier
V = FinitePrimePlace 2 7, from the paper's allowed input
I : OriginalInput l (FinitePrimePlace 2 7) and actual source structures:

* boundary is the actual SourceProcessionBoundary.Input.concreteInput l;
* strip is the actual source q-pilot strip anchor sourceQPilotStrip boundary
  (definitionally the prime strip of the input Hodge theater);
* oneColumn is the actual one-column arithmetic holomorphic structure of the
  completed local rings O_v and local fields K_v
  (actualOneColumnFinitePrimePlace: completion integers of Q at the rational
  prime into the completed field);
* lineBundle is the concrete completion-localized trivial line bundle over the
  q-pilot base field I.initial.arithmetic.Fmod: sections are the base field,
  localizations are the actual completion embeddings k ->+* K_v;
* logKummer is the actual self Kummer arrow on the q-pilot strip
  (selfKummerArrow, whose actions are the supplied kappa-orbit units actions of
  the strip, not an invented trivial action);
* qPilotLogVolume is the actual source scalar candidate
  sourceQPilotSignedLog I.initial = -sum_b |log q_b| over the actual bad
  q-parameters.

## The four paper_*_identification fields

In PaperQPilotObject these are opaque Prop placeholders.  Here they are
replaced by **concrete propositions about the actual strip, line bundle,
log-Kummer arrow and q-pilot scalar, and proved as fields of the object**:

1. OrigXiFPaperStripIdentified boundary strip:
   strip = boundary.theater.primeStrip and boundary.target_q =
   boundary.theater.thetaPacket.q.  This is the actual strip anchor together
   with the boundary's theta-q agreement (target_q_eq_source), not the paper's
   F^boxplus-triangleright-x-mu-prime-strip identification.
2. OrigXiFPaperLineBundleIdentified L: the carrier is exactly the
   completion-localized trivial bundle over the q-pilot base field, and its
   localizations are injective (algebraMap_completion_injective).  This is the
   concrete rank-one carrier; it does not assert that the sections are the
   fractional-ideal sections of the paper's O(-D).
3. OrigXiFPaperLogKummerIdentified K: the x-mu layer of the actual arrow
   satisfies the IUT II Definition 4.9(i) invariant-image law at every place
   and open subgroup, and its strip representative preserves degrees.  This is
   the actual Kummer content of the reduced arrow; it does not assert the full
   paper log-Kummer correspondence.
4. OrigXiFPaperQPilotScalarIdentified S x: x = -OrigXiFPaperBadQAbsLog S and
   x <= 0, i.e. the object scalar is the actual bad-place absolute-log sum.
   The strict inequality under a nonempty bad set is proved separately.  This
   is *not* the open comparison -sum_b |log q_b| = -|log ||C3.q.q|||, which is
   recorded elsewhere (OrigXiFPaperQPilotScalarActual) as the exact first field
   and is not fabricated here.

No True, Nonempty, empty inductive, arbitrary inhabitant, axiom or sorry is
used for any of the four identifications.

## Bridge to the frozen PaperQPilotObject

OrigXiFPaperQPilotObject.toPaperQPilotObject maps the actual object to the
frozen structure with the four Prop fields *instantiated by the concrete
propositions above*, and toPaperQPilotObject_paper_* prove that those
instantiations hold.  Thus the placeholders are no longer opaque: they are
concrete propositions, and they are true of the constructed object.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.OrigXiF

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperLineBundleCarrierActual

universe ua uv upi umon ui uG uL uC u

/-! ## 1. Concrete identification propositions -/

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

/-- The concrete completion-localized trivial line bundle over the q-pilot base
field: sections are the base field, localizations are the actual completion
embeddings into the completed fields. -/
def OrigXiFPaperCompletionLineBundleCarrier (k : Type u) [Field k]
    [NumberField k] : PaperLineBundleCarrier k where
  total := k
  localization := fun v => algebraMap k (Completion v)

/-- Concrete line-bundle identification: the carrier is the completion-localized
trivial bundle over the q-pilot base field, and its localizations are injective
at every finite place. -/
def OrigXiFPaperLineBundleIdentified {k : Type u} [Field k] [NumberField k]
    (L : PaperLineBundleCarrier k) : Prop :=
  L = OrigXiFPaperCompletionLineBundleCarrier k ∧
    ∀ v : NumberField.FinitePlace k, Function.Injective (L.localization v)

/-- The completion embedding is injective (source theorem
algebraMap_completion_injective). -/
theorem OrigXiFPaperCompletionLineBundleCarrier_injective {k : Type u}
    [Field k] [NumberField k] (v : NumberField.FinitePlace k) :
    Function.Injective
      ((OrigXiFPaperCompletionLineBundleCarrier k).localization v) :=
  NumberFieldFinitePlace.algebraMap_completion_injective v

/-- The concrete carrier satisfies the concrete line-bundle identification. -/
theorem OrigXiFPaperCompletionLineBundleCarrier_identified {k : Type u}
    [Field k] [NumberField k] :
    OrigXiFPaperLineBundleIdentified
      (OrigXiFPaperCompletionLineBundleCarrier k) :=
  ⟨rfl, fun v =>
    OrigXiFPaperCompletionLineBundleCarrier_injective v⟩

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

/-! ## 2. The actual object structure with proved identification fields -/

/-- The O-layer actual paper q-pilot object.  Same data surface as the frozen
PaperQPilotObject, but the four paper_*_identification fields are concrete
propositions *carried with their proofs*. -/
structure OrigXiFPaperQPilotObject
    {l : PrimeGeFive} {V : Type uv}
    {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (G : Type uG) [Group G] [TopologicalSpace G]
    (envStrip : FPrimeStrip V) where
  /-- The actual source input boundary. -/
  boundary : SourceProcessionBoundary.Input.{ua, uv, upi, umon, uL, uC}
    (l := l) (V := V) (Label := Label) (Choice := Choice)
  /-- The actual q-pilot F-prime-strip anchor. -/
  strip : FPrimeStrip V
  strip_eq_source : strip = sourceQPilotStrip boundary
  /-- Card AS: the actual one-column arithmetic holomorphic structure. -/
  oneColumn : SourceOneColumnArithmeticHolomorphicStructure V
  /-- Card AV: the completion-localized line-bundle carrier over the q-pilot
  base field. -/
  lineBundle : PaperLineBundleCarrier (k := I.initial.arithmetic.Fmod)
  /-- The actual reduced Kummer arrow. -/
  logKummer : SourceKummerArrow G envStrip strip
  /-- The actual source q-pilot scalar candidate. -/
  qPilotLogVolume : Real
  qPilotLogVolume_eq : qPilotLogVolume = sourceQPilotSignedLog I.initial
  /-- Concrete strip identification (proved). -/
  paper_strip_identification : OrigXiFPaperStripIdentified boundary strip
  /-- Concrete line-bundle identification (proved). -/
  paper_lineBundle_identification : OrigXiFPaperLineBundleIdentified lineBundle
  /-- Concrete log-Kummer identification (proved). -/
  paper_logKummer_identification : OrigXiFPaperLogKummerIdentified logKummer
  /-- Concrete q-pilot scalar identification (proved). -/
  paper_qPilot_log_identification :
    OrigXiFPaperQPilotScalarIdentified I.initial qPilotLogVolume

namespace OrigXiFPaperQPilotObject

variable {V : Type uv} {l : PrimeGeFive} {Label : Type uL} {Choice : Type uC}
  [AddGroup Label] [Preorder Choice]
  {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
  {G : Type uG} [Group G] [TopologicalSpace G]
  {envStrip : FPrimeStrip V}

/-- The strip is the source q-pilot strip anchor. -/
theorem strip_eq (O : OrigXiFPaperQPilotObject
    (Label := Label) (Choice := Choice) I G envStrip) :
    O.strip = sourceQPilotStrip O.boundary := O.strip_eq_source

/-- The q-pilot log-volume is the negated actual bad-place absolute-log sum. -/
theorem qPilotLogVolume_eq_neg_abs_sum (O : OrigXiFPaperQPilotObject
    (Label := Label) (Choice := Choice) I G envStrip) :
    O.qPilotLogVolume = -OrigXiFPaperBadQAbsLog I.initial := by
  rw [O.qPilotLogVolume_eq]
  exact sourceQPilotSignedLog_eq_neg_badQAbsLog I.initial

/-- The q-pilot log-volume is nonpositive. -/
theorem qPilotLogVolume_nonpos (O : OrigXiFPaperQPilotObject
    (Label := Label) (Choice := Choice) I G envStrip) :
    O.qPilotLogVolume ≤ 0 :=
  O.paper_qPilot_log_identification.2

/-- The q-pilot log-volume is strictly negative when the bad set is nonempty. -/
theorem qPilotLogVolume_neg_of_bad_nonempty (O : OrigXiFPaperQPilotObject
    (Label := Label) (Choice := Choice) I G envStrip)
    (hbad : Nonempty I.initial.badPlaces) : O.qPilotLogVolume < 0 := by
  rw [O.qPilotLogVolume_eq]
  exact sourceQPilotSignedLog_neg_of_nonempty I.initial hbad

/-- Map the actual object to the frozen PaperQPilotObject, instantiating the
four opaque Prop fields by the concrete propositions of this file. -/
noncomputable def toPaperQPilotObject (O : OrigXiFPaperQPilotObject
    (Label := Label) (Choice := Choice) I G envStrip) :
    PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip where
  boundary := O.boundary
  strip := O.strip
  strip_eq_source := O.strip_eq_source
  oneColumn := O.oneColumn
  lineBundle := O.lineBundle
  logKummer := O.logKummer
  qPilotLogVolume := O.qPilotLogVolume
  qPilotLogVolume_eq := O.qPilotLogVolume_eq
  paper_strip_identification :=
    OrigXiFPaperStripIdentified O.boundary O.strip
  paper_lineBundle_identification :=
    OrigXiFPaperLineBundleIdentified O.lineBundle
  paper_logKummer_identification :=
    OrigXiFPaperLogKummerIdentified O.logKummer
  paper_qPilot_log_identification :=
    OrigXiFPaperQPilotScalarIdentified I.initial O.qPilotLogVolume

/-- The frozen object's strip placeholder is now the concrete strip proposition,
and it holds. -/
theorem toPaperQPilotObject_paper_strip (O : OrigXiFPaperQPilotObject
    (Label := Label) (Choice := Choice) I G envStrip) :
    O.toPaperQPilotObject.paper_strip_identification :=
  O.paper_strip_identification

/-- The frozen object's line-bundle placeholder is now the concrete line-bundle
proposition, and it holds. -/
theorem toPaperQPilotObject_paper_lineBundle (O : OrigXiFPaperQPilotObject
    (Label := Label) (Choice := Choice) I G envStrip) :
    O.toPaperQPilotObject.paper_lineBundle_identification :=
  O.paper_lineBundle_identification

/-- The frozen object's log-Kummer placeholder is now the concrete log-Kummer
proposition, and it holds. -/
theorem toPaperQPilotObject_paper_logKummer (O : OrigXiFPaperQPilotObject
    (Label := Label) (Choice := Choice) I G envStrip) :
    O.toPaperQPilotObject.paper_logKummer_identification :=
  O.paper_logKummer_identification

/-- The frozen object's q-pilot scalar placeholder is now the concrete scalar
proposition, and it holds. -/
theorem toPaperQPilotObject_paper_qPilot_log (O : OrigXiFPaperQPilotObject
    (Label := Label) (Choice := Choice) I G envStrip) :
    O.toPaperQPilotObject.paper_qPilot_log_identification :=
  O.paper_qPilot_log_identification

end OrigXiFPaperQPilotObject

/-! ## 3. The actual concrete object -/

namespace OrigXiFPaperQPilotObjectActual

open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual
open LeanFormal.IUT.Theorem311Source.IPLAPTDataActual

/-- Actual paper preorder on procession choices: the upper semi-level
progression Ind3Step of the concrete finite model.  This is the source
upper-procession order, not the former le := True placeholder. -/
instance origXiFPaperProcessionPreorder (l : PrimeGeFive) :
    Preorder (ConcreteFiniteTheorem311.ProcessionChoice l) where
  le a b := ConcreteFiniteTheorem311.ProcessionChoice.Ind3Step a b
  lt a b := ConcreteFiniteTheorem311.ProcessionChoice.Ind3Step a b ∧
    ¬ ConcreteFiniteTheorem311.ProcessionChoice.Ind3Step b a
  le_refl a := ConcreteFiniteTheorem311.ProcessionChoice.ind3Step_refl a
  le_trans := fun _ _ _ h1 h2 =>
    ConcreteFiniteTheorem311.ProcessionChoice.ind3Step_trans h1 h2
  lt_iff_le_not_ge := fun _ _ => Iff.rfl

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

variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))

/-- **The actual paper q-pilot object** (O layer), with the four concrete
identifications proved. -/
noncomputable def origXiFPaperQPilotObjectActual :
    OrigXiFPaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      I (OrigXiFPaperSourceKummerGroup l)
      (OrigXiFPaperSourceStrip l) where
  boundary := OrigXiFPaperSourceBoundary l
  strip := OrigXiFPaperSourceStrip l
  strip_eq_source := rfl
  oneColumn := actualOneColumnFinitePrimePlace
  lineBundle := OrigXiFPaperCompletionLineBundleCarrier I.initial.arithmetic.Fmod
  logKummer := OrigXiFPaperSourceKummerArrow l
  qPilotLogVolume := sourceQPilotSignedLog I.initial
  qPilotLogVolume_eq := rfl
  paper_strip_identification :=
    ⟨rfl, (OrigXiFPaperSourceBoundary l).target_q_eq_source⟩
  paper_lineBundle_identification :=
    OrigXiFPaperCompletionLineBundleCarrier_identified
  paper_logKummer_identification :=
    OrigXiFPaperLogKummerIdentified_of_arrow
      (OrigXiFPaperSourceKummerArrow l)
  paper_qPilot_log_identification :=
    ⟨sourceQPilotSignedLog_eq_neg_badQAbsLog I.initial,
      sourceQPilotSignedLog_nonpos I.initial⟩

/-- The constructed object's strip identification holds. -/
theorem origXiFPaperQPilotObjectActual_paper_strip :
    OrigXiFPaperStripIdentified (origXiFPaperQPilotObjectActual I).boundary
      (origXiFPaperQPilotObjectActual I).strip :=
  (origXiFPaperQPilotObjectActual I).paper_strip_identification

/-- The constructed object's line-bundle identification holds. -/
theorem origXiFPaperQPilotObjectActual_paper_lineBundle :
    OrigXiFPaperLineBundleIdentified
      (origXiFPaperQPilotObjectActual I).lineBundle :=
  (origXiFPaperQPilotObjectActual I).paper_lineBundle_identification

/-- The constructed object's log-Kummer identification holds. -/
theorem origXiFPaperQPilotObjectActual_paper_logKummer :
    OrigXiFPaperLogKummerIdentified
      (origXiFPaperQPilotObjectActual I).logKummer :=
  (origXiFPaperQPilotObjectActual I).paper_logKummer_identification

/-- The constructed object's q-pilot scalar identification holds. -/
theorem origXiFPaperQPilotObjectActual_paper_qPilot_log :
    OrigXiFPaperQPilotScalarIdentified I.initial
      (origXiFPaperQPilotObjectActual I).qPilotLogVolume :=
  (origXiFPaperQPilotObjectActual I).paper_qPilot_log_identification

/-- The constructed object's q-pilot log-volume is the negated actual bad-place
absolute-log sum. -/
theorem origXiFPaperQPilotObjectActual_qPilotLogVolume :
    (origXiFPaperQPilotObjectActual I).qPilotLogVolume =
      -OrigXiFPaperBadQAbsLog I.initial :=
  OrigXiFPaperQPilotObject.qPilotLogVolume_eq_neg_abs_sum _

/-- The constructed object's q-pilot log-volume is nonpositive. -/
theorem origXiFPaperQPilotObjectActual_qPilotLogVolume_nonpos :
    (origXiFPaperQPilotObjectActual I).qPilotLogVolume ≤ 0 :=
  OrigXiFPaperQPilotObject.qPilotLogVolume_nonpos _

/-- The constructed object's q-pilot log-volume is strictly negative when the
bad set is nonempty. -/
theorem origXiFPaperQPilotObjectActual_qPilotLogVolume_neg
    (hbad : Nonempty I.initial.badPlaces) :
    (origXiFPaperQPilotObjectActual I).qPilotLogVolume < 0 :=
  OrigXiFPaperQPilotObject.qPilotLogVolume_neg_of_bad_nonempty _ hbad

/-- The frozen PaperQPilotObject built from the actual object, with concrete
(proved) identification fields. -/
noncomputable def origXiFPaperQPilotObjectActualFrozen :
    PaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      I (OrigXiFPaperSourceKummerGroup l)
      (OrigXiFPaperSourceStrip l) :=
  (origXiFPaperQPilotObjectActual I).toPaperQPilotObject

/-- The frozen object's four paper identification fields are concrete
propositions and hold. -/
theorem origXiFPaperQPilotObjectActualFrozen_identifications :
    (origXiFPaperQPilotObjectActualFrozen I).paper_strip_identification ∧
    (origXiFPaperQPilotObjectActualFrozen I).paper_lineBundle_identification ∧
    (origXiFPaperQPilotObjectActualFrozen I).paper_logKummer_identification ∧
    (origXiFPaperQPilotObjectActualFrozen I).paper_qPilot_log_identification :=
  ⟨(origXiFPaperQPilotObjectActual I).paper_strip_identification,
    (origXiFPaperQPilotObjectActual I).paper_lineBundle_identification,
    (origXiFPaperQPilotObjectActual I).paper_logKummer_identification,
    (origXiFPaperQPilotObjectActual I).paper_qPilot_log_identification⟩

end OrigXiFPaperQPilotObjectActual

/-! ## 4. Axiom audit -/

#print axioms OrigXiFPaperCompletionLineBundleCarrier_identified
#print axioms OrigXiFPaperLogKummerIdentified_of_arrow
#print axioms OrigXiFPaperStripIdentified_anchor
#print axioms OrigXiFPaperQPilotObject.toPaperQPilotObject_paper_strip
#print axioms OrigXiFPaperQPilotObjectActual.origXiFPaperQPilotObjectActual
#print axioms OrigXiFPaperQPilotObjectActual.origXiFPaperQPilotObjectActualFrozen_identifications

end LeanFormal.IUT.XiFPaper.OrigXiF

end
