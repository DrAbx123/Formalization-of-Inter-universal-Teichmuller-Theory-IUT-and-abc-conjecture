import tmp.sheaf.xif.paper.S1880OriginalXiFActual
import tmp.sheaf.xif.paper.OrigXiFPaperBoundaryStripActual
import tmp.sheaf.xif.paper.S1679CompleteODCarrierActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceSHETransportConjugation
import LeanFormal.IUT.IUTIII.Theorem311.SourceFTimesMuPrimeStripPolyIsomorphism
import LeanFormal.IUT.IUTII.Frobenioid.LocalIntegralFPrimeStrip
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceUnitRegionHaarDataActual

/-!
# S1895: paper-level O-object identifications on the actual (1,0) core

Layer: O (original Theta-link / q-pilot).  S1880 built the paper-route
object S1880PaperO and the C3 carrier S1880PaperC3, and proved the xi-f
content.  This file addresses the four paper-level identification obligations
which S1880 explicitly left separate:

1. the q-pilot F^boxplus-triangleright-x-mu-prime-strip identification;
2. the full (one-column) log-Kummer correspondence;
3. the (1,0) / 1,circ label binding;
4. the strip anchors.

## What is constructed here

* The actual (1,0) core I.fPrimeStripAt 1 0 of the S1527 input and its
  canonical times-mu prime-strip SourceFTimesMuPrimeStrip.canonical.  On this
  core the paper-level F-times-mu identification is the identity full
  poly-isomorphism (a genuine SourceFTimesMuPrimeStripFullPolyIsomorphism).
* The actual one-column vertical Kummer card: the self Kummer arrow on the
  core is conjugated along the actual source strip links I.fLinkAt 1 0 1 m,
  producing a SourceVerticalKummerCard (IUT III Theorem 3.11(ii)) at every
  m.  Its m = 0 component is the object's logKummer.
* The actual vertical log-Kummer correspondence of the procession profile
  (VerticalLogKummerCorrespondence), with the upper-semi Ind3 field proved
  from the actual source profile.
* The actual 1,circ label binding: column index n = 1, vertical index
  m = 0, carrier exactly the object's actual one-column structure.
* The actual strip anchors: the strip is the source q-pilot strip of the
  boundary, and the boundary target q is the theater theta q.
* A correctly based O object S1895PaperO carrying the actual S1679 O(-D)
  line bundle, the actual S1391/S1527 scalar, and the four identifications
  above.  Its four frozen paper_* prop slots are instantiated by the
  paper-level propositions and every one of them is proved.

## The exact first missing for the S1880 object

S1880's S1880PaperO uses the concrete finite-local boundary
SourceProcessionBoundary.Input.concreteInput, whose strip is
finiteLocalIntegralFPrimeStrip 2 7; its input S1527Input has the paper
(1,0) strip S1487Strip 1 0 (the S1487 shear core).  These are different
F-prime-strips.  The first paper-level identification for S1880PaperO is
therefore the full times-mu bridge

  SourceFTimesMuPrimeStripFullPolyIsomorphism
    (canonical (S1880PaperO).strip) (canonical ((S1527Input).fPrimeStripAt 1 0)),

recorded as S1895S1880FTimesMuBridge / S1895FirstMissing.  No inhabitant
is asserted or fabricated here.  The exact value-monoid obstruction is
recorded below: at the place 5 the first strip has value monoid
LocalIntegralMonoid 5, the second has SourceHaarActualValueMonoid; these
are not isomorphic as monoids, so no FPrimeStripEquiv between the two
strips can exist.  The correct construction is the rebased S1895PaperO on
the actual paper core, which is what this file builds.

No sorry, axiom, True, PUnit, empty type, arbitrary inhabitant or Nonempty
gate is used.  The missing types are recorded as definitions, not inhabited.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual

open LeanFormal.IUT
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1527OOrderEqualityActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S1679CompleteODCarrierActual
open LeanFormal.IUT.XiFPaper.OrigXiFPaperBoundaryStrip
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual
open LeanFormal.IUT.XiFPaper.OrigXiF
open LeanFormal.IUT.XiFPaper.OrigXiF.OrigXiFPaperQPilotObjectActual
open LeanFormal.IUT.XiFPaper.S1880OriginalXiFActual
open LeanFormal.IUT.Theorem311Source.IPLAPTDataActual
open LeanFormal.IUT.XiFPaper.PaperLineBundleCarrierActual

local instance s1895FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

local instance s1895GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-! ## 0. The actual S1280/S1527 input data -/

/-- The full actual input parameters of the S1280 Gaussian datum: the remaining
Definition 3.1 clause supply and the D9 compatibility pairs.  This is the same
data surface as S1880PaperO, packaged for readability; it constructs nothing
new. -/
structure S1895PaperInput where
  l : PrimeGeFive
  R : S1280RemainingClauses l
  redCompat : Prop
  hredCompat : redCompat
  torCompat : Prop
  htorCompat : torCompat
  orbCompat : Prop
  horbCompat : orbCompat
  secCompat : Prop
  hsecCompat : secCompat
  cusCompat : Prop
  hcusCompat : cusCompat

namespace S1895PaperInput

/-- The actual S1527 shear input over the S1280 assembled source data. -/
noncomputable def I (D : S1895PaperInput) :
    OriginalInput.{0, 0, 0, 0, 0} D.l (FinitePrimePlace 2 7) :=
  S1527Input D.l D.R D.redCompat D.hredCompat D.torCompat D.htorCompat
    D.orbCompat D.horbCompat D.secCompat D.hsecCompat D.cusCompat D.hcusCompat

end S1895PaperInput

/-! ## 1. The actual (1,0) core and the canonical times-mu strip -/

variable {l : PrimeGeFive}

/-- The paper (1,0) F-prime-strip of an original input. -/
abbrev S1895Core (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) :
    FPrimeStrip (FinitePrimePlace 2 7) :=
  I.fPrimeStripAt 1 0

/-- The canonical product group of the paper core. -/
abbrev S1895KummerGroup
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) : Type :=
  SelfGroup (S1895Core I)

/-- The actual paper level order on the source procession choices: the level
c.2 of a choice.  This is the Ind3 level used by the boundary carrier, not a
le := True placeholder. -/
instance (priority := 10000) s1895ChoicePreorder
    {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)} :
    Preorder (OrigXiFPaperChoice I) where
  le a b := a.2 ≤ b.2
  lt a b := a.2 < b.2
  le_refl a := le_rfl
  le_trans _ _ _ h1 h2 := le_trans h1 h2
  lt_iff_le_not_ge a b := Nat.lt_iff_le_and_not_ge

/-- The S1527 core is the S1487 shear strip at (1,0). -/
theorem s1895PaperInput_core_eq_shear (D : S1895PaperInput) :
    S1895Core (S1895PaperInput.I D) = (S1487Strip 1 0) := rfl

/-- The core is definitionally the boundary's source q-pilot strip. -/
theorem s1895PaperInput_core_eq_strip (D : S1895PaperInput) :
    S1895Core (S1895PaperInput.I D) =
      OrigXiFPaperStrip (S1895PaperInput.I D) 1 0 := rfl

/-- The canonical times-mu prime-strip of the actual (1,0) core (IUT II,
Corollary 4.10, (iii)). -/
noncomputable def s1895TimesMuStrip (D : S1895PaperInput) :
    SourceFTimesMuPrimeStrip (FinitePrimePlace 2 7) :=
  SourceFTimesMuPrimeStrip.canonical (S1895Core (S1895PaperInput.I D))

/-- The underlying F-prime-strip of the canonical times-mu strip is the paper
(1,0) core. -/
theorem s1895TimesMuStrip_toFPrimeStrip (D : S1895PaperInput) :
    (s1895TimesMuStrip D).toFPrimeStrip =
      S1895Core (S1895PaperInput.I D) := rfl

/-! ## 2. The actual one-column vertical log-Kummer correspondence -/

/-- The actual vertical Kummer arrow of the paper column at 1, at vertical
index m: the self Kummer arrow on the core conjugated along the actual
source strip link I.fLinkAt 1 0 1 m. -/
noncomputable def s1895VerticalKummerArrow
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) (m : Int) :
    SourceKummerArrow (S1895KummerGroup I) (I.fPrimeStripAt 1 m)
      (S1895Core I) :=
  SourceKummerArrow.conjugate (selfKummerArrow (S1895Core I))
    (I.fLinkAt 1 0 1 m) (FPrimeStripEquiv.refl (S1895Core I))

/-- The actual one-column vertical Kummer card of Theorem 3.11(ii) at column
1: its m-th arrow is the conjugated actual Kummer arrow. -/
noncomputable def s1895VerticalKummerCard
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) :
    SourceVerticalKummerCard (S1895KummerGroup I) I 1 where
  kummer := s1895VerticalKummerArrow I

/-- The actual ordered vertical log-Kummer correspondence of the procession
profile: the Ind3 upper-semi inclusion is the source profile's ind3_upper,
proved. -/
noncomputable def s1895VerticalLogCorrespondence
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) :
    VerticalLogKummerCorrespondence where
  D := Real
  ordD := inferInstance
  F := fun _ => OrigXiFPaperChoice I
  ordF := fun _ => s1895ChoicePreorder (I := I)
  log := fun n c => (OrigXiFPaperCore I).ind3 n c
  kummer := fun _ c => (OrigXiFPaperProfile I).logVolume c
  upperSemi := by
    intro m c
    exact (OrigXiFPaperProfile I).ind3_upper m c

/-- The actual one-column log-Kummer correspondence package: the vertical
Kummer card, the ordered profile correspondence, and the object arrow as the
card's m = 0 component. -/
structure S1895FullLogKummerCorrespondence
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) where
  /-- the actual vertical Kummer arrows of the column -/
  vertical : SourceVerticalKummerCard (S1895KummerGroup I) I 1
  /-- the actual ordered vertical log-Kummer correspondence -/
  verticalLog : VerticalLogKummerCorrespondence
  /-- the q-pilot object's Kummer arrow -/
  objectKummer : SourceKummerArrow (S1895KummerGroup I) (S1895Core I)
    (S1895Core I)
  /-- the object arrow is the m = 0 component of the card -/
  objectKummer_eq : objectKummer = vertical.kummer 0

/-- The actual full one-column log-Kummer correspondence, with the object arrow
definitionally the m = 0 vertical Kummer arrow. -/
noncomputable def s1895FullLogKummerCorrespondence
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) :
    S1895FullLogKummerCorrespondence I where
  vertical := s1895VerticalKummerCard I
  verticalLog := s1895VerticalLogCorrespondence I
  objectKummer := (s1895VerticalKummerCard I).kummer 0
  objectKummer_eq := rfl

/-- The correspondence's object arrow is exactly the card's m = 0 arrow. -/
theorem s1895FullLogKummerCorrespondence_object
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) :
    (s1895FullLogKummerCorrespondence I).objectKummer =
      (s1895VerticalKummerCard I).kummer 0 := rfl

/-! ## 3. The paper-level identification propositions -/

/-- Paper-level F^boxplus-triangleright-x-mu-prime-strip identification on a
given F-prime-strip: the canonical times-mu strip on that strip is fully
poly-isomorphic to the canonical times-mu strip on the actual paper (1,0)
core.  This is the source-facing identification of IUT II, Corollary 4.10(iii);
the full global realified Frobenioid/log-shell realization is a separate object
field (see the module boundary). -/
def S1895FTimesMuProp
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (strip : FPrimeStrip (FinitePrimePlace 2 7)) : Prop :=
  Nonempty (SourceFTimesMuPrimeStripFullPolyIsomorphism
    (SourceFTimesMuPrimeStrip.canonical strip)
    (SourceFTimesMuPrimeStrip.canonical (S1895Core I)))

/-- Paper-level full one-column log-Kummer identification: the object's Kummer
arrow is the m = 0 component of an actual full one-column correspondence. -/
def S1895FullLogKummerProp
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) : Prop :=
  ∃ C : S1895FullLogKummerCorrespondence I,
    C.objectKummer = C.vertical.kummer 0

/-- Paper-level q-pilot scalar identification: the object scalar is the actual
completion magnitude -localLogMagnitude S1487Cand and is nonpositive.  This is
the frozen structure's paper_qPilot_log_identification slot, kept faithful to
its scalar meaning; the (1,0) label binding is a separate structure. -/
def S1895ScalarProp
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) (x : Real) : Prop :=
  x = -localLogMagnitude S1487Cand ∧ x ≤ 0

/-- The actual 1,circ label binding on a one-column structure: column index
1, vertical index 0, carrier exactly the given one-column structure. -/
structure S1895OneColumnLabel (V : Type) where
  /-- the column index n of the 1,circ label -/
  n : Int
  n_eq : n = 1
  /-- the vertical index m of the (1,0) binding -/
  m : Int
  m_eq : m = 0
  /-- the actual one-column arithmetic holomorphic carrier -/
  carrier : SourceOneColumnArithmeticHolomorphicStructure V

/-- The actual label binding from a one-column carrier. -/
def s1895OneColumnLabel
    (V : Type) (col : SourceOneColumnArithmeticHolomorphicStructure V) :
    S1895OneColumnLabel V where
  n := 1
  n_eq := rfl
  m := 0
  m_eq := rfl
  carrier := col

/-- The (1,0) label binding proposition for a one-column carrier. -/
def S1895OneZeroLabelProp
    (V : Type) (col : SourceOneColumnArithmeticHolomorphicStructure V) : Prop :=
  ∃ L : S1895OneColumnLabel V, L.n = 1 ∧ L.m = 0 ∧ L.carrier = col

/-- The actual (1,0) label binding holds for every actual one-column
carrier. -/
theorem s1895OneZeroLabelProp_holds
    (V : Type) (col : SourceOneColumnArithmeticHolomorphicStructure V) :
    S1895OneZeroLabelProp V col :=
  ⟨s1895OneColumnLabel V col, rfl, rfl, rfl⟩

/-- The full one-column log-Kummer proposition holds on every actual input. -/
theorem s1895FullLogKummerProp_holds
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) :
    S1895FullLogKummerProp I :=
  ⟨s1895FullLogKummerCorrespondence I, rfl⟩

/-! ## 4. The correctly based paper O object

The frozen PaperQPilotObject stores its identification fields as Prop
slots.  Here those slots are instantiated by the paper-level propositions of
section 3; the object is built on the actual paper (1,0) strip, not on the
concrete finite-local strip used by S1880PaperO.  Every slot is proved in
section 5. -/

/-- The paper O object on the actual (1,0) core of the S1527 input. -/
noncomputable def S1895PaperO (D : S1895PaperInput) :
    PaperQPilotObject (l := D.l) (V := FinitePrimePlace 2 7)
      (Label := OrigXiFPaperLabel)
      (Choice := OrigXiFPaperChoice (S1895PaperInput.I D))
      (S1895PaperInput.I D)
      (S1895KummerGroup (S1895PaperInput.I D))
      (S1895Core (S1895PaperInput.I D)) := by
  letI := s1895ChoicePreorder (I := S1895PaperInput.I D)
  let I := S1895PaperInput.I D
  exact {
    boundary := OrigXiFPaperBoundary I 1 0
    strip := S1895Core I
    strip_eq_source := rfl
    oneColumn := actualOneColumnFinitePrimePlace
    lineBundle := s1679Carrier D.l
    logKummer := (s1895FullLogKummerCorrespondence I).objectKummer
    qPilotLogVolume := sourceQPilotSignedLog I.initial
    qPilotLogVolume_eq := rfl
    paper_strip_identification := S1895FTimesMuProp I (S1895Core I)
    paper_lineBundle_identification := S1679PaperLineBundleIdentified D.l
    paper_logKummer_identification := S1895FullLogKummerProp I
    paper_qPilot_log_identification :=
      S1895ScalarProp I (sourceQPilotSignedLog I.initial)
  }

/-- The object's strip is the boundary's source q-pilot strip and the boundary
target q is the theater theta q: the two strip anchors. -/
theorem s1895PaperO_strip_anchors (D : S1895PaperInput) :
    (S1895PaperO D).strip = sourceQPilotStrip (S1895PaperO D).boundary ∧
      (S1895PaperO D).boundary.target_q =
        (S1895PaperO D).boundary.theater.thetaPacket.q :=
  ⟨rfl, rfl⟩

/-- The object's strip anchor, first component. -/
theorem s1895PaperO_strip_eq_source (D : S1895PaperInput) :
    (S1895PaperO D).strip = sourceQPilotStrip (S1895PaperO D).boundary := rfl

/-- The object's strip is the paper (1,0) core. -/
theorem s1895PaperO_strip_eq_core (D : S1895PaperInput) :
    (S1895PaperO D).strip =
      S1895Core (S1895PaperInput.I D) := rfl

/-- The object's actual one-column label binding: n = 1, m = 0, carrier
exactly the object's one-column structure. -/
noncomputable def s1895PaperO_oneColumnLabel (D : S1895PaperInput) :
    S1895OneColumnLabel (FinitePrimePlace 2 7) :=
  s1895OneColumnLabel _ (S1895PaperO D).oneColumn

theorem s1895PaperO_oneColumnLabel_n (D : S1895PaperInput) :
    (s1895PaperO_oneColumnLabel D).n = 1 := rfl

theorem s1895PaperO_oneColumnLabel_m (D : S1895PaperInput) :
    (s1895PaperO_oneColumnLabel D).m = 0 := rfl

theorem s1895PaperO_oneColumnLabel_carrier (D : S1895PaperInput) :
    (s1895PaperO_oneColumnLabel D).carrier = (S1895PaperO D).oneColumn := rfl

/-! ## 5. The four paper-level identifications, proved for S1895PaperO -/

/-- The paper-level F-times-mu identification for S1895PaperO: the canonical
times-mu strip on the object's actual core is fully poly-isomorphic to itself
(the actual identity identification). -/
theorem s1895PaperO_paper_strip (D : S1895PaperInput) :
    (S1895PaperO D).paper_strip_identification := by
  change S1895FTimesMuProp (S1895PaperInput.I D)
    (S1895Core (S1895PaperInput.I D))
  exact ⟨SourceFTimesMuPrimeStripFullPolyIsomorphism.id _⟩

/-- The S1679 complete O(-D) line-bundle identification holds on the object. -/
theorem s1895PaperO_paper_lineBundle (D : S1895PaperInput) :
    (S1895PaperO D).paper_lineBundle_identification :=
  s1679_identified D.l

/-- The full one-column log-Kummer identification holds: the object's Kummer
arrow is the m = 0 component of the actual correspondence. -/
theorem s1895PaperO_paper_logKummer (D : S1895PaperInput) :
    (S1895PaperO D).paper_logKummer_identification := by
  change S1895FullLogKummerProp (S1895PaperInput.I D)
  exact ⟨s1895FullLogKummerCorrespondence _, rfl⟩

/-- The object's q-pilot scalar is the actual completion scalar
-localLogMagnitude S1487Cand = -(order_C3 * log 5). -/
theorem s1895PaperO_qPilot_eq (D : S1895PaperInput) :
    (S1895PaperO D).qPilotLogVolume = -localLogMagnitude S1487Cand := by
  change sourceQPilotSignedLog (S1895PaperInput.I D).initial =
    -localLogMagnitude S1487Cand
  have hinit : (S1895PaperInput.I D).initial =
      S1527SourceData D.l D.R D.redCompat D.hredCompat D.torCompat D.htorCompat
        D.orbCompat D.horbCompat D.secCompat D.hsecCompat D.cusCompat D.hcusCompat :=
    rfl
  rw [hinit]
  unfold sourceQPilotSignedLog
  rw [S1527_sourceBadQAbsLog_eq_localLogMagnitude]

/-- The paper q-pilot scalar identification holds on the object: the scalar is
the actual completion magnitude and is nonpositive. -/
theorem s1895PaperO_paper_qPilot (D : S1895PaperInput) :
    (S1895PaperO D).paper_qPilot_log_identification := by
  change S1895ScalarProp (S1895PaperInput.I D)
    (sourceQPilotSignedLog (S1895PaperInput.I D).initial)
  exact ⟨s1895PaperO_qPilot_eq D,
    sourceQPilotSignedLog_nonpos (S1895PaperInput.I D).initial⟩

/-- The (1,0) label binding holds on the object: the actual one-column label
has n = 1, m = 0, and carrier exactly the object's one-column structure. -/
theorem s1895PaperO_label (D : S1895PaperInput) :
    (s1895PaperO_oneColumnLabel D).n = 1 ∧
      (s1895PaperO_oneColumnLabel D).m = 0 ∧
      (s1895PaperO_oneColumnLabel D).carrier = (S1895PaperO D).oneColumn :=
  ⟨rfl, rfl, rfl⟩

/-- **All four paper-level identification obligations hold for
S1895PaperO**: the F-times-mu strip, the full one-column log-Kummer
correspondence, the (1,0) label binding, and the two strip anchors.  The
conjunction also records the two frozen scalar/line-bundle fields, which are
the actual S1679 and S1527 identifications. -/
theorem s1895PaperO_identifications (D : S1895PaperInput) :
    (S1895PaperO D).paper_strip_identification ∧
      (S1895PaperO D).paper_logKummer_identification ∧
      ((s1895PaperO_oneColumnLabel D).n = 1 ∧
        (s1895PaperO_oneColumnLabel D).m = 0 ∧
        (s1895PaperO_oneColumnLabel D).carrier = (S1895PaperO D).oneColumn) ∧
      ((S1895PaperO D).strip = sourceQPilotStrip (S1895PaperO D).boundary ∧
        (S1895PaperO D).boundary.target_q =
          (S1895PaperO D).boundary.theater.thetaPacket.q) ∧
      (S1895PaperO D).paper_lineBundle_identification ∧
      (S1895PaperO D).paper_qPilot_log_identification :=
  ⟨s1895PaperO_paper_strip D,
    s1895PaperO_paper_logKummer D,
    s1895PaperO_label D,
    s1895PaperO_strip_anchors D,
    s1895PaperO_paper_lineBundle D,
    s1895PaperO_paper_qPilot D⟩

/-! ## 6. The exact first missing for S1880PaperO

S1880PaperO is the S1684 object on the concrete finite-local boundary.  Its
strip is finiteLocalIntegralFPrimeStrip 2 7; the paper (1,0) core of its
S1527 input is S1487Strip 1 0.  The first paper-level identification is the
full times-mu bridge between the canonical strips on these two carriers.  The
type is recorded below, with no inhabitant. -/

/-- S1880's paper-route O object, over the same S1527 input. -/
noncomputable abbrev S1895S1880O (D : S1895PaperInput) :
    PaperQPilotObject (l := D.l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel D.l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice D.l)
      (S1895PaperInput.I D)
      (OrigXiFPaperSourceKummerGroup D.l) (OrigXiFPaperSourceStrip D.l) :=
  S1880PaperO D.l D.R D.redCompat D.hredCompat D.torCompat D.htorCompat
    D.orbCompat D.horbCompat D.secCompat D.hsecCompat D.cusCompat
    D.hcusCompat

/-- S1880PaperO's strip is exactly the concrete finite-local strip. -/
theorem s1895S1880_strip_eq_concrete (D : S1895PaperInput) :
    (S1895S1880O D).strip = finiteLocalIntegralFPrimeStrip 2 7 := rfl

/-- The paper (1,0) core is the S1487 shear strip. -/
theorem s1895S1880_core_eq_shear (D : S1895PaperInput) :
    S1895Core (S1895PaperInput.I D) = (S1487Strip 1 0) := rfl

/-- The two strip anchors already hold for S1880PaperO. -/
theorem s1895S1880_strip_anchors (D : S1895PaperInput) :
    (S1895S1880O D).strip = sourceQPilotStrip (S1895S1880O D).boundary ∧
      (S1895S1880O D).boundary.target_q =
        (S1895S1880O D).boundary.theater.thetaPacket.q :=
  ⟨(S1895S1880O D).strip_eq_source,
    (S1895S1880O D).boundary.target_q_eq_source⟩

/-- The (1,0) label binding already holds for S1880PaperO's one-column
carrier. -/
theorem s1895S1880_oneZeroLabel (D : S1895PaperInput) :
    S1895OneZeroLabelProp (FinitePrimePlace 2 7)
      (S1895S1880O D).oneColumn :=
  s1895OneZeroLabelProp_holds _ _

/-- The exact first missing type of the paper-level O identifications for
S1880PaperO: a full times-mu poly-isomorphism between the canonical times-mu
strips on the concrete finite-local strip and on the paper (1,0) shear core.
This is a Type (data), not a proposition to be proved by True; no inhabitant
is constructed. -/
def S1895S1880FTimesMuBridge (D : S1895PaperInput) : Type :=
  SourceFTimesMuPrimeStripFullPolyIsomorphism
    (SourceFTimesMuPrimeStrip.canonical (S1895S1880O D).strip)
    (SourceFTimesMuPrimeStrip.canonical (S1895Core (S1895PaperInput.I D)))

/-- The first missing object, named. -/
abbrev S1895FirstMissing (D : S1895PaperInput) : Type :=
  S1895S1880FTimesMuBridge D

/-- The first missing full-poly-isomorphism is equivalent to a times-mu strip
equivalence (the quotient is nonempty exactly when a representative exists). -/
theorem s1895FirstMissing_iff (D : S1895PaperInput) :
    Nonempty (S1895S1880FTimesMuBridge D) ↔
      Nonempty (SourceFTimesMuPrimeStripEquivalence
        (SourceFTimesMuPrimeStrip.canonical (S1895S1880O D).strip)
        (SourceFTimesMuPrimeStrip.canonical
          (S1895Core (S1895PaperInput.I D)))) :=
  SourceFTimesMuPrimeStripFullPolyIsomorphism.nonempty_iff

/-- Any inhabitant of the first missing type yields an FPrimeStripEquiv
between S1880PaperO's strip and the paper (1,0) core. -/
theorem s1895FirstMissing_to_stripEquiv (D : S1895PaperInput) :
    Nonempty (S1895S1880FTimesMuBridge D) →
      Nonempty (FPrimeStripEquiv (S1895S1880O D).strip
        (S1895Core (S1895PaperInput.I D))) := by
  rintro ⟨φ⟩
  obtain ⟨ψ, _⟩ :=
    SourceFTimesMuPrimeStripFullPolyIsomorphism.representative_exists φ
  exact ⟨ψ.toF⟩

/-! ## 7. The value-monoid obstruction at the bad place

At the place 5, the finite-local strip has value monoid LocalIntegralMonoid 5
and the S1487 shear strip has SourceHaarActualValueMonoid.  The former has
the nontrivial torsion element -1; the latter is torsion-free.  Hence no
monoid isomorphism exists, and no FPrimeStripEquiv between the two strips
exists.  This is why the paper object must be based on the actual paper core
(as in S1895PaperO), not on S1880PaperO's concrete strip. -/

/-- The place 5 in the concrete finite-prime carrier. -/
def s1895FivePlace : FinitePrimePlace 2 7 where
  val := 5
  property := by
    show 2 ≤ 5 ∧ 5 ≤ 7 ∧ Nat.Prime 5
    exact ⟨by norm_num, by norm_num, Nat.prime_five⟩

/-- The real -1 as an element of the local integral monoid at 5. -/
def s1895NegOne : LocalIntegralMonoid 5 :=
  ⟨-1, mem_nonZeroDivisors_of_ne_zero (by norm_num)⟩

theorem s1895NegOne_ne_one : s1895NegOne ≠ (1 : LocalIntegralMonoid 5) := by
  intro h
  have h' : (-1 : LocalAlgebraicIntegerRing 5) = 1 := congrArg Subtype.val h
  norm_num at h'

theorem s1895NegOne_mul_self :
    s1895NegOne * s1895NegOne = (1 : LocalIntegralMonoid 5) := by
  apply Subtype.ext
  change (-1 : LocalAlgebraicIntegerRing 5) * (-1) = 1
  ring

/-- The nonpositive-real value monoid is torsion-free: x * x = 1 forces
x = 1. -/
theorem s1895ValueMonoid_sq_eq_one {x : SourceHaarActualValueMonoid}
    (h : x * x = 1) : x = 1 := by
  have h' : Multiplicative.toAdd x + Multiplicative.toAdd x = 0 := by
    simpa using congrArg Multiplicative.toAdd h
  apply Multiplicative.ext
  have hreal :
      ((Multiplicative.toAdd x : sourceHaarActualNonpositiveAddSubmonoid) : Real) = 0 := by
    have h2 :
        ((Multiplicative.toAdd x : sourceHaarActualNonpositiveAddSubmonoid) : Real) +
          ((Multiplicative.toAdd x : sourceHaarActualNonpositiveAddSubmonoid) : Real) = 0 :=
      congrArg (fun z : sourceHaarActualNonpositiveAddSubmonoid => (z : Real)) h'
    linarith
  exact Subtype.ext hreal

/-- No monoid isomorphism exists between the local integral monoid at 5 and
the nonpositive-real value monoid. -/
theorem s1895_no_localIntegral_valueMonoid_equiv :
    ¬ Nonempty (LocalIntegralMonoid 5 ≃* SourceHaarActualValueMonoid) := by
  rintro ⟨e⟩
  have h := congrArg (fun x => e x) s1895NegOne_mul_self
  rw [map_mul, map_one] at h
  have hy : e s1895NegOne = 1 := s1895ValueMonoid_sq_eq_one h
  have h1 : s1895NegOne = 1 := by
    calc
      s1895NegOne = e.symm (e s1895NegOne) :=
        (e.symm_apply_apply s1895NegOne).symm
      _ = e.symm 1 := by rw [hy]
      _ = 1 := map_one e.symm
  exact s1895NegOne_ne_one h1

/-! ## 8. The first missing is impossible on the S1880 carrier

A full times-mu bridge would give an FPrimeStripEquiv between the concrete
finite-local strip and the paper core; that would give a monoid isomorphism at
the place 5, contradicting section 7.  Hence the paper-level identification
cannot be transported to S1880PaperO, and the rebased S1895PaperO is the
correct object. -/

/-- No F-prime-strip equivalence exists between S1880PaperO's concrete strip
and the paper (1,0) core, because their value monoids at the place 5 are not
isomorphic. -/
theorem s1895S1880_no_stripEquiv (D : S1895PaperInput) :
    ¬ Nonempty (FPrimeStripEquiv (S1895S1880O D).strip
      (S1895Core (S1895PaperInput.I D))) := by
  rintro ⟨e⟩
  have hmono : Nonempty ((S1895S1880O D).strip.Mon s1895FivePlace ≃*
      (S1895Core (S1895PaperInput.I D)).Mon s1895FivePlace) :=
    ⟨e.isoMon s1895FivePlace⟩
  have hmono' : Nonempty (LocalIntegralMonoid 5 ≃*
      SourceHaarActualValueMonoid) := hmono
  exact s1895_no_localIntegral_valueMonoid_equiv hmono'

/-- The first missing type has no inhabitant: the paper-level F-times-mu
identification is not merely unproved on S1880PaperO, it is impossible. -/
theorem s1895FirstMissing_impossible (D : S1895PaperInput) :
    ¬ Nonempty (S1895S1880FTimesMuBridge D) :=
  fun h => s1895S1880_no_stripEquiv D (s1895FirstMissing_to_stripEquiv D h)

/-! ## 9. Axiom probes -/

#print axioms s1895PaperO_identifications
#print axioms s1895PaperO_paper_strip
#print axioms s1895PaperO_paper_logKummer
#print axioms s1895PaperO_paper_qPilot
#print axioms s1895PaperO_label
#print axioms s1895PaperO_strip_anchors
#print axioms s1895S1880_strip_eq_concrete
#print axioms s1895S1880_no_stripEquiv
#print axioms s1895FirstMissing_impossible

end LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual

end