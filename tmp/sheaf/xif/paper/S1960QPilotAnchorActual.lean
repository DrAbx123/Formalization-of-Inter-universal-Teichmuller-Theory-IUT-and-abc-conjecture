import tmp.sheaf.xif.paper.S1958FullLogKummerUQActual

/-!
# S1960: the R6 q-pilot anchor on S1895PaperO and the S1927 package

## The R6 obligation

`LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows`, R6 (lines
74--75), records the exact reduced source obligation that is *not* made:

> the identification of the reduced q-pilot anchor with the paper's q-pilot
> `F^boxplus-triangleright-x-mu`-prime-strip (DSH-F trap T5).

The reduced q-pilot anchor is `sourceQPilotStrip input`, i.e. the `F`-layer
strip of the input Hodge theater.  On `S1895PaperO` the boundary is the actual
`OrigXiFPaperBoundary I 1 0`, so its `qPilotStrip` vertex is the paper
`(1,0)` core `I.fPrimeStripAt 1 0 = S1895Core I` -- definitionally, not by a
new identification.  That is the whole reduced content available here.

## What this file constructs (all actual, kernel-checked)

1. The reduced q-pilot anchor of the S1895 paper O object,

     reducedQPilotAnchor D = sourceQPilotStrip (S1895PaperO D).boundary,

   with the definitional equalities to `(S1895PaperO D).strip`, to the paper
   `(1,0)` core `S1895Core (paperInput D)` and to the actual theater strip
   `((paperInput D).theaterAt 1 0).primeStrip`.
2. Its canonical times-mu lift `reducedQPilotTimesMu D`
   (`SourceFTimesMuPrimeStrip.canonical`), definitionally the S1895
   `s1895TimesMuStrip D`, with its underlying strip and torsion-quotient
   fibers.
3. The actual reduced identification `reducedAnchorIdentification D`, a
   genuine `SourceFTimesMuPrimeStripFullPolyIsomorphism` from the canonical
   lift to the S1895 paper-core times-mu strip, plus its equivalence form.
4. `S1960QPilotAnchoredUQ D`: the S1958 package `paperFullLogKummerUQ D`
   together with the reduced anchor, its canonical lift, the reduced
   identification, the paper one-column structure and the actual `(1,0)`
   label.  It is inhabited for every `S1895PaperInput`.
5. The anchor is the lower-left (LGP) vertex of the package's actual
   Kummer-evaluation square `(paperFullLogKummerUQ D).evaluationSquare`.
6. The exact placement of S1895's `paper_strip_identification` slot: it is
   *definitionally* the canonical self-identification of the reduced anchor
   (the paper side used by S1895 is `s1895TimesMuStrip D`, the same canonical
   lift).  It is therefore not R6.

## The exact first missing (R6 proper)

R6 asks for an identification with the **paper's** q-pilot
`F^boxplus-triangleright-x-mu`-prime-strip.  That object is a *definition*
that does not exist in the tree: IUT III, Definition 3.8, (i), determines the
q-pilot object by the `q_v`, and no Lean definition of the paper-side q-pilot
`F^boxplus`-prime-strip (before or after the times-mu lift) is present.  The
named actual candidate is the canonical times-mu lift of the `(1,0)` core
(the term `qPilotFTimesMuPrimeStripAt10` of
`QPilotFTimesMuPrimeStripActual`); that module states explicitly that it is
not asserted to be the paper's q-pilot strip.  The canonical q-pilot-object
constructor `paperQPilotObjectActualOfCanonical` (`QPilotCanonicalConstruction`)
likewise takes the F-prime-strip as a parameter and then applies
`SourceFTimesMuPrimeStrip.canonical`; it does not construct a `q_v`-determined
paper strip.  Hence the first missing is a definition, not a proposition:
the paper-side q-pilot times-mu strip together with its `q_v`-determination.  This file consequently does not declare a
paper-side type, an arbitrary inhabitant, a free `Prop` slot, or a
`FirstMissing` carrier -- any such type-level object that could be inhabited
from the present data would be a fake anchor.  Instead, §5 names the exact
interface `QPilotAnchorIdentification D paperStrip`: it is parameterized by
the missing paper-side strip, and the only actual inhabitant supplied is the
reduced self-identification.

## Honesty note

No `sorry`, `admit`, `axiom`, `True`/`PUnit` slot, empty type, arbitrary
inhabitant or assumption-only `Nonempty` gate is used.  The classical inputs
are exactly those already carried by S1895/S1958 (`propext`,
`Classical.choice`, `Quot.sound`), see the axiom probes at the end.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1960QPilotAnchorActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual
open LeanFormal.IUT.XiFPaper.S1951KummerEvaluationSquareActual
open LeanFormal.IUT.XiFPaper.S1958FullLogKummerUQActual
open LeanFormal.IUT.XiFPaper.OrigXiFPaperBoundaryStrip

/-! ## 1. The reduced q-pilot anchor of S1895PaperO -/

/-- The finite-prime place type of the S1895 paper input. -/
abbrev PaperV : Type := FinitePrimePlace 2 7

/-- The actual S1527 input carried by an S1895 paper input. -/
abbrev paperInput (D : S1895PaperInput) :
    OriginalInput.{0, 0, 0, 0, 0} D.l PaperV :=
  S1895PaperInput.I D

/-- The reduced q-pilot anchor of the S1895 paper O object: the
`qPilotStrip` vertex of the source boundary, i.e. the `F`-layer source strip
anchor of `SourceKummerEvaluationArrows`. -/
noncomputable def reducedQPilotAnchor (D : S1895PaperInput) :
    FPrimeStrip PaperV :=
  sourceQPilotStrip (S1895PaperO D).boundary

/-- The reduced anchor is the source `qPilotStrip` vertex of the boundary. -/
@[simp] theorem reducedQPilotAnchor_eq_source (D : S1895PaperInput) :
    reducedQPilotAnchor D =
      sourceQPilotStrip (S1895PaperO D).boundary := rfl

/-- The reduced anchor is the strip of the S1895 paper O object. -/
@[simp] theorem reducedQPilotAnchor_eq_paperO_strip (D : S1895PaperInput) :
    reducedQPilotAnchor D = (S1895PaperO D).strip := rfl

/-- The reduced anchor is the actual paper `(1,0)` core. -/
@[simp] theorem reducedQPilotAnchor_eq_core (D : S1895PaperInput) :
    reducedQPilotAnchor D = S1895Core (paperInput D) := rfl

/-- The reduced anchor is the `(1,0)` source F-prime-strip of the S1527 input. -/
@[simp] theorem reducedQPilotAnchor_eq_fPrimeStripAt (D : S1895PaperInput) :
    reducedQPilotAnchor D = (paperInput D).fPrimeStripAt 1 0 := rfl

/-- The reduced anchor is the actual theater strip at `(1,0)`. -/
@[simp] theorem reducedQPilotAnchor_eq_theater (D : S1895PaperInput) :
    reducedQPilotAnchor D = ((paperInput D).theaterAt 1 0).primeStrip := rfl

/-- The reduced anchor is the OrigXiF actual source q-pilot strip at `(1,0)`. -/
@[simp] theorem reducedQPilotAnchor_eq_origXiF (D : S1895PaperInput) :
    reducedQPilotAnchor D = OrigXiFPaperStrip (paperInput D) 1 0 := rfl

/-- The reduced anchor is the LGP (lower-left) corner of the actual
Kummer-evaluation square `s1927Square D` carried by the S1927 package.  This is
the reduced LGP vertex; it is not asserted to be the paper's `F_LGP` (R3). -/
@[simp] theorem reducedQPilotAnchor_eq_lgpStrip (D : S1895PaperInput) :
    reducedQPilotAnchor D = lgpStrip D := rfl

/-- The reduced anchor is the lower-left vertex of the package's actual
Kummer-evaluation square. -/
@[simp] theorem reducedQPilotAnchor_eq_packageSquare_lowerLeft
    (D : S1895PaperInput) :
    reducedQPilotAnchor D = (paperFullLogKummerUQ D).evaluationSquare.lowerLeft :=
  rfl

/-! ## 2. The canonical times-mu lift and the reduced identification -/

/-- The canonical `F^boxplus-triangleright-x-mu` lift of the reduced anchor:
the O-times-mu fibers are the torsion quotients of the actual unit groups. -/
noncomputable def reducedQPilotTimesMu (D : S1895PaperInput) :
    SourceFTimesMuPrimeStrip PaperV :=
  SourceFTimesMuPrimeStrip.canonical (reducedQPilotAnchor D)

/-- The underlying F-prime-strip of the lift is the reduced anchor. -/
@[simp] theorem reducedQPilotTimesMu_toFPrimeStrip (D : S1895PaperInput) :
    (reducedQPilotTimesMu D).toFPrimeStrip = reducedQPilotAnchor D := rfl

/-- The times-mu fiber at `v` is the torsion quotient of the actual unit group
of the reduced anchor at `v`. -/
@[simp] theorem reducedQPilotTimesMu_timesMu (D : S1895PaperInput) (v : PaperV) :
    (reducedQPilotTimesMu D).timesMu v =
      TimesMuQuotient ((reducedQPilotAnchor D).Mon v)ˣ := rfl

/-- The quotient map of the lift is the canonical torsion quotient map. -/
@[simp] theorem reducedQPilotTimesMu_quotientMap (D : S1895PaperInput)
    (v : PaperV) :
    (reducedQPilotTimesMu D).timesMuQuotientMap v =
      TimesMuQuotient.quotientMap := rfl

/-- The canonical lift of the reduced anchor is definitionally the S1895
canonical times-mu strip of the paper `(1,0)` core. -/
theorem reducedQPilotTimesMu_eq_s1895TimesMuStrip (D : S1895PaperInput) :
    reducedQPilotTimesMu D = s1895TimesMuStrip D := rfl

/-- The actual full poly-isomorphism from the reduced anchor's canonical
times-mu lift to the S1895 canonical times-mu strip.  It is the canonical
self-identification: both sides are definitionally
`SourceFTimesMuPrimeStrip.canonical (S1895Core I)`. -/
noncomputable def reducedAnchorIdentification (D : S1895PaperInput) :
    SourceFTimesMuPrimeStripFullPolyIsomorphism (reducedQPilotTimesMu D)
      (s1895TimesMuStrip D) :=
  SourceFTimesMuPrimeStripFullPolyIsomorphism.id _

/-- The reduced identification is exactly the identity full poly-isomorphism. -/
theorem reducedAnchorIdentification_eq_id (D : S1895PaperInput) :
    reducedAnchorIdentification D =
      SourceFTimesMuPrimeStripFullPolyIsomorphism.id (s1895TimesMuStrip D) := rfl

/-- The reduced identification, in equivalence form (the identity equivalence). -/
noncomputable def reducedAnchorEquivalence (D : S1895PaperInput) :
    SourceFTimesMuPrimeStripEquivalence (reducedQPilotTimesMu D)
      (s1895TimesMuStrip D) :=
  SourceFTimesMuPrimeStripEquivalence.refl _

/-- The reduced identification is actual: the full poly-isomorphism class is
inhabited. -/
theorem reducedAnchorIdentification_nonempty (D : S1895PaperInput) :
    Nonempty (SourceFTimesMuPrimeStripFullPolyIsomorphism
      (reducedQPilotTimesMu D) (s1895TimesMuStrip D)) :=
  ⟨reducedAnchorIdentification D⟩

/-! ## 3. S1895's `paper_strip_identification` is the reduced self-identification

S1895 instantiates the paper strip slot on `S1895PaperO` by
`S1895FTimesMuProp I (S1895Core I)`, i.e. by the full poly-isomorphism from
the canonical times-mu strip on the core to itself.  The theorem below records
this as an equality of propositions: the slot is *definitionally* the reduced
identification of §2, whose paper side is the same canonical lift.  This is why
the slot does not close R6. -/

/-- The S1895 paper-strip slot is definitionally the reduced identification
proposition. -/
theorem s1895PaperO_paper_strip_eq_reducedSelf (D : S1895PaperInput) :
    (S1895PaperO D).paper_strip_identification =
      Nonempty (SourceFTimesMuPrimeStripFullPolyIsomorphism
        (reducedQPilotTimesMu D) (s1895TimesMuStrip D)) := rfl

/-- The reduced identification proves the S1895 paper-strip slot. -/
theorem s1895PaperO_paper_strip_reduced (D : S1895PaperInput) :
    (S1895PaperO D).paper_strip_identification :=
  reducedAnchorIdentification_nonempty D

/-! ## 4. The anchored S1927 package -/

/-- The S1960 anchored package: the actual S1958 full log-Kummer package
`paperFullLogKummerUQ D`, the actual reduced q-pilot anchor, its canonical
times-mu lift, the actual reduced identification and the paper `(1,0)` label
data.  The identification field is the reduced one; identifying it with the
paper's q-pilot strip is R6 (see §5). -/
structure S1960QPilotAnchoredUQ (D : S1895PaperInput) where
  /-- the S1927 full log-Kummer package -/
  package : S1927FullLogKummerUQ D
  /-- the package is the S1958 assembly -/
  package_eq : package = paperFullLogKummerUQ D
  /-- the actual reduced q-pilot anchor -/
  anchor : FPrimeStrip PaperV
  /-- the anchor is the S1895 paper O object's strip -/
  anchor_eq_paperO : anchor = (S1895PaperO D).strip
  /-- the anchor is the source q-pilot strip of the boundary -/
  anchor_eq_source : anchor = sourceQPilotStrip (S1895PaperO D).boundary
  /-- the canonical times-mu lift of the anchor -/
  timesMu : SourceFTimesMuPrimeStrip PaperV
  /-- the lift is the canonical times-mu construction -/
  timesMu_eq : timesMu = SourceFTimesMuPrimeStrip.canonical anchor
  /-- the actual reduced full poly-isomorphism -/
  identification :
    SourceFTimesMuPrimeStripFullPolyIsomorphism timesMu (s1895TimesMuStrip D)
  /-- the package's one-column structure is the paper O object's -/
  oneColumn_eq : package.oneColumn = (S1895PaperO D).oneColumn
  /-- the package's label has column index `1` -/
  label_n : package.label.n = 1
  /-- the package's label has vertical index `0` -/
  label_m : package.label.m = 0

/-- The anchored package is inhabited for every S1895 paper input. -/
noncomputable def s1960QPilotAnchoredUQ (D : S1895PaperInput) :
    S1960QPilotAnchoredUQ D where
  package := paperFullLogKummerUQ D
  package_eq := rfl
  anchor := reducedQPilotAnchor D
  anchor_eq_paperO := rfl
  anchor_eq_source := rfl
  timesMu := reducedQPilotTimesMu D
  timesMu_eq := rfl
  identification := reducedAnchorIdentification D
  oneColumn_eq := rfl
  label_n := paperFullLogKummerUQ_label_n D
  label_m := paperFullLogKummerUQ_label_m D

/-- The anchored package exists. -/
theorem s1960QPilotAnchoredUQ_exists (D : S1895PaperInput) :
    Nonempty (S1960QPilotAnchoredUQ D) :=
  ⟨s1960QPilotAnchoredUQ D⟩

/-- The anchored package's package component is the S1958 package. -/
@[simp] theorem s1960QPilotAnchoredUQ_package (D : S1895PaperInput) :
    (s1960QPilotAnchoredUQ D).package = paperFullLogKummerUQ D := rfl

/-- The anchored package's anchor is the S1895 paper O object's strip. -/
@[simp] theorem s1960QPilotAnchoredUQ_anchor (D : S1895PaperInput) :
    (s1960QPilotAnchoredUQ D).anchor = (S1895PaperO D).strip := rfl

/-- The anchored package's times-mu lift is the S1895 canonical strip. -/
@[simp] theorem s1960QPilotAnchoredUQ_timesMu (D : S1895PaperInput) :
    (s1960QPilotAnchoredUQ D).timesMu = s1895TimesMuStrip D := rfl

/-- The anchored package's label is the S1895 `(1,0)` label. -/
theorem s1960QPilotAnchoredUQ_label (D : S1895PaperInput) :
    (s1960QPilotAnchoredUQ D).package.label =
      s1895PaperO_oneColumnLabel D :=
  paperFullLogKummerUQ_label D

/-- The anchored package carries the S1895 scalar candidate (the bad-place
absolute-log sum); this scalar is not altered by the strip identification. -/
theorem s1960QPilotAnchoredUQ_qPilotLogVolume (D : S1895PaperInput) :
    (S1895PaperO D).qPilotLogVolume =
      sourceQPilotSignedLog (paperInput D).initial := rfl

/-! ## 5. The R6 interface and the exact first missing

R6 is the identification of the reduced q-pilot anchor with the **paper's**
q-pilot `F^boxplus-triangleright-x-mu`-prime-strip.  The paper side is a
definition that does not exist in the tree.  The identification type below is
therefore parameterized by the paper-side strip: it is the exact interface to be
populated when the paper-side definition lands.  Its only actual inhabitant in
this file is the reduced self-identification, which is not R6. -/

/-- The R6 identification interface: an identification of the reduced anchor's
canonical times-mu lift with a supplied paper-side q-pilot times-mu strip.  The
paper-side strip is an explicit parameter because it is not defined in the tree
(IUT III, Definition 3.8, (i), `q_v`-determination). -/
def QPilotAnchorIdentification (D : S1895PaperInput)
    (paperStrip : SourceFTimesMuPrimeStrip PaperV) : Type :=
  SourceFTimesMuPrimeStripFullPolyIsomorphism (reducedQPilotTimesMu D) paperStrip

/-- The R6 interface is nonempty exactly when a times-mu equivalence to the
supplied paper-side strip exists. -/
theorem qPilotAnchorIdentification_nonempty_iff (D : S1895PaperInput)
    (paperStrip : SourceFTimesMuPrimeStrip PaperV) :
    Nonempty (QPilotAnchorIdentification D paperStrip) ↔
      Nonempty (SourceFTimesMuPrimeStripEquivalence
        (reducedQPilotTimesMu D) paperStrip) :=
  SourceFTimesMuPrimeStripFullPolyIsomorphism.nonempty_iff

/-- The canonical self-identification of the reduced anchor.  It is an actual
inhabitant of the *reduced* interface; it is not R6, since its paper side is the
reduced anchor itself, not an independent paper q-pilot strip. -/
noncomputable def qPilotAnchorSelfIdentification (D : S1895PaperInput) :
    QPilotAnchorIdentification D (reducedQPilotTimesMu D) :=
  SourceFTimesMuPrimeStripFullPolyIsomorphism.id _

/-- The reduced identification inhabits the R6 interface at the paper `(1,0)`
core's canonical times-mu strip. -/
noncomputable def reducedAnchorIdentification_mem (D : S1895PaperInput) :
    QPilotAnchorIdentification D (s1895TimesMuStrip D) :=
  reducedAnchorIdentification D

/-- **The precise first missing of R6.**  The missing datum is a paper-side
`paperStrip : SourceFTimesMuPrimeStrip PaperV` that is the paper's q-pilot
`F^boxplus-triangleright-x-mu`-prime-strip determined by the `q_v` of IUT III,
Definition 3.8, (i).  The tree supplies no such definition: the canonical
times-mu lift of the `(1,0)` core (the term `qPilotFTimesMuPrimeStripAt10`)
is only a candidate and is not asserted to be the paper strip.  Consequently no
inhabitant of `QPilotAnchorIdentification D paperStrip` for a *paper* strip is
constructed here, and no paper-side type or free `Prop` slot is declared.  The
theorem below records the exact logical shape of the reduction: once such a
`paperStrip` is supplied, R6 is exactly the nonemptiness of the
times-mu-equivalence class above.  The first missing remains the definition of
`paperStrip`, not a proposition. -/
theorem s1960_r6_exact_reduction (D : S1895PaperInput)
    (paperStrip : SourceFTimesMuPrimeStrip PaperV) :
    Nonempty (QPilotAnchorIdentification D paperStrip) ↔
      Nonempty (SourceFTimesMuPrimeStripEquivalence
        (reducedQPilotTimesMu D) paperStrip) :=
  qPilotAnchorIdentification_nonempty_iff D paperStrip

/-! ## 6. Axiom probes -/

#print axioms reducedQPilotAnchor
#print axioms reducedQPilotTimesMu
#print axioms reducedAnchorIdentification
#print axioms s1895PaperO_paper_strip_eq_reducedSelf
#print axioms s1895PaperO_paper_strip_reduced
#print axioms s1960QPilotAnchoredUQ
#print axioms s1960QPilotAnchoredUQ_exists
#print axioms s1960QPilotAnchoredUQ_label
#print axioms reducedQPilotAnchor_eq_packageSquare_lowerLeft
#print axioms qPilotAnchorIdentification_nonempty_iff
#print axioms s1960_r6_exact_reduction

end LeanFormal.IUT.XiFPaper.S1960QPilotAnchorActual