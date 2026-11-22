import tmp.sheaf.xif.paper.S1954ArchimedeanPeriodActual
import tmp.sheaf.xif.paper.S1958FullLogKummerUQActual

/-!
# S1969: the period-carrying archimedean component of the full log-Kummer package

## The gap this file closes

S1927 records the archimedean component of its full log-Kummer package as

  'S1927FirstMissing D = (w : InfinitePlace (PaperFmod D)) ->
     ArchimedeanLogShellDatum D w',

a *reduced* datum: a compact convex set contained in the actual closed unit ball
and containing 0.  S1950 fills that slot with the actual closed unit ball at
every infinite place, and S1958 assembles 'paperFullLogKummerUQ D' from it.

S1954 constructed the paper's *full*, period-carrying datum
'PaperArchimedeanLogShellDatum D w' (the log-shell I_k = {x | ‖x‖ ≤ π}, the
period generator 2πi, the fundamental segment [-πi, πi], the orbit identity
I_k = O_k^× . [-πi, πi], and the log-link upper semi-commutativity) at every
**complex** infinite place, and proved that

* no full datum exists at a real place ('real_place_not_inhabited');
* no full datum's log-shell is contained in the reduced unit ball
  ('no_logShell_subset_unitBall'), because the period has norm 2π > 2;
  therefore the reduced S1927 slot 'ArchimedeanLogShellDatum D w' can never be
  filled by the paper's datum.

So the paper's archimedean component must be carried by a *separate*,
complex-place-indexed slot.  This file defines that slot and wires it into the
full log-Kummer package:

* 'S1927FirstMissingComplex D := (w) (hw : w.IsComplex) ->
  PaperArchimedeanLogShellDatum D w', inhabited at every D by
  'paperArchimedeanLogShellComplex D' (the S1954 family);
* 'S1969FullLogKummerUQPeriod D', the period-carrying full log-Kummer package:
  S1958's reduced package together with the full paper archimedean family, and
  the paper's (b^arc) containment O_k ⊆ I_k relating the two;
* the canonical inhabitant 'paperFullLogKummerUQPeriod D', whose reduced
  component is definitionally S1958's 'paperFullLogKummerUQ D' and whose
  archimedean component is definitionally S1954's family;
* 's1969FullLogKummerUQPeriod_nonempty_iff_square': after this file the only
  remaining *input* of the log-Kummer interface is the Kummer evaluation
  square, which S1951 already constructs on the four actual source strips.

## No real-place datum

The full paper family over **all** infinite places is not asserted: it is
provably empty as soon as one infinite place is real
('fullFamily_nonempty_iff_allComplex', 'not_nonempty_fullFamily_of_isReal').
The complex-place-indexed slot 'S1927FirstMissingComplex' is the maximal honest
paper-faithful version; nothing is fabricated at real places.

## The exact remaining first missing

The remaining paper-level missing is **not** a proposition.  The square used by
the period-carrying package is S1951's reduced square on the four actual source
strips envStrip, gauStrip, lgpStrip, lgpLowerStrip; the paper's four coric
vertices F_env, F_gau, F_LGP, F_lgp are missing *definitions* (the tree has no
F^⊩-prime-strip carrier; S1959 records this exactly).  The vertices, the
operation-level Kummer/evaluation isomorphisms of IUT II, Definition 4.9, (i),
and Corollary 4.10, (ii), and the q-pilot anchor identification (R6) therefore
cannot be stated as propositions here.  's1969_square_corners' records which
actual strips the package's square uses, so the reduction is not hidden.

## Honesty note

No sorry, admit, axiom, arbitrary inhabitant, empty type or fake real place
datum is used.  The classical inputs are exactly those of S1950, S1951, S1954
and S1958 (propext, Classical.choice, Quot.sound); see the axiom probes at the
end.
-/

noncomputable section

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.S1969ComplexArchimedeanUQActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual
open LeanFormal.IUT.XiFPaper.S1950ArchimedeanLogShellActual
open LeanFormal.IUT.XiFPaper.S1951KummerEvaluationSquareActual
open LeanFormal.IUT.XiFPaper.S1954ArchimedeanPeriodActual
open LeanFormal.IUT.XiFPaper.S1958FullLogKummerUQActual

/-! ## 1. The complex-place archimedean interface -/

/-- The paper's archimedean log-shell type over the **complex** infinite places
of the base field Fmod.  At each complex place it asks for the full,
period-carrying datum of [IUTchIII], Definition 1.1, (ii), i.e. S1954's
'PaperArchimedeanLogShellDatum D w' (I_k = {x | ‖x‖ ≤ π}, period 2πi,
fundamental segment [-πi, πi], orbit identity, log-link upper
semi-commutativity).

This is *not* S1927's 'S1927FirstMissing D': that type asks for a reduced datum
at every infinite place, including real ones, and its containment requirement
'logShell ⊆ {x | ‖x‖ ≤ 1}' is incompatible with the nonzero period
(S1954, 'no_logShell_subset_unitBall').  The paper itself only meets complex
archimedean fields ([IUTchI], Definition 3.1, (a), assumes sqrt(-1) ∈ F;
[IUTchIII], Remark 1.2.2, (ii), reads 'K_v is a complex archimedean field').
'hw : w.IsComplex' is therefore part of the index of this interface: no datum
is produced or required at a real place. -/
def S1927FirstMissingComplex (D : S1895PaperInput) : Type :=
  (w : NumberField.InfinitePlace (PaperFmod D)) -> (hw : w.IsComplex) ->
    PaperArchimedeanLogShellDatum D w

/-- The actual paper archimedean family: at every complex infinite place the
π-disk with period 2πi, fundamental segment [-πi, πi], orbit identity
I_k = O_k^× . [-πi, πi] and log-link upper semi-commutativity, all from
S1954.  This is the inhabitant of the complex-place interface. -/
noncomputable def paperArchimedeanLogShellComplex (D : S1895PaperInput) :
    S1927FirstMissingComplex D :=
  fun w hw => paperArchimedeanLogShellDatum D w hw

/-- The complex-place archimedean interface is inhabited for every S1895 paper
input: the paper archimedean component is no longer a missing input. -/
theorem s1927FirstMissingComplex_inhabited (D : S1895PaperInput) :
    Nonempty (S1927FirstMissingComplex D) :=
  ⟨paperArchimedeanLogShellComplex D⟩

/-- The complex-place family applies to S1954's constructed datum. -/
@[simp] theorem paperArchimedeanLogShellComplex_apply
    (D : S1895PaperInput) (w : NumberField.InfinitePlace (PaperFmod D))
    (hw : w.IsComplex) :
    paperArchimedeanLogShellComplex D w hw = paperArchimedeanLogShellDatum D w hw :=
  rfl

/-- The full paper family over **all** infinite places exists exactly when every
infinite place is complex.  This is the precise reason the interface is indexed
by 'hw : w.IsComplex': at a real place the full datum is provably uninhabited
(S1954, 'real_place_not_inhabited'), so an all-places family cannot honestly
exist, and the equivalence below is not a weakening but the exact boundary. -/
theorem fullFamily_nonempty_iff_allComplex (D : S1895PaperInput) :
    Nonempty ((w : NumberField.InfinitePlace (PaperFmod D)) ->
        PaperArchimedeanLogShellDatum D w) <->
      forall w : NumberField.InfinitePlace (PaperFmod D), w.IsComplex := by
  constructor
  . rintro ⟨F⟩ w
    by_contra hw
    have hreal : w.IsReal :=
      NumberField.InfinitePlace.not_isComplex_iff_isReal.mp hw
    exact real_place_not_inhabited D w hreal ⟨F w⟩
  . intro h
    exact ⟨fun w => paperArchimedeanLogShellDatum D w (h w)⟩

/-- No all-places full paper family exists as soon as one infinite place is
real: the Pi type over all infinite places is then empty. -/
theorem not_nonempty_fullFamily_of_isReal (D : S1895PaperInput)
    {w : NumberField.InfinitePlace (PaperFmod D)} (hreal : w.IsReal) :
    Not (Nonempty ((w' : NumberField.InfinitePlace (PaperFmod D)) ->
      PaperArchimedeanLogShellDatum D w')) := by
  rintro ⟨F⟩
  exact real_place_not_inhabited D w hreal ⟨F w⟩

/-- At a real place the full paper datum is provably uninhabited (S1954).  This
re-export is the formal statement that this file does not fabricate a real
place datum. -/
theorem not_nonempty_paperDatum_of_isReal (D : S1895PaperInput)
    {w : NumberField.InfinitePlace (PaperFmod D)} (hreal : w.IsReal) :
    Not (Nonempty (PaperArchimedeanLogShellDatum D w)) :=
  real_place_not_inhabited D w hreal

/-- The full paper datum cannot fill the reduced S1927 archimedean slot: no
reduced datum has the paper's log-shell, because the reduced slot forces
containment in the plain unit ball while the period has norm 2π.  This is why
the paper component needs its own slot instead of replacing
'S1927FirstMissing D'. -/
theorem not_reducedDatum_of_fullLogShell (D : S1895PaperInput)
    {w : NumberField.InfinitePlace (PaperFmod D)} (hw : w.IsComplex)
    (F : PaperArchimedeanLogShellDatum D w) :
    Not (Exists fun R : ArchimedeanLogShellDatum D w => R.logShell = F.logShell) := by
  rintro ⟨R, hR⟩
  refine no_logShell_subset_unitBall D w hw F ?_
  rw [← hR]
  exact R.logShell_subset_unitBall

/-! ## 2. The period-carrying full log-Kummer package -/

/-- The period-carrying full log-Kummer package on 1,circ U_Q.

S1927's 'S1927FullLogKummerUQ' carries the reduced archimedean slot
'S1927FirstMissing D' (a unit-ball family over all infinite places).  Because
that slot is provably incompatible with the paper's π-normalized datum
('no_logShell_subset_unitBall'), the paper's archimedean component is attached
here as a second, complex-place-indexed component, together with the paper's
(b^arc) containment O_k ⊆ I_k between the two.

'package' is S1958's reduced package: it carries the one-column structure, the
(1,0) label, the finite log-shell packet and the Kummer evaluation square of
1,circ U_Q.  The full paper component 'archimedeanLogShell' is the S1954 family
at every complex place. -/
structure S1969FullLogKummerUQPeriod (D : S1895PaperInput) where
  /-- the reduced S1927 full log-Kummer package (S1958's actual assembly) -/
  package : S1927FullLogKummerUQ D
  /-- the full, period-carrying paper archimedean component, at complex places -/
  archimedeanLogShell : S1927FirstMissingComplex D
  /-- (b^arc) of [IUTchIII], Proposition 1.2, (v): at every complex place the
  reduced S1927 log-shell is contained in the full period-carrying log-shell
  (O_k ⊆ I_k).  Both containments are one-sided; the reverse containment is
  false ('paperFullLogKummerUQPeriod_logShell_not_subset_unitBall'). -/
  reducedLogShell_subset :
    forall (w : NumberField.InfinitePlace (PaperFmod D)) (hw : w.IsComplex),
      (package.archimedeanLogShell w).logShell ⊆
        (archimedeanLogShell w hw).logShell

/-- The period-carrying full log-Kummer package from a given Kummer evaluation
square: the reduced package is S1950's assembly at that square, whose
archimedean slot is the actual closed unit ball, and the full component is
S1954's actual paper family.  The (b^arc) containment is the actual
'archimedeanUnitBall D w ⊆ paperLogShell D w'. -/
noncomputable def paperFullLogKummerUQPeriodOfSquare
    (D : S1895PaperInput) (square : S1927KummerEvaluationSquareActual D) :
    S1969FullLogKummerUQPeriod D where
  package := paperFullLogKummerUQOfKummerSquare D square
  archimedeanLogShell := paperArchimedeanLogShellComplex D
  reducedLogShell_subset := by
    intro w hw
    change (paperArchimedeanLogShell D w).logShell ⊆
      (paperArchimedeanLogShellDatum D w hw).logShell
    rw [paperArchimedeanLogShell_logShell, paperArchimedeanLogShellDatum_logShell]
    exact archimedeanUnitBall_subset_paperLogShell D w

/-- The canonical period-carrying full log-Kummer package: S1958's actual
package plus S1954's actual full archimedean family. -/
noncomputable def paperFullLogKummerUQPeriod (D : S1895PaperInput) :
    S1969FullLogKummerUQPeriod D :=
  paperFullLogKummerUQPeriodOfSquare D (s1927Square D)

/-- The reduced component of the period-carrying package, as an S1927 full
log-Kummer package.  Its archimedean slot is necessarily S1950's unit ball; the
full period-carrying datum cannot be placed there. -/
noncomputable def S1969FullLogKummerUQPeriod.toS1927FullLogKummerUQ
    {D : S1895PaperInput} (P : S1969FullLogKummerUQPeriod D) :
    S1927FullLogKummerUQ D :=
  P.package

/-! ## 3. Component identifications with S1958 and S1954 -/

/-- The reduced component of the canonical period-carrying package is
definitionally S1958's 'paperFullLogKummerUQ D'. -/
@[simp] theorem paperFullLogKummerUQPeriod_package (D : S1895PaperInput) :
    (paperFullLogKummerUQPeriod D).package = paperFullLogKummerUQ D :=
  rfl

/-- The full archimedean component of the canonical package is definitionally
S1954's constructed family. -/
@[simp] theorem paperFullLogKummerUQPeriod_archimedeanLogShell
    (D : S1895PaperInput) :
    (paperFullLogKummerUQPeriod D).archimedeanLogShell =
      paperArchimedeanLogShellComplex D :=
  rfl

/-- The reduced component's archimedean slot is S1950's actual closed unit ball
family, i.e. S1958's archimedean component. -/
@[simp] theorem paperFullLogKummerUQPeriod_reduced_archimedeanLogShell
    (D : S1895PaperInput) :
    (paperFullLogKummerUQPeriod D).toS1927FullLogKummerUQ.archimedeanLogShell =
      paperArchimedeanLogShell D :=
  rfl

/-- The reduced component of the canonical package is S1958's package. -/
@[simp] theorem paperFullLogKummerUQPeriod_toS1927FullLogKummerUQ
    (D : S1895PaperInput) :
    (paperFullLogKummerUQPeriod D).toS1927FullLogKummerUQ =
      paperFullLogKummerUQ D :=
  rfl

/-- The Kummer evaluation square of the period-carrying package is S1951's
actual square. -/
@[simp] theorem paperFullLogKummerUQPeriod_evaluationSquare
    (D : S1895PaperInput) :
    (paperFullLogKummerUQPeriod D).package.evaluationSquare = s1927Square D :=
  rfl

/-- The square carried by the period-carrying package is the actual
SourceKummerEvaluationSquare of S1951 on the four actual source strips. -/
@[simp] theorem paperFullLogKummerUQPeriod_square
    (D : S1895PaperInput) :
    (paperFullLogKummerUQPeriod D).package.evaluationSquare.square =
      kummerEvaluationSquare D :=
  rfl

/-- The four corners of the package's square are the four actual source strips
envStrip, gauStrip, lgpStrip, lgpLowerStrip.  These are source F-prime-strips;
they are not asserted to be the paper's coric vertices (that definition is the
remaining first missing, S1959). -/
theorem s1969_square_corners (D : S1895PaperInput) :
    (paperFullLogKummerUQPeriod D).package.evaluationSquare.upperLeft = envStrip D ∧
      (paperFullLogKummerUQPeriod D).package.evaluationSquare.upperRight = gauStrip D ∧
        (paperFullLogKummerUQPeriod D).package.evaluationSquare.lowerLeft = lgpStrip D ∧
          (paperFullLogKummerUQPeriod D).package.evaluationSquare.lowerRight =
            lgpLowerStrip D :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The full component's log-shell at a complex place is the paper's π-disk
I_k = {x | ‖x‖ ≤ π}. -/
@[simp] theorem paperFullLogKummerUQPeriod_logShell (D : S1895PaperInput)
    (w : NumberField.InfinitePlace (PaperFmod D)) (hw : w.IsComplex) :
    ((paperFullLogKummerUQPeriod D).archimedeanLogShell w hw).logShell =
      paperLogShell D w :=
  rfl

/-- The full component's period generator is 2πi. -/
@[simp] theorem paperFullLogKummerUQPeriod_period (D : S1895PaperInput)
    (w : NumberField.InfinitePlace (PaperFmod D)) (hw : w.IsComplex) :
    ((paperFullLogKummerUQPeriod D).archimedeanLogShell w hw).period =
      paperPeriod D w hw :=
  rfl

/-- The full component's fundamental closed segment is [-πi, πi]. -/
@[simp] theorem paperFullLogKummerUQPeriod_fundamentalSegment
    (D : S1895PaperInput) (w : NumberField.InfinitePlace (PaperFmod D))
    (hw : w.IsComplex) :
    ((paperFullLogKummerUQPeriod D).archimedeanLogShell w hw).fundamentalSegment =
      paperFundamentalSegment D w hw :=
  rfl

/-- The period of the package's full component has norm 2π, the length of
O_k^× ⊆ k. -/
theorem paperFullLogKummerUQPeriod_period_norm (D : S1895PaperInput)
    (w : NumberField.InfinitePlace (PaperFmod D)) (hw : w.IsComplex) :
    ‖((paperFullLogKummerUQPeriod D).archimedeanLogShell w hw).period‖ =
      2 * Real.pi := by
  rw [paperFullLogKummerUQPeriod_period]
  exact norm_paperPeriod D w hw

/-- (b^arc): the actual closed unit ball O_k is contained in the package's
full log-shell at every complex place. -/
theorem paperFullLogKummerUQPeriod_unitBall_subset (D : S1895PaperInput)
    (w : NumberField.InfinitePlace (PaperFmod D)) (hw : w.IsComplex) :
    archimedeanUnitBall D w ⊆
      ((paperFullLogKummerUQPeriod D).archimedeanLogShell w hw).logShell := by
  rw [paperFullLogKummerUQPeriod_logShell]
  exact archimedeanUnitBall_subset_paperLogShell D w

/-- (c^arc) / log-link upper semi-commutativity: the compact unit group is
contained in the exponential image of the package's full log-shell. -/
theorem paperFullLogKummerUQPeriod_units_subset_exp (D : S1895PaperInput)
    (w : NumberField.InfinitePlace (PaperFmod D)) (hw : w.IsComplex) :
    archimedeanUnitSphere D w ⊆
      archimedeanExp D w ''
        ((paperFullLogKummerUQPeriod D).archimedeanLogShell w hw).logShell := by
  rw [paperFullLogKummerUQPeriod_logShell]
  exact archimedeanUnitSphere_subset_exp_paperLogShell D w hw

/-- The one-sidedness is genuine: the package's full log-shell is **not**
contained in the reduced unit ball, so it is not an S1927 reduced datum. -/
theorem paperFullLogKummerUQPeriod_logShell_not_subset_unitBall
    (D : S1895PaperInput) (w : NumberField.InfinitePlace (PaperFmod D))
    (hw : w.IsComplex) :
    Not (((paperFullLogKummerUQPeriod D).archimedeanLogShell w hw).logShell ⊆
      archimedeanUnitBall D w) := by
  rw [paperFullLogKummerUQPeriod_logShell]
  exact no_logShell_subset_unitBall D w hw (paperArchimedeanLogShellDatum D w hw)

/-- The full component of any period-carrying package cannot be the reduced
archimedean component of any S1927 package. -/
theorem S1969FullLogKummerUQPeriod.not_reduced_eq
    {D : S1895PaperInput} (P : S1969FullLogKummerUQPeriod D)
    (w : NumberField.InfinitePlace (PaperFmod D)) (hw : w.IsComplex) :
    Not (Exists fun R : ArchimedeanLogShellDatum D w =>
      R.logShell = (P.archimedeanLogShell w hw).logShell) :=
  not_reducedDatum_of_fullLogShell D hw (P.archimedeanLogShell w hw)

/-- The archimedean content of the period-carrying package, packaged: at every
complex infinite place the log-shell is the paper π-disk, the period is 2πi of
norm 2π, the fundamental segment is [-πi, πi], the unit ball is contained in
the log-shell, and the compact unit group is contained in its exponential
image. -/
theorem s1969_archimedean_content (D : S1895PaperInput)
    (w : NumberField.InfinitePlace (PaperFmod D)) (hw : w.IsComplex) :
    ((paperFullLogKummerUQPeriod D).archimedeanLogShell w hw).logShell =
        paperLogShell D w ∧
      ((paperFullLogKummerUQPeriod D).archimedeanLogShell w hw).period =
        paperPeriod D w hw ∧
      ‖((paperFullLogKummerUQPeriod D).archimedeanLogShell w hw).period‖ =
        2 * Real.pi ∧
      ((paperFullLogKummerUQPeriod D).archimedeanLogShell w hw).fundamentalSegment =
        paperFundamentalSegment D w hw ∧
      archimedeanUnitBall D w ⊆
        ((paperFullLogKummerUQPeriod D).archimedeanLogShell w hw).logShell ∧
      archimedeanUnitSphere D w ⊆
        archimedeanExp D w ''
          ((paperFullLogKummerUQPeriod D).archimedeanLogShell w hw).logShell :=
  ⟨rfl, rfl, paperFullLogKummerUQPeriod_period_norm D w hw, rfl,
    paperFullLogKummerUQPeriod_unitBall_subset D w hw,
    paperFullLogKummerUQPeriod_units_subset_exp D w hw⟩

/-! ## 4. Nonemptiness and the exact remaining input -/

/-- The period-carrying full log-Kummer package is inhabited for every S1895
paper input: its reduced component is S1958's package and its archimedean
component is the constructed S1954 family.  No archimedean input is missing. -/
theorem s1969FullLogKummerUQPeriod_inhabited (D : S1895PaperInput) :
    Nonempty (S1969FullLogKummerUQPeriod D) :=
  ⟨paperFullLogKummerUQPeriod D⟩

/-- The only remaining input of the period-carrying package is the Kummer
evaluation square: nonemptiness of the package is equivalent to nonemptiness of
S1927's square type.  The archimedean component no longer contributes an
input. -/
theorem s1969FullLogKummerUQPeriod_nonempty_iff_square
    (D : S1895PaperInput) :
    Nonempty (S1969FullLogKummerUQPeriod D) ↔
      Nonempty (S1927KummerEvaluationSquareActual D) := by
  constructor
  . rintro ⟨P⟩
    exact ⟨P.package.evaluationSquare⟩
  . rintro ⟨square⟩
    exact ⟨paperFullLogKummerUQPeriodOfSquare D square⟩

/-- The exact state after the archimedean integration: the complex-place
archimedean interface is inhabited, the period-carrying package is inhabited,
its reduced component is definitionally S1958's package, and its full
archimedean component is definitionally S1954's family. -/
theorem s1969_exact_state (D : S1895PaperInput) :
    Nonempty (S1927FirstMissingComplex D) ∧
      Nonempty (S1969FullLogKummerUQPeriod D) ∧
        (paperFullLogKummerUQPeriod D).archimedeanLogShell =
            paperArchimedeanLogShellComplex D ∧
          (paperFullLogKummerUQPeriod D).package = paperFullLogKummerUQ D :=
  ⟨s1927FirstMissingComplex_inhabited D,
    s1969FullLogKummerUQPeriod_inhabited D, rfl, rfl⟩

/-- The no-real-place boundary, packaged: a full paper datum is uninhabited at
every real place, the all-places family is empty whenever a real place exists,
and the all-places family exists exactly when every place is complex.  No real
place datum is asserted or fabricated. -/
theorem s1969_no_real_place_datum (D : S1895PaperInput) :
    (forall (w : NumberField.InfinitePlace (PaperFmod D)) (hreal : w.IsReal),
        Not (Nonempty (PaperArchimedeanLogShellDatum D w))) ∧
      (forall (w : NumberField.InfinitePlace (PaperFmod D)) (hreal : w.IsReal),
        Not (Nonempty ((w' : NumberField.InfinitePlace (PaperFmod D)) ->
          PaperArchimedeanLogShellDatum D w'))) ∧
        (Nonempty ((w : NumberField.InfinitePlace (PaperFmod D)) ->
            PaperArchimedeanLogShellDatum D w) ↔
          forall w : NumberField.InfinitePlace (PaperFmod D), w.IsComplex) :=
  ⟨fun w hreal => real_place_not_inhabited D w hreal,
    fun w hreal => not_nonempty_fullFamily_of_isReal D hreal,
    fullFamily_nonempty_iff_allComplex D⟩

/-! ## 5. Axiom probes -/

#print axioms S1927FirstMissingComplex
#print axioms paperArchimedeanLogShellComplex
#print axioms fullFamily_nonempty_iff_allComplex
#print axioms not_reducedDatum_of_fullLogShell
#print axioms S1969FullLogKummerUQPeriod
#print axioms paperFullLogKummerUQPeriodOfSquare
#print axioms paperFullLogKummerUQPeriod
#print axioms paperFullLogKummerUQPeriod_package
#print axioms paperFullLogKummerUQPeriod_period_norm
#print axioms s1969FullLogKummerUQPeriod_inhabited
#print axioms s1969FullLogKummerUQPeriod_nonempty_iff_square
#print axioms s1969_no_real_place_datum

end LeanFormal.IUT.XiFPaper.S1969ComplexArchimedeanUQActual
