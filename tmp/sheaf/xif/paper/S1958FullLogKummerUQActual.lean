import tmp.sheaf.xif.paper.S1950ArchimedeanLogShellActual
import tmp.sheaf.xif.paper.S1951KummerEvaluationSquareActual

/-!
# S1958: the actual full log-Kummer package on 1,circ U_Q

S1927 parameterized its full log-Kummer package on 1,circ U_Q by two named
inputs:

  archimedeanLogShell : S1927FirstMissing D
  evaluationSquare    : S1927KummerEvaluationSquareActual D

S1950 constructed the first input for every S1895PaperInput D, as
paperArchimedeanLogShell D: at every infinite place w of Fmod it is the actual
closed unit ball of the actual completion w.Completion, with the actual
compact-convex structure.  S1951 constructed the second input, as s1927Square D:
the four actual source F-prime-strips envStrip, gauStrip, lgpStrip,
lgpLowerStrip, and the reduced Kummer-evaluation square built by the paper's
conjugation instruction.

This file performs the assembly, using only those actual objects:

* paperFullLogKummerUQ D : S1927FullLogKummerUQ D is the actual inhabitant,
  obtained as
  s1927FullLogKummerUQ_of_missing D (paperArchimedeanLogShell D) (s1927Square D);
* s1927FullLogKummerUQ_inhabited D : Nonempty (S1927FullLogKummerUQ D) for
  every S1895 paper input D;
* every field of the inhabitant is tied to its actual source: the archimedean
  datum is paperArchimedeanLogShell D (the actual closed unit ball at each
  infinite place), the square is s1927Square D (actual source strips), the
  finite log-shell is paperGlobalLogShellPacket, and the one-column structure
  and (1,0) label are exactly the data of the paper O object S1895PaperO D
  (label carrier, n = 1, m = 0).

Thus S1927's reduced full log-Kummer package is no longer conditional on any
missing Lean datum: Nonempty (S1927FullLogKummerUQ D) holds outright.

## The exact remaining missing

The inhabitant assembled here lives on the *reduced* interface.  The
paper-level objects that are still not defined in the tree are, exactly:

1. the paper's four coric vertices F_env, F_gau, F_LGP, F_lgp
   (SourceKummerEvaluationArrows, R3);
2. the operation-level Kummer isomorphism of IUT II, Definition 4.9, (i), and
   the evaluation isomorphism of IUT II, Corollary 4.10, (ii), on those
   vertices;
3. the q-pilot anchor identification (R6).

These are missing *definitions*, not propositions, and S1951 records them in
its section 5.  This file neither asserts nor replaces them: the four corners
used here are the actual source strips and no theorem says that they are the
paper vertices.  The inhabitant below is therefore a genuine inhabitant of the
reduced S1927 interface; the assertion that the paper's full log-Kummer package
itself has been constructed is *not* made.

## Honesty note

No sorry, admit, axiom, arbitrary inhabitant or empty-carrier device is used.
The classical inputs are exactly those already carried by S1950 and S1951
(propext, Classical.choice, Quot.sound); see the axiom probes at the end of the
file.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.S1958FullLogKummerUQActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual
open LeanFormal.IUT.XiFPaper.S1950ArchimedeanLogShellActual
open LeanFormal.IUT.XiFPaper.S1951KummerEvaluationSquareActual

/-! ## 1. The assembled actual package -/

/-- The actual full log-Kummer package on 1,circ U_Q: S1927's structure
populated by the actual archimedean log-shell family of S1950 at every
infinite place and by the actual Kummer-evaluation square of S1951 on the four
actual source strips. -/
noncomputable def paperFullLogKummerUQ (D : S1895PaperInput) :
    S1927FullLogKummerUQ D :=
  fullLogKummerUQ D (paperArchimedeanLogShell D)

/-- The assembled package is exactly S1950's assembly at S1951's square. -/
theorem paperFullLogKummerUQ_eq_assembly (D : S1895PaperInput) :
    paperFullLogKummerUQ D =
      paperFullLogKummerUQOfKummerSquare D (s1927Square D) := rfl

/-- The archimedean component of the package is the actual S1950 log-shell
family, i.e. the actual closed unit ball at every infinite place. -/
theorem paperFullLogKummerUQ_archimedeanLogShell (D : S1895PaperInput) :
    (paperFullLogKummerUQ D).archimedeanLogShell =
      paperArchimedeanLogShell D := rfl

/-- The square component of the package is the actual S1951 square on the four
actual source strips. -/
theorem paperFullLogKummerUQ_evaluationSquare (D : S1895PaperInput) :
    (paperFullLogKummerUQ D).evaluationSquare = s1927Square D := rfl

/-- The finite log-shell component is the constructed global packet. -/
theorem paperFullLogKummerUQ_finiteLogShell (D : S1895PaperInput) :
    (paperFullLogKummerUQ D).finiteLogShell = paperGlobalLogShellPacket := rfl

/-- The one-column structure component is the paper O object's one-column
structure. -/
theorem paperFullLogKummerUQ_oneColumn (D : S1895PaperInput) :
    (paperFullLogKummerUQ D).oneColumn = (S1895PaperO D).oneColumn := rfl

/-- The label component is the paper O object's actual (1,0) label. -/
theorem paperFullLogKummerUQ_label (D : S1895PaperInput) :
    (paperFullLogKummerUQ D).label = s1895PaperO_oneColumnLabel D := rfl

/-! ## 2. The target: nonemptiness of the actual package -/

/-- S1927's full log-Kummer package on 1,circ U_Q is inhabited for every S1895
paper input, by actual objects (no missing input remains at the reduced
interface). -/
theorem s1927FullLogKummerUQ_inhabited (D : S1895PaperInput) :
    Nonempty (S1927FullLogKummerUQ D) :=
  ⟨paperFullLogKummerUQ D⟩

/-- Nonemptiness of the full package is equivalent to nonemptiness of the
Kummer-evaluation square, both sides being actual here. -/
theorem s1927FullLogKummerUQ_nonempty_iff_kummerSquare
    (D : S1895PaperInput) :
    Nonempty (S1927FullLogKummerUQ D) ↔
      Nonempty (S1927KummerEvaluationSquareActual D) :=
  paperFullLogKummerUQ_nonempty_iff_kummerSquare_nonempty D

/-- The Kummer-evaluation square component is inhabited at the actual source
strips. -/
theorem s1927KummerEvaluationSquare_inhabited (D : S1895PaperInput) :
    Nonempty (S1927KummerEvaluationSquareActual D) :=
  s1927Square_nonempty D

/-! ## 3. Attachment to the S1895 paper O object

The full package is not merely nonempty: its (1,0) data are definitionally the
paper O object's data.  This is the interface the package must have to sit over
S1895PaperO. -/

/-- The label's carrier is exactly the package's one-column structure. -/
theorem paperFullLogKummerUQ_label_carrier (D : S1895PaperInput) :
    (paperFullLogKummerUQ D).oneColumn =
      (s1895PaperO_oneColumnLabel D).carrier := by
  rw [s1895PaperO_oneColumnLabel_carrier]
  exact paperFullLogKummerUQ_oneColumn D

/-- The label is the n = 1 label. -/
theorem paperFullLogKummerUQ_label_n (D : S1895PaperInput) :
    (paperFullLogKummerUQ D).label.n = 1 := by
  rw [paperFullLogKummerUQ_label]
  exact s1895PaperO_oneColumnLabel_n D

/-- The label is the m = 0 label. -/
theorem paperFullLogKummerUQ_label_m (D : S1895PaperInput) :
    (paperFullLogKummerUQ D).label.m = 0 := by
  rw [paperFullLogKummerUQ_label]
  exact s1895PaperO_oneColumnLabel_m D

/-- The assembled actual package, attached to the paper O object: its
one-column structure and label are the paper object's, the label's carrier is
the package's one-column, and its finite log-shell is the global packet. -/
theorem paperFullLogKummerUQ_attached_to_paperO (D : S1895PaperInput) :
    (paperFullLogKummerUQ D).oneColumn = (S1895PaperO D).oneColumn ∧
      (paperFullLogKummerUQ D).label = s1895PaperO_oneColumnLabel D ∧
      (paperFullLogKummerUQ D).oneColumn =
        (s1895PaperO_oneColumnLabel D).carrier ∧
      (paperFullLogKummerUQ D).finiteLogShell =
        paperGlobalLogShellPacket :=
  ⟨rfl, rfl, paperFullLogKummerUQ_label_carrier D, rfl⟩

/-- There is an actual inhabitant of S1927's package whose every component is
identified with its source object: the S1950 archimedean family, the S1951
square and the S1895 paper O data. -/
theorem exists_paperFullLogKummerUQ_attached (D : S1895PaperInput) :
    Exists fun P : S1927FullLogKummerUQ D =>
      P.oneColumn = (S1895PaperO D).oneColumn ∧
        P.label = s1895PaperO_oneColumnLabel D ∧
        P.archimedeanLogShell = paperArchimedeanLogShell D ∧
        P.evaluationSquare = s1927Square D :=
  ⟨paperFullLogKummerUQ D, rfl, rfl, rfl, rfl⟩

/-! ## 4. The archimedean content of the package is the actual unit ball -/

/-- At every infinite place, the package's log-shell is the actual closed unit
ball of the actual completion. -/
theorem paperFullLogKummerUQ_logShell_eq_closedBall
    (D : S1895PaperInput)
    (w : NumberField.InfinitePlace (PaperFmod D)) :
    ((paperFullLogKummerUQ D).archimedeanLogShell w).logShell =
      Metric.closedBall (0 : w.Completion) 1 := by
  rw [paperFullLogKummerUQ_archimedeanLogShell]
  exact paperArchimedeanLogShell_logShell_eq_closedBall D w

/-! ## 5. Axiom probes -/

#print axioms paperFullLogKummerUQ
#print axioms paperFullLogKummerUQ_eq_assembly
#print axioms s1927FullLogKummerUQ_inhabited
#print axioms paperFullLogKummerUQ_attached_to_paperO
#print axioms exists_paperFullLogKummerUQ_attached
#print axioms paperFullLogKummerUQ_logShell_eq_closedBall

end LeanFormal.IUT.XiFPaper.S1958FullLogKummerUQActual
