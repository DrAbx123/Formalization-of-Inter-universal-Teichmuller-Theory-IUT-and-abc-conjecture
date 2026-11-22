# S1969: period-carrying archimedean component of the full log-Kummer package

Date: 2026-11-01.
Source: tmp/sheaf/xif/paper/S1969ComplexArchimedeanUQActual.lean
Olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S1969ComplexArchimedeanUQActual.olean
Consumer: tmp/sheaf/xif/paper/_S1969Consumer.lean

## Verification

- Build command (plain check):
  lake env lean tmp/sheaf/xif/paper/S1969ComplexArchimedeanUQActual.lean
  EXIT=0, no errors, no warnings.
- Olean build command:
  lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1969ComplexArchimedeanUQActual.olean tmp/sheaf/xif/paper/S1969ComplexArchimedeanUQActual.lean
  EXIT=0, no errors, no warnings.
- Source: 23077 bytes, 462 lines,
  SHA256 893168270BF05D0EEB4811E384486E5D1DF327E09F17C64F916FBB07F96A2B3C.
- Olean: 144976 bytes,
  SHA256 8079A61A2A1076B9196AE27DF08E90F14E50931444C05F4883B56897FC883074.
- Import re-check: EXIT=0 (scratch module _S1969Consumer.lean imports the built
  olean; its #checks report exactly the intended signatures and its examples
  use the new interface, the definitional S1958 attachment and the real-place
  boundary). Consumer olean 3824 bytes, SHA256
  293DED2291C61032EF0616F288A22AD1E85076AE0C246B6A1E09A41338E98DA4.
- Axiom audit (#print axioms on 12 main declarations): only
  [propext, Classical.choice, Quot.sound].  No sorryAx, no axiom declaration.
- Source scan: no sorry/admit tactic and no axiom declaration; the only
  occurrences of those words are in the honesty paragraph and the
  #print axioms probe section.
- Imports: only S1954ArchimedeanPeriodActual and S1958FullLogKummerUQActual.
- Project automation (tools/lean_auto.py repair) was not run to completion in this
  session (harness deadline under concurrent Lean builds of other packages); the
  direct lake env lean checks above are the recorded evidence.

## What is integrated

1. S1927FirstMissingComplex (D : S1895PaperInput) : Type :=
     (w : InfinitePlace (PaperFmod D)) -> (hw : w.IsComplex) ->
       PaperArchimedeanLogShellDatum D w
   This is the paper-faithful archimedean interface: the S1954 full,
   period-carrying datum indexed by the complex infinite places only.
   It is inhabited for every D by paperArchimedeanLogShellComplex D, which
   is literally (fun w hw => paperArchimedeanLogShellDatum D w hw), so no
   field is fitted.  No real-place datum is produced.

2. paperFullLogKummerUQPeriod (D) : S1969FullLogKummerUQPeriod D, the
   period-carrying full log-Kummer package on 1,circ U_Q.  Its fields are
     package : S1927FullLogKummerUQ D            (the S1958 reduced package)
     archimedeanLogShell : S1927FirstMissingComplex D  (the S1954 family)
     reducedLogShell_subset : at each complex w, the reduced S1927 log-shell
       is contained in the full log-shell (paper (b^arc), O_k subset I_k).
   The canonical inhabitant is paperFullLogKummerUQPeriod D =
   paperFullLogKummerUQPeriodOfSquare D (s1927Square D).

3. Definitional component identifications (all proved by rfl, so they are
   identities, not merely equal-up-to-proof):
   - (paperFullLogKummerUQPeriod D).package = paperFullLogKummerUQ D
     (the S1958 package, hence its one-column structure, (1,0) label, finite
     log-shell packet and Kummer-evaluation square are S1958's);
   - .archimedeanLogShell = paperArchimedeanLogShellComplex D;
   - .toS1927FullLogKummerUQ.archimedeanLogShell = paperArchimedeanLogShell D
     (the S1950 closed unit ball; the reduced slot cannot take the full datum);
   - .package.evaluationSquare = s1927Square D and
     .package.evaluationSquare.square = kummerEvaluationSquare D.

4. Componentwise paper content at every complex infinite place w:
   logShell = paperLogShell D w = {x | norm x <= pi}; period = paperPeriod
   = 2*pi*i with norm 2*pi; fundamentalSegment = paperFundamentalSegment =
   [-pi*i, pi*i]; unit ball subset logShell ((b^arc)); unit sphere subset
   exp '' logShell ((c^arc), upper semi-commutativity).  Also the log-shell
   is NOT contained in the plain unit ball, i.e. it is not an S1927 reduced
   datum, and no reduced datum has the same log-shell.

5. Input accounting:
   Nonempty (S1969FullLogKummerUQPeriod D) <->
     Nonempty (S1927KummerEvaluationSquareActual D),
   and Nonempty (S1969FullLogKummerUQPeriod D) holds outright.  The
   archimedean component contributes no remaining input.

6. Real-place boundary (no fake datum):
   - at a real w, the full datum is uninhabited: not Nonempty
     (PaperArchimedeanLogShellDatum D w);
   - an all-infinite-places full family is empty whenever a real place
     exists;
   - an all-infinite-places full family exists iff every infinite place is
     complex (the S1954 sqrt(-1) hypothesis, formally characterized).

## Exact remaining first missing

The remaining paper-level missing is NOT a proposition.  The square carried
by the period-carrying package is the S1951 reduced square on the four actual
source F-prime-strips envStrip, gauStrip, lgpStrip, lgpLowerStrip (S1969's
s1969_square_corners identifies them definitionally).  The paper's four coric
vertices F_env, F_gau, F_LGP, F_lgp are missing DEFINITIONS: the tree has no
F-paper-strip carrier, no theta monoid and no Gaussian monoid, so the
vertices cannot be stated, and neither can the operation-level Kummer
isomorphism of IUT II, Definition 4.9, (i), the evaluation isomorphism of
IUT II, Corollary 4.10, (ii), or the q-pilot anchor identification (R6).
S1959 records this gap precisely (including that the four source strips come
from four distinct Hodge theaters, while the paper's vertices come from one
Theta-ellNF-Hodge theater).  S1969 does not replace, encode, or fake any of
these objects.

## Honest boundary

No sorry, admit, axiom, arbitrary inhabitant, empty type, PUnit slot or fake
real-place datum.  The file does not claim that the reduced source-strip
square is the paper's coric square: its own reductions are recorded as
componentwise identifications above, exactly enough to expose the remaining
definition gap.  The S1927 reduced archimedean slot still holds the S1950
unit ball, which is correct for that interface; the paper datum lives in the
new complex-place slot because S1954 proves the two cannot coincide.

## Next executable step

Consumer-facing packages (the S1960 QPilot anchor, the S1959 vertex layer)
can now take S1969FullLogKummerUQPeriod D as their full log-Kummer component
and read the paper archimedean data off .archimedeanLogShell.  The next
paper-level construction is the F-paper-prime-strip carrier (and PsiFenv)
needed to define the four coric vertices; until it exists, the
operation-level Kummer and evaluation arrows and R6 remain definitions, not
propositions.
