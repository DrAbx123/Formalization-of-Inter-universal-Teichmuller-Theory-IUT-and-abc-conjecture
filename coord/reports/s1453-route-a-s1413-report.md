# S1453: Route A S1413 recheck and q-link report

## Compile recheck

Command: lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1413SourceKPlaceQComparisonActual.olean tmp/sheaf/xif/paper/S1413SourceKPlaceQComparisonActual.lean

Result: EXIT=-1, no diagnostics, no olean. This is a process-level failure
(the file is 445 lines, has no sorry); the kernel status of S1413 is therefore
UNVERIFIED. No consumer may import S1413 until it produces an olean.

S1413 source-level content inspected (not kernel-verified):
- sectionKPlace := kSidePlace (T:=T) b
- sectionFPlace := fkDescentShadow ... b.1
- sectionQ : FinitePlaceQCandidate (sectionKPlace T b)
- sectionQ_order : (sectionQ).order = eSource * (shadowQ).order
- valuation law and localLogMagnitude / orderNormalizedMagnitude laws
- kSideQVFamilySpecOfSection conditional on S1413ShadowEqualsNative and
  a TateCurveComparison at the section place
- SectionTwoLRoot exact missing root; two_l_dvd_order_of_root /
  l_dvd_ramification_of_root exact obstructions

## S605 link: exact first fields

S605 KSideQVComparisonData requires:

1. place_eq : qVFamilyKLift T b = kSidePlace T b
   S1413 does NOT prove this; it proves only conditional implications from
   hplace : qVFamilyKLift T b = sectionKPlace T b, and sectionKPlace is
   definitionally kSidePlace.  place_eq is an exact first field.

2. shadow_eq : fkDescentShadow ... b.1 = (nativeBadLift T).lift b
   This is exactly S1413ShadowEqualsNative T b; not proved in S1413.

3. qSection : FinitePlaceQCandidate (kSidePlace T b)
   qSection_eq : qSection = place_eq.symm ▸ qVFamilyK T b
   S1413 supplies sectionQ at the same place, but the equality
   sectionQ = qVFamilyK is NOT proved.  Exact candidate equality.

4. uniformization : TateCurveComparison (kSideCurve T) (kSidePlace T b) qSection
   Exact; S1413 only records S1413SectionTateUniformization as a Prop;
   no Tate comparison at a K-place exists in the tree.

5. order_eq : qSection.order = eSource * (qVFamily T b).order
   Derivable from S1413 sectionQ_order plus shadowQ_order_eq_of_shadow_eq
   and qSection_eq, but only after 2-4; not currently a standalone actual.

## Exact minimal chain

To construct S605 KSideQVComparisonData from the S1413 section q:
  (a) hplace : qVFamilyKLift T b = sectionKPlace T b
  (b) hF : S1413ShadowEqualsNative T b
  (c) hq : sectionQ T b = qVFamilyK T b at the same place (after (a))
  (d) uniformization : TateCurveComparison ... sectionQ
Then kSideQVFamilySpecOfComparison / kSideQVFamilyRequired follows.

## Verdict

Report-only: S1413 cannot be imported because it has no olean (EXIT=-1), so no
Lean bridge file S1453RoutAQLinkActual.lean was written.  Exact first fields
remain (a)-(d).  No fake bridge and no re-verification claim is made.