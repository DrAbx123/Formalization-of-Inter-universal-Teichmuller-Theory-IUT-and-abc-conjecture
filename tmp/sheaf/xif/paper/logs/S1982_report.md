# S1982: the l = 5 instance of D5 (S1906Separability 5 + S1725RankTwoBasisGap 5)

Date: 2026-11-01.
Source: tmp/sheaf/xif/paper/S1982D5FiveActual.lean
Olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S1982D5FiveActual.olean
Consumer: tmp/sheaf/xif/paper/_S1982Consumer.lean
Build log: tmp/sheaf/xif/paper/logs/S1982_build.log
Consumer log: tmp/sheaf/xif/paper/logs/S1982_consumer.log

## Verification

- Build command (full elaboration + olean):
  lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1982D5FiveActual.olean tmp/sheaf/xif/paper/S1982D5FiveActual.lean
  EXIT=0, no errors, no warnings.
- Source: 13447 bytes, 301 lines,
  SHA256 7EA790BCA2B52711A0036C77BF4DBA40C22E12A5EA3762432CF0CDB9A82D65D0.
- Olean: 80888 bytes,
  SHA256 16709AB9B620D62C750B70E5C9E2F378838810E37FA4455D048088734AC75D21.
- Import re-check: EXIT=0.  The scratch module _S1982Consumer.lean imports the
  built olean and #checks the main declarations; it reports exactly the expected
  types (S1906Separability S1982Five, S1725RankTwoBasisGap S1982Five,
  Nat.card (S1720Curve.LTorsion S1982Five) = 25,
  Module.finrank (ZMod S1982Five.value) (...) = 2,
  S1982D5ExactFirstMissing : Prop,
  S1982SourceTorsionClause_five (h : S1982D5ExactFirstMissing) :
    SourceTorsionClause.{0, 0, 0} S1982Five).
- Axiom audit (#print axioms on 17 main declarations): only
  [propext, Classical.choice, Quot.sound].  No sorryAx, no axiom declaration,
  no opaque.
- Source scan: no sorry/admit tactic and no axiom/opaque declaration; the only
  occurrence of those words is the honesty sentence in the header.
- Imports: S1942PrePsiFiveActual, S1933PrePsiSeparableActual,
  S1924ZeroCriterionActual, S1906RankTwoTorsionActual (the four requested; the
  first already pulls the rest), plus S1894D5LargeImageActual.  S1894 is used
  only to state the exact decomposition of the D5 image input into the
  rank-two part and the basis-free large-image part.

## What is proved unconditionally at l = 5

1. S1982W_isElliptic : S1906W.IsElliptic.  S1906W is E' base changed to
   AlgebraicClosure F'; the instance is Mathlib's base-change instance for
   IsElliptic, made explicit at the concrete curve.

2. S1982Separability_five : S1906Separability S1982Five, i.e.
   (S1906W.preΨ 5).Separable.  Proof: transport S1942Certificate_five through
   S1933separable_of_certificate to S1906W.  (S1982Separability_five_direct is
   the same statement via S1942_preΨ_five_separable.)

3. S1982RootCount_five : S1906RootCount S1982Five, via
   S1906RootCount_of_separable.

4. S1982RankTwoBasisGap_five : S1725RankTwoBasisGap S1982Five, via
   S1924S1906BasisGap_of_separable.  This is the rank-two freeness of the
   actual E'[5].

5. S1982S1906ExactFirstMissing_five : S1906ExactFirstMissing S1982Five, and
   S1982NatCard_LTorsion_five : Nat.card (S1720Curve.LTorsion S1982Five) = 25,
   S1982Finrank_five : Module.finrank (ZMod 5) E'[5] = 2,
   S1982FiniteFreeRankTwo_five : E'[5] is a finite free ZMod 5-module of rank
   two, and S1982Basis : S1725TorsionBasis S1982Five, an actual rank-two
   ZMod 5-basis extracted from the nonempty type of bases.

6. The arithmetic side of D5 at l = 5 (all from S1725/S1724/S1720):
   S1982D5Place_five : S1725D5Place 5 = S1720PlaceAboveSeven;
   S1982D5Place_residueCharacteristic_five : residue characteristic 7;
   S1982SplitAtPlace_five : split multiplicative reduction at that place;
   S1982LTorsionCompatible_five : Nat.Coprime 5 7 (Definition 3.1(c) half);
   S1982SixTorsionIndependent : Torsion23Rational E' (paper condition (b)).

## The D5 clause at l = 5 and the exact remaining input

The actual clause is S1725SourceTorsionClause 5 hI with
hI : S1725ImageContainsSL2 5.  S1894 proves

  S1725ImageContainsSL2 l <-> S1725RankTwoBasisGap l
                              AND S1894LargeImageInput l
  (S1894ImageContainsSL2_iff_forall_of_basisGap / S1894ImageContainsSL2_iff),

where S1894LargeImageInput 5 is the basis-free condition
forall b : S1725TorsionBasis 5, S1725ImageTail 5 b, equivalently the frozen
SerreStyleLargeImageStatement S1720Curve 5.  Since the rank-two half is item 4
above, the exact first missing input at l = 5 is

  S1982D5ExactFirstMissing := S1894LargeImageInput S1982Five,

with the machine-checked equivalences

  S1982D5ExactFirstMissing_iff_imageContainsSL2 :
    S1982D5ExactFirstMissing <-> S1725ImageContainsSL2 S1982Five,
  S1982D5ExactFirstMissing_iff_tail :
    S1982D5ExactFirstMissing <-> S1725ImageTail S1982Five S1982Basis,
  S1982D5ExactFirstMissing_iff_serre :
    S1982D5ExactFirstMissing <-> SerreStyleLargeImageStatement S1720Curve S1982Five,
  S1982S1894ExactMissing_iff :
    S1894ExactMissing S1982Five <-> S1982D5ExactFirstMissing.

The actual clause is constructed from exactly that input:

  S1982SourceTorsionClause_five (h : S1982D5ExactFirstMissing) :
    SourceTorsionClause.{0, 0, 0} S1982Five

built with S1725SourceTorsionClause.  Its fields are the actual objects:
the image field is S1725ImageContainsSL2 5 (rfl), the torsion carrier is the
literal mu_6 of AlgebraicClosure F' (rfl), the six-torsion field is
Torsion23Rational E' (rfl), and the l-compatibility field is the actual
residue-characteristic condition (rfl); S1982SourceTorsionClause_five_fields
packages the three source-clause fields.  S1982SourceTorsionClause_five_of_tail
builds the same clause from the single-basis tail witness.

## Exact first missing, stated precisely

S1894LargeImageInput 5, equivalently S1725ImageContainsSL2 5, equivalently
SerreStyleLargeImageStatement (S1720Curve) (PrimeGeFive at 5): for (every / some)
rank-two ZMod 5-basis of E'[5], SL_2(F_5) is contained in the image of the
actual mod-5 Galois representation.  This is the open Serre-style large-image
statement for E'/F'; it is not derivable from rank-two freeness, and no proof
of it is supplied or assumed here.  Consequently no unconditional inhabitant of
SourceTorsionClause.{0,0,0} 5 is claimed: the paper clause requires the
image proof as a field, and S1725SourceTorsionClause is used only with the
explicit hypothesis.

## Honest boundary

No sorry, no admit, no new axiom, no opaque, no placeholder, no fake clause and
no arbitrary basis: S1982Basis is Classical.choice of the proved Nonempty type.
The rank-two and separability parts are unconditional; the large-image part is
a named Prop with no inhabitant asserted.  No change of target: S1906Separability
and S1725RankTwoBasisGap are used exactly as defined; S1906W/S1906K/S1720Curve
are the actual S1906/S1720 objects.

## Next executable step

Attack S1982D5ExactFirstMissing (Serre large image for the actual E'/F' at 5),
or reduce it to a finite/analytic input for this specific curve.  Until then the
l = 5 D5 status is: rank-two and separability CLOSED, large image OPEN, and the
clause is available conditionally on exactly that open statement.
