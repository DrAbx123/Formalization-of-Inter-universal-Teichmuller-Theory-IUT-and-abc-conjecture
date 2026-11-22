/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
-/
import tmp.sheaf.xif.paper.S1982D5FiveActual

/-!
# S1987: the l = 5 D5 large-image input on the actual curve E'/F'

## The target

S1982 performed the l = 5 specialization of the D5 arithmetic on the actual
curve E' = S1720Curve over the actual number field F' = S1720Field:

* S1982Separability_five (the S1942 certificate at n = 5);
* S1982RankTwoBasisGap_five (E'[5] is ZMod-5-free of rank two);
* S1982NatCard_LTorsion_five (Nat.card E'[5] = 25), S1982Finrank_five,
  S1982FiniteFreeRankTwo_five, and the actual basis S1982Basis;
* the bad place above 7 with split multiplicative reduction and odd residue
  characteristic 7 (S1982D5Place_five, S1982SplitAtPlace_five,
  S1982LTorsionCompatible_five).

The only remaining input of the paper's D5 clause at l = 5 is the basis-free
large-image condition

  S1894LargeImageInput 5
  = for every rank-two ZMod-5-basis b of the actual E'[5],
    SL_2(F_5) <= range (rho_{5,b}),

also named S1982D5ExactFirstMissing in S1982.  This file gives it its own
name, S1987D5LargeImageFive, proves that it is equivalent to the tail
condition at *any single* actual basis (in particular at S1982Basis), to the
frozen SerreStyleLargeImageStatement E' 5, to the determinant-one form, and
to the missing statement of S1894.  It also builds the actual S1725 D5 clause
from the input, and records a sufficient condition (range = top in one basis).

## Status of the target: MISSING in the kernel-checked tree

Nothing in this file, in S1982, in S1894, in S1725, in Mathlib or elsewhere in
the tree proves S1987D5LargeImageFive.  No inhabitant of the target, of
S1725ImageContainsSL2 5, or of the D5 clause is produced.  No sorry, axiom,
opaque declaration, True/PUnit gate, Nonempty gate or arbitrary inhabitant is
used: the file is an exact-missing endpoint, not a fake proof.

The arithmetic data of D5 does not yield the image statement.  In particular
the tree's "nine-point injection" S1708 is the count Nat.card E[3] = 9 of
condition (b) (six 3-torsion y-coordinates plus P and -P); it says nothing about
the mod-5 Galois image.  Likewise the actual split multiplicative reduction at
the place above 7 and the odd residue characteristic 7 give local data, but the
tree has no Tate-uniformization/Weil-pairing interface that would turn them
into mod-5 matrices.  Consequently no proof of the target is derivable from
the currently formalized arithmetic.

## A human proof that the target is TRUE (not formalized here)

The mathematical statement itself is not open for this particular curve.  The
companion report coord/reports/S1987-d5-large-image-five-actual.md records the
following proof, whose only non-formal inputs are finite, explicit
computations (two modular polynomial computations over F_13 and F_29, plus the
explicit 480-element subgroup enumeration of GL_2(F_5); scripts in tmp/s1987/):

1. The odd 5-division polynomial psi_5 of E = S1667Curve has degree 12 and is
   irreducible over Q.  Certificate: its primitive integer form
   2^36 * psi_5 is irreducible modulo 13 (degree 12; squarefree).  Hence the
   mod-5 image G <= GL_2(F_5) over Q acts transitively on the 12 pairs
   {P, -P} (P in E[5] minus {0}).
2. Modulo 29 the same polynomial factors, squarefree, as an irreducible
   quadratic times an irreducible degree-10 factor; so the Frobenius at 29 has
   cycle type (10,2) on the 12 pairs.
3. det G = (Z/5)^*: the determinant of the mod-5 representation is the
   cyclotomic character (Weil pairing), so Q(zeta_5) lies in the 5-division
   field.
4. Dickson's maximal-subgroup list for GL_2(F_5), checked explicitly: the
   proper subgroups with surjective determinant and a transitive action on the
   12 pairs are exactly the preimages of S_4 (order 96) and of S_3 x C_2
   (order 48); the Borel (order 80) is not transitive, and the preimage of
   A_5 (order 240) has determinant image the squares.  Neither order-96 nor
   order-48 preimage contains an element of cycle type (10,2).  Hence
   G = GL_2(F_5).
5. F' = SplittingField (S1687H * (X^2 + 1)) is Galois over Q with group
   S_3 x C_2; its quadratic subfields are Q(sqrt(-3)), Q(sqrt(3)) and Q(i).
   The only quadratic subfield of the 5-division field is Q(sqrt(5)), because
   det^2 is the only nontrivial quadratic character of GL_2(F_5).  Therefore
   F' cap Q(E[5]) = Q, the mod-5 image over F' is the full mod-5 image over Q,
   and SL_2(F_5) <= G = GL_2(F_5).

So the exact *formal* first missing is the bridge from these finite
certificates to galoisLTorsionMatrixRepresentation (Dedekind factorization,
the division-field/Galois correspondence, the subgroup classification of
GL_2(F_5), and the Galois group of F'/Q).  None of that is asserted in Lean in
this file.

## What this file proves

* S1987D5LargeImageFive is literally S1982D5ExactFirstMissing
  (S1987D5LargeImageFive_iff_S1982);
* it is equivalent to the tail at any actual basis
  (S1987D5LargeImageFive_iff_tail), in particular S1982Basis;
* it is equivalent to S1725ImageContainsSL2 5
  (..._iff_imageContainsSL2) and to the frozen Serre statement
  (..._iff_serre);
* it is equivalent to the determinant-one containment for every basis
  (..._iff_detKer) and to S1894ExactMissing 5
  (..._iff_S1894ExactMissing);
* range = top in one basis is sufficient (..._of_fullRange);
* the actual S1725 D5 clause is reconstructed from the input, with its image
  field recognised (S1987SourceTorsionClause and its field lemmas).

All declarations depend only on propext, Classical.choice and Quot.sound; see
the axiom footprint at the end.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual
open LeanFormal.IUT.XiFPaper.S1924ZeroCriterionActual
open LeanFormal.IUT.XiFPaper.S1933PrePsiSeparableActual
open LeanFormal.IUT.XiFPaper.S1942PrePsiFiveActual
open LeanFormal.IUT.XiFPaper.S1894D5LargeImageActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.InitialThetaSource.TorsionCarrierReduction


/-! ## 0. The prime label and the exact target -/

/-- The prime label l = 5 of the actual D5 instance (S1982). -/
abbrev S1987Five : PrimeGeFive := S1982Five

/-- The exact remaining large-image input at l = 5, in the actual curve and
the actual rank-two bases of E'[5].  This is definitionally
S1982D5ExactFirstMissing. -/
def S1987D5LargeImageFive : Prop := S1894LargeImageInput S1987Five

/-- The same target, named as the exact first missing statement. -/
abbrev S1987D5ExactFirstMissing : Prop := S1987D5LargeImageFive

/-! ## 1. The target is the S1982 missing input -/

/-- The target is literally the S1982 exact first missing statement. -/
theorem S1987D5LargeImageFive_iff_S1982 :
    S1987D5LargeImageFive ↔ S1982D5ExactFirstMissing :=
  Iff.rfl

/-- The target is literally the S1894 missing statement at l = 5, read after
the rank-two half has been discharged in S1982. -/
theorem S1987D5LargeImageFive_iff_S1894ExactMissing :
    S1987D5LargeImageFive ↔ S1894ExactMissing S1987Five :=
  S1982S1894ExactMissing_iff.symm

/-! ## 2. Equivalent forms of the exact missing input -/

/-- The target is the existential-basis form S1725ImageContainsSL2 5: by S1894
the basis quantifier carries no extra content once a rank-two basis exists,
and S1982 constructs one. -/
theorem S1987D5LargeImageFive_iff_imageContainsSL2 :
    S1987D5LargeImageFive ↔ S1725ImageContainsSL2 S1987Five :=
  S1982D5ExactFirstMissing_iff_imageContainsSL2

/-- **The target is the tail condition at any single actual basis.**  This is
the sharpest basis-level form of the exact missing input: it is enough to
prove the containment for the fixed actual basis S1982Basis (or for any other
one), by S1894's basis-independence. -/
theorem S1987D5LargeImageFive_iff_tail (b : S1725TorsionBasis S1987Five) :
    S1987D5LargeImageFive ↔ S1725ImageTail S1987Five b := by
  constructor
  · intro h
    exact h b
  · intro h b'
    exact (S1894ImageTail_congr S1987Five b' b).mpr h

/-- The target at the actual S1982 basis. -/
theorem S1987D5LargeImageFive_iff_tail_basis :
    S1987D5LargeImageFive ↔ S1725ImageTail S1987Five S1982Basis :=
  S1987D5LargeImageFive_iff_tail S1982Basis

/-- The target is the frozen Serre-style large-image statement for E'. -/
theorem S1987D5LargeImageFive_iff_serre :
    S1987D5LargeImageFive ↔ SerreStyleLargeImageStatement S1720Curve S1987Five :=
  S1982D5ExactFirstMissing_iff_serre

/-- The target is the determinant-one containment form: it says that for every
rank-two basis the range contains all determinant-one matrices.  This is the
literal SL_2(F_l) <= im rho statement. -/
theorem S1987D5LargeImageFive_iff_detKer :
    S1987D5LargeImageFive ↔
      ∀ b : S1725TorsionBasis S1987Five,
        (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := ZMod S1987Five.value)).ker ≤
          (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range :=
  S1894LargeImageInput_iff_detKer S1987Five

/-! ## 3. A sufficient condition in the tree's existing vocabulary -/

/-- If the actual mod-5 matrix representation is all of GL_2(F_5) in one
rank-two basis, then the exact missing input holds.  This records the only
known formal sufficient condition; it is not asserted. -/
theorem S1987D5LargeImageFive_of_fullRange (b : S1725TorsionBasis S1987Five)
    (h : (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range = ⊤) :
    S1987D5LargeImageFive :=
  (S1987D5LargeImageFive_iff_imageContainsSL2).mpr
    (S1894ImageContainsSL2_of_fullRange S1987Five b h)


/-! ## 4. The actual D5 clause built from the exact missing input -/

/-- The actual S1725 Definition 3.1(c) clause at l = 5, constructed from the
single remaining input.  Every field is the actual S1720/S1721/S1724/S1725
object; the image field is the large-image input, exposed and not hidden. -/
noncomputable def S1987SourceTorsionClause (h : S1987D5LargeImageFive) :
    SourceTorsionClause.{0, 0, 0} S1987Five :=
  S1982SourceTorsionClause_five h

/-- The three source-clause fields of the reconstructed l = 5 clause. -/
theorem S1987SourceTorsionClause_fields (h : S1987D5LargeImageFive) :
    (S1987SourceTorsionClause h).imageContainsSL2 ∧
      (S1987SourceTorsionClause h).sixTorsionIndependent ∧
      (S1987SourceTorsionClause h).lTorsionCompatible :=
  S1982SourceTorsionClause_five_fields h

/-- The image field of the reconstructed clause is the actual large-image
input, not a placeholder. -/
@[simp] theorem S1987SourceTorsionClause_imageContainsSL2
    (h : S1987D5LargeImageFive) :
    (S1987SourceTorsionClause h).imageContainsSL2 =
      S1725ImageContainsSL2 S1987Five :=
  S1982SourceTorsionClause_five_imageContainsSL2 h

/-- The torsion carrier of the reconstructed clause is the literal mu_6. -/
@[simp] theorem S1987SourceTorsionClause_torsionCarrier
    (h : S1987D5LargeImageFive) :
    (S1987SourceTorsionClause h).torsionCarrier = S1725SixTorsionCarrier :=
  S1982SourceTorsionClause_five_torsionCarrier h

/-- The six-torsion field of the reconstructed clause is the S1724 theorem. -/
@[simp] theorem S1987SourceTorsionClause_sixTorsionIndependent
    (h : S1987D5LargeImageFive) :
    (S1987SourceTorsionClause h).sixTorsionIndependent =
      PuncturedEllipticCurve.Torsion23Rational S1720Curve :=
  S1982SourceTorsionClause_five_sixTorsionIndependent h

/-- The l-compatibility field of the reconstructed clause is the actual
residue-characteristic condition at the place above 7. -/
@[simp] theorem S1987SourceTorsionClause_lTorsionCompatible
    (h : S1987D5LargeImageFive) :
    (S1987SourceTorsionClause h).lTorsionCompatible =
      S1725LTorsionCompatible S1987Five :=
  S1982SourceTorsionClause_five_lTorsionCompatible h

/-! ## 5. Axiom footprint -/

#print axioms S1987D5LargeImageFive_iff_S1982
#print axioms S1987D5LargeImageFive_iff_S1894ExactMissing
#print axioms S1987D5LargeImageFive_iff_imageContainsSL2
#print axioms S1987D5LargeImageFive_iff_tail
#print axioms S1987D5LargeImageFive_iff_tail_basis
#print axioms S1987D5LargeImageFive_iff_serre
#print axioms S1987D5LargeImageFive_iff_detKer
#print axioms S1987D5LargeImageFive_of_fullRange
#print axioms S1987SourceTorsionClause
#print axioms S1987SourceTorsionClause_fields
#print axioms S1987SourceTorsionClause_imageContainsSL2

end LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
