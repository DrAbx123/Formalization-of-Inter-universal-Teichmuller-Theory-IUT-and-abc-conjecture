/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
-/
import tmp.sheaf.xif.paper.S1942PrePsiFiveActual
import tmp.sheaf.xif.paper.S1933PrePsiSeparableActual
import tmp.sheaf.xif.paper.S1924ZeroCriterionActual
import tmp.sheaf.xif.paper.S1906RankTwoTorsionActual
import tmp.sheaf.xif.paper.S1894D5LargeImageActual

/-!
# S1982: the l = 5 instance of the D5 torsion gap on the actual curve E'/F'

S1942 proves the derivative/gcd certificate

  A * prePsi_5 + B * (prePsi_5)' = C (5120 * Delta^5)

over the universal curve Z[a1,a2,a3,a4,a6], and hence
`(W.prePsi 5).Separable` for every elliptic Weierstrass curve over every
characteristic-zero field (`S1942Certificate_five`,
`S1942_prePsi_five_separable`).  S1924 removes the x-coordinate formula and
the zero criterion from the S1906 division-polynomial route, so that route is
exactly the separability of `prePsi_l` (`S1924S1906BasisGap_iff_separable`).

This file performs the l = 5 specialization on the actual curve E' of S1720
over the actual number field F':

* `S1982Separability_five : S1906Separability 5`, obtained by transporting
  `S1942Certificate_five` through S1933's certificate transfer
  (`S1933separable_of_certificate`) to the actual base-changed curve
  `S1906W = S1720Curve.curve.baseChange (AlgebraicClosure F')`;
* `S1982RankTwoBasisGap_five : S1725RankTwoBasisGap 5`, by S1924;
* the exact S1906 cardinality at l = 5
  (`Nat.card E'[5] = 25`), the finrank-two form, finite-free-rank-two, and
  an actual basis `S1982Basis`;
* the decomposition of the D5 image input at l = 5.  S1894 proves

    S1725ImageContainsSL2 l  <->  S1725RankTwoBasisGap l
                                    AND S1894LargeImageInput l.

  Since the rank-two half is now a theorem, the exact remaining first missing
  input of the actual D5 clause at l = 5 is the basis-free large-image
  condition `S1982D5ExactFirstMissing`, i.e. the frozen Serre-style statement
  `SerreStyleLargeImageStatement E' 5`.
  The actual clause `S1725SourceTorsionClause 5` is constructed from exactly
  that input (`S1982SourceTorsionClause_five`), so the interface is exercised
  and the gap is exposed, not hidden.

## What is not claimed

No unconditional inhabitant of `S1725ImageContainsSL2 5`, of the
basis-free large-image condition, or of the paper's D5 clause is produced:
the large-image statement is the open Serre input, and it is not derivable
from rank-two freeness.  The other D5 fields (mu_6 carrier, 2*3-torsion
rationality, l-coprimality at the actual bad place above 7) are unconditional
already in S1725/S1724 and are re-exported here at l = 5.

No sorry, no admit, no axiom, no opaque, no placeholder.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1982D5FiveActual

open Polynomial WeierstrassCurve
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual
open LeanFormal.IUT.XiFPaper.S1924ZeroCriterionActual
open LeanFormal.IUT.XiFPaper.S1933PrePsiSeparableActual
open LeanFormal.IUT.XiFPaper.S1942PrePsiFiveActual
open LeanFormal.IUT.XiFPaper.S1894D5LargeImageActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.InitialThetaSource.TorsionCarrierReduction

/-! ## 0. The prime label l = 5 -/

/-- The prime label `l = 5`, with its actual primality and `5 <= l` proofs. -/
def S1982Five : PrimeGeFive := ⟨5, Nat.prime_five, le_rfl⟩

@[simp] theorem S1982Five_value : S1982Five.value = 5 := rfl

/-! ## 1. The actual curve E' over the algebraic closure is elliptic -/

/-- The base change of E' to the algebraic closure of F' is elliptic.  This is
Mathlib's base-change instance for `IsElliptic`, made explicit at the concrete
curve `S1906W`. -/
theorem S1982W_isElliptic : S1906W.IsElliptic := by
  change (S1720Curve.curve.map (algebraMap S1720Field S1906K)).IsElliptic
  infer_instance

/-! ## 2. `S1906Separability 5` -/

/-- **Separability of `prePsi_5` on the actual curve E'.**  The S1942
certificate at n = 5 is transported through S1933's certificate transfer to
the actual base-changed curve over the characteristic-zero algebraic closure
of F'. -/
theorem S1982Separability_five : S1906Separability S1982Five := by
  haveI : S1906W.IsElliptic := S1982W_isElliptic
  have h : (S1906W.preΨ (5 : ℤ)).Separable :=
    S1933separable_of_certificate (W := S1906W) S1942Certificate_five
  simpa [S1906Separability, S1982Five] using h

/-- The same separability directly from S1942's headline theorem. -/
theorem S1982Separability_five_direct : S1906Separability S1982Five := by
  haveI : S1906W.IsElliptic := S1982W_isElliptic
  have h : (S1906W.preΨ (5 : ℤ)).Separable :=
    S1942_preΨ_five_separable S1906W
  simpa [S1906Separability, S1982Five] using h

/-- The root count of `prePsi_5` on E': its `(5^2 - 1)/2 = 12` roots are
distinct. -/
theorem S1982RootCount_five : S1906RootCount S1982Five :=
  S1906RootCount_of_separable S1982Five S1982Separability_five

/-! ## 3. `S1725RankTwoBasisGap 5` and the exact l = 5 cardinality -/

/-- **The rank-two basis gap at l = 5**: the actual 5-torsion of E' is
ZMod-5-free of rank two.  This is the S1924 consumer of separability. -/
theorem S1982RankTwoBasisGap_five : S1725RankTwoBasisGap S1982Five :=
  S1924S1906BasisGap_of_separable S1982Five S1982Separability_five

/-- The exact S1906 first-missing statement at l = 5 is now a theorem:
`Nat.card E'[5] = 25`. -/
theorem S1982S1906ExactFirstMissing_five :
    S1906ExactFirstMissing S1982Five :=
  (S1906RankTwoBasisGap_iff_natCard S1982Five).mp S1982RankTwoBasisGap_five

/-- The cardinality in the concrete numeral form. -/
theorem S1982NatCard_LTorsion_five :
    Nat.card (S1720Curve.LTorsion S1982Five) = 25 := by
  have h : Nat.card (S1720Curve.LTorsion S1982Five) = S1982Five.value ^ 2 :=
    S1982S1906ExactFirstMissing_five
  rw [S1982Five_value] at h
  exact h.trans (by norm_num)

/-- The finrank form: `dim_{ZMod 5} E'[5] = 2`. -/
theorem S1982Finrank_five :
    Module.finrank (ZMod S1982Five.value) (S1720Curve.LTorsion S1982Five) = 2 :=
  (S1906RankTwoBasisGap_iff_finrank S1982Five).mp S1982RankTwoBasisGap_five

/-- `E'[5]` is a finite free ZMod-5-module of rank two. -/
theorem S1982FiniteFreeRankTwo_five :
    Module.Finite (ZMod S1982Five.value) (S1720Curve.LTorsion S1982Five) ∧
      Module.Free (ZMod S1982Five.value) (S1720Curve.LTorsion S1982Five) ∧
      Module.finrank (ZMod S1982Five.value) (S1720Curve.LTorsion S1982Five) = 2 :=
  S1906FiniteFreeRankTwo_of_basisGap S1982Five S1982RankTwoBasisGap_five

/-- An actual rank-two ZMod-5-basis of the actual E'[5], extracted from the
nonempty type of bases. -/
noncomputable def S1982Basis : S1725TorsionBasis S1982Five :=
  Classical.choice S1982RankTwoBasisGap_five

/-- The cardinality follows from the explicit basis `S1982Basis`. -/
theorem S1982NatCard_eq_sq_of_basis :
    Nat.card (S1720Curve.LTorsion S1982Five) = S1982Five.value ^ 2 :=
  S1906NatCard_eq_sq_of_basis S1982Five S1982Basis

/-! ## 4. The D5 clause at l = 5 and the exact remaining image input -/

/-- The selected bad place at l = 5 is the actual place of F' above 7. -/
theorem S1982D5Place_five : S1725D5Place S1982Five = S1720PlaceAboveSeven :=
  S1725D5Place_of_five S1982Five rfl

/-- The residue characteristic of the l = 5 bad place is 7. -/
theorem S1982D5Place_residueCharacteristic_five :
    NumberFieldFinitePlace.residueCharacteristic (S1725D5Place S1982Five) = 7 := by
  rw [S1982D5Place_five, S1725PlaceAboveSeven_residueCharacteristic]

/-- E' has split multiplicative reduction at the l = 5 bad place. -/
theorem S1982SplitAtPlace_five :
    S1720Curve.HasSplitMultiplicativeReductionAt (S1725D5Place S1982Five) :=
  S1725SplitAtPlace S1982Five

/-- The residue-characteristic half of Definition 3.1(c) at l = 5: 5 is prime
to 7. -/
theorem S1982LTorsionCompatible_five :
    S1725LTorsionCompatible S1982Five :=
  S1725LTorsionCompatible_proved S1982Five

/-- The 2*3-torsion condition (paper condition (b)) for E'/F' at l = 5. -/
theorem S1982SixTorsionIndependent : S1725SixTorsionIndependent :=
  S1725SixTorsionIndependent_proved

/-- **The exact remaining first missing input at l = 5**: the basis-free
large-image condition of S1894.  Equivalently, every rank-two basis of E'[5]
sees the full determinant-one subgroup in the image of the actual mod-5
representation.  This is the Serre-style large-image statement for E'/F'. -/
def S1982D5ExactFirstMissing : Prop := S1894LargeImageInput S1982Five

/-- The exact first missing input is literally the image input of the actual
S1725 clause, since the rank-two half has been proved in section 3. -/
theorem S1982D5ExactFirstMissing_iff_imageContainsSL2 :
    S1982D5ExactFirstMissing ↔ S1725ImageContainsSL2 S1982Five :=
  (S1894ImageContainsSL2_iff_forall_of_basisGap S1982Five
    S1982RankTwoBasisGap_five).symm

/-- The remaining input is already witnessed by the single actual basis
`S1982Basis`: by S1894's basis-independence, the containment at one basis is
the basis-free condition. -/
theorem S1982D5ExactFirstMissing_iff_tail :
    S1982D5ExactFirstMissing ↔ S1725ImageTail S1982Five S1982Basis := by
  constructor
  · intro h
    exact h S1982Basis
  · intro h b
    exact (S1894ImageTail_congr S1982Five b S1982Basis).mpr h

/-- The remaining input is literally the frozen Serre-style large-image
statement for the actual curve E'. -/
theorem S1982D5ExactFirstMissing_iff_serre :
    S1982D5ExactFirstMissing ↔
      SerreStyleLargeImageStatement S1720Curve S1982Five :=
  S1982D5ExactFirstMissing_iff_imageContainsSL2.trans
    (S1725ImageContainsSL2_iff_serre S1982Five)

/-- S1894's exact missing statement splits into the rank-two gap and the
large-image input; at l = 5 the rank-two half is now a theorem, so S1894's
missing statement is exactly the large-image input. -/
theorem S1982S1894ExactMissing_iff :
    S1894ExactMissing S1982Five ↔ S1982D5ExactFirstMissing :=
  ⟨fun h => h.2, fun h => ⟨S1982RankTwoBasisGap_five, h⟩⟩

/-- **The actual S1725 D5 clause at l = 5**, constructed from the one remaining
source input.  Every field is the actual object of S1720/S1721/S1724/S1725;
the image field is the large-image input, not a placeholder. -/
noncomputable def S1982SourceTorsionClause_five
    (h : S1982D5ExactFirstMissing) :
    SourceTorsionClause.{0, 0, 0} S1982Five :=
  S1725SourceTorsionClause S1982Five
    (S1982D5ExactFirstMissing_iff_imageContainsSL2.mp h)

/-- The same clause from the single-basis tail witness. -/
noncomputable def S1982SourceTorsionClause_five_of_tail
    (h : S1725ImageTail S1982Five S1982Basis) :
    SourceTorsionClause.{0, 0, 0} S1982Five :=
  S1982SourceTorsionClause_five (S1982D5ExactFirstMissing_iff_tail.mpr h)

/-- The image field of the l = 5 clause is the actual S1725 image input. -/
@[simp] theorem S1982SourceTorsionClause_five_imageContainsSL2
    (h : S1982D5ExactFirstMissing) :
    (S1982SourceTorsionClause_five h).imageContainsSL2 =
      S1725ImageContainsSL2 S1982Five := rfl

/-- The torsion carrier of the l = 5 clause is the literal mu_6 of the
algebraic closure of F'. -/
@[simp] theorem S1982SourceTorsionClause_five_torsionCarrier
    (h : S1982D5ExactFirstMissing) :
    (S1982SourceTorsionClause_five h).torsionCarrier =
      S1725SixTorsionCarrier := rfl

/-- The six-torsion field of the l = 5 clause is the S1724 theorem. -/
@[simp] theorem S1982SourceTorsionClause_five_sixTorsionIndependent
    (h : S1982D5ExactFirstMissing) :
    (S1982SourceTorsionClause_five h).sixTorsionIndependent =
      PuncturedEllipticCurve.Torsion23Rational S1720Curve := rfl

/-- The l-compatibility field of the l = 5 clause is the actual
residue-characteristic condition at the place above 7. -/
@[simp] theorem S1982SourceTorsionClause_five_lTorsionCompatible
    (h : S1982D5ExactFirstMissing) :
    (S1982SourceTorsionClause_five h).lTorsionCompatible =
      S1725LTorsionCompatible S1982Five := rfl

/-- The three source-clause fields of the l = 5 clause, with the image part
carried by the remaining input `h`. -/
theorem S1982SourceTorsionClause_five_fields
    (h : S1982D5ExactFirstMissing) :
    (S1982SourceTorsionClause_five h).imageContainsSL2 ∧
      (S1982SourceTorsionClause_five h).sixTorsionIndependent ∧
      (S1982SourceTorsionClause_five h).lTorsionCompatible :=
  S1725SourceTorsionClause_fields S1982Five
    (S1982D5ExactFirstMissing_iff_imageContainsSL2.mp h)

/-! ## 5. Axiom footprint -/

#print axioms S1982W_isElliptic
#print axioms S1982Separability_five
#print axioms S1982Separability_five_direct
#print axioms S1982RootCount_five
#print axioms S1982RankTwoBasisGap_five
#print axioms S1982S1906ExactFirstMissing_five
#print axioms S1982NatCard_LTorsion_five
#print axioms S1982Finrank_five
#print axioms S1982FiniteFreeRankTwo_five
#print axioms S1982Basis
#print axioms S1982D5ExactFirstMissing_iff_imageContainsSL2
#print axioms S1982D5ExactFirstMissing_iff_tail
#print axioms S1982D5ExactFirstMissing_iff_serre
#print axioms S1982S1894ExactMissing_iff
#print axioms S1982SourceTorsionClause_five
#print axioms S1982SourceTorsionClause_five_of_tail
#print axioms S1982SourceTorsionClause_five_fields

end LeanFormal.IUT.XiFPaper.S1982D5FiveActual
