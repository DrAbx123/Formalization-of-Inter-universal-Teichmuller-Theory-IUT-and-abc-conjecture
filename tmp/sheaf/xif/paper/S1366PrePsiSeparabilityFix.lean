import tmp.sheaf.xif.paper.S1329RankTwoTorsionBasisActual
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1366PrePsiSeparabilityFix

open Polynomial
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1298TorsionClauseActual
open LeanFormal.IUT.XiFPaper.S1329RankTwoTorsionBasisActual

local instance s1366GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s1366ClosureDecEq (l : PrimeGeFive) :
    DecidableEq (S1329Closure l) :=
  Classical.decEq _

/-!
# S1366: the exact first lemma for separability of the concrete l-division polynomial

S1329ConcreteSeparable l is the statement that the concrete odd l-division
polynomial prePsi_l of the Gaussian curve y ^ 2 + x * y = x ^ 3 + 5 has exactly
(l ^ 2 - 1) / 2 distinct roots over the algebraic closure of Q(i); by
S1362PrePsiSeparabilityActual this is equivalent to prePsi_l.Separable,
Squarefree (prePsi_l), and to (prePsi_l).roots.Nodup.

This file does NOT prove that statement unconditionally, and it introduces no
proof holes, trusted declarations, opaque constants, or placeholder data.  What it does is:

1. Prove, from Mathlib's division-polynomial degree/roots API alone, the
   counting theorem

     detection + cardinality  =>  separability

   for an arbitrary elliptic Weierstrass curve over an algebraically closed
   field: if n is odd and invertible, every n-torsion point has its
   x-coordinate among the roots of prePsi_n (detection), and the n-torsion has
   exactly n ^ 2 points (cardinality), then prePsi_n has at least
   (n ^ 2 - 1) / 2 distinct roots; the unconditional degree bound gives the
   reverse inequality, hence equality, hence separability.

   The proof is the Tau Ceti argument (WeierstrassCurve.separable_prePsi,
   TauCeti commit df319cee..., file
   TauCeti/AlgebraicGeometry/EllipticCurve/Isogeny/MulByInt/DivisionPolynomialSeparable.lean,
   Lean v4.36.0-rc1) with its two analytic inputs made explicit.  Tau Ceti is
   not importable here: this tree is Lean v4.32.2 with Mathlib v4.32.2, while
   Tau Ceti requires Lean v4.36.0-rc1 and a newer Mathlib pin.

2. Specialise the counting theorem to the concrete Gaussian curve and prove
   the exact equivalence

     S1329ConcreteSeparable l  <=>  (S1329Curve l).prePsi (l.value).Separable.

3. Record the two exact first mathematical inputs in the precise forms used by
   the counting theorem:

   * S1366TorsionDetection l: every l-torsion point of the concrete curve has
     its x-coordinate among the roots of prePsi_l.  This is the forward half of
     the S1361/S1329 group-law criterion and is the statement
     DivisionPolynomialDetectsTorsion of
     LeanFormal.IUT.ABCBridge.Galois.EllipticTorsionAlgebraicity; the tree
     proves it for n = 2 and n = 3 and no other n.

   * S1366TorsionCardinality l: Nat.card (S1298TorsionCarrier l) = l ^ 2, the
     numerical cardinality of the S1298 D5 first field.  Equivalently, the
     affine l-torsion has l ^ 2 points; this file proves that form and back.

   Neither is inhabited here.  The single consolidated first lemma is
   S1366GenericOddPrePsiSeparableInput, the characteristic-zero odd-n separability
   specialization of WeierstrassCurve.separable_prePsi of Tau Ceti;
   this file proves it implies S1329ConcreteSeparable.

## What is genuinely new here

* s1366Separable_of_detection_and_card: a complete proof of separability from
  detection plus cardinality, with no use of the reverse half of the group-law
  criterion and no circularity.
* s1366ConcreteSeparable_of_inputs: the concrete S1329 second input follows
  from the two named group-law inputs.
* s1366ConcreteSeparable_of_genericInput: Tau Ceti's separable_prePsi (odd
  part) implies the concrete S1329 second input.

## References

* [J Silverman, The Arithmetic of Elliptic Curves][silverman2009]
* Tau Ceti, WeierstrassCurve.separable_prePsi, commit
  df319cee080d8cab30699ff8ab3ed8d9347768aa.
-/

/-! ## 1. The counting theorem -/

/-- Detection plus cardinality gives separability.

Let W be an elliptic Weierstrass curve over an algebraically closed field, n
odd with (n : F) != 0.  Suppose every n-torsion point has its x-coordinate
among the roots of prePsi_n, and suppose the n-torsion is exactly a finite set
of n.natAbs ^ 2 points.  Then prePsi_n is separable.

No reverse detection and no group-law criterion are used: the roots of
prePsi_n are counted from the torsion points through the two-to-one
x-coordinate map, and the unconditional degree bound closes the count. -/
theorem s1366Separable_of_detection_and_card
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
    (W : WeierstrassCurve F) [W.IsElliptic]
    {n : ℤ} (hodd : ¬ Even n) (hchar : (n : F) ≠ 0)
    (hdet : ∀ P : W.toAffine.Point, n • P = 0 →
      W.evalDivisionPolynomialAtPoint n P = 0)
    (T : Finset W.toAffine.Point) (hTcard : T.card = n.natAbs ^ 2)
    (hTmem : ∀ P : W.toAffine.Point, P ∈ T ↔ n • P = 0) :
    (W.preΨ n).Separable := by
  classical
  have hpre : W.preΨ n ≠ 0 := W.preΨ_ne_zero hchar
  have hsplit : (W.preΨ n).Splits := IsAlgClosed.splits _
  have hdeg : (W.preΨ n).natDegree = (n.natAbs ^ 2 - 1) / 2 := by
    rw [W.natDegree_preΨ hchar, if_neg hodd]
  set S : Finset F := (W.preΨ n).roots.toFinset with hS
  have hzero_mem : (0 : W.toAffine.Point) ∈ T := (hTmem 0).mpr (by simp)
  have hmaps : ∀ P ∈ T.erase 0, P.xRep ∈ S.image (fun x : F => ![x, 1]) := by
    intro P hP
    rw [Finset.mem_erase] at hP
    obtain ⟨hP0, hPT⟩ := hP
    have htors : n • P = 0 := (hTmem P).mp hPT
    rcases P with _ | ⟨x, y, hns⟩
    · exact absurd rfl hP0
    · have hxroot : (W.preΨ n).eval x = 0 := by
        have h := hdet _ htors
        rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
          WeierstrassCurve.evalDivisionPolynomial_eq_eval_preΨ_of_odd W hns.1 hodd] at h
        exact h
      refine Finset.mem_image.mpr ⟨x, ?_, ?_⟩
      · rw [hS, Multiset.mem_toFinset, Polynomial.mem_roots hpre, Polynomial.IsRoot.def]
        exact hxroot
      · rw [WeierstrassCurve.Affine.Point.xRep_some]
  have hfib : ∀ b ∈ S.image (fun x : F => ![x, 1]),
      {P ∈ T.erase 0 | P.xRep = b}.card ≤ 2 := by
    intro b hb
    rcases Finset.eq_empty_or_nonempty {P ∈ T.erase 0 | P.xRep = b} with h | ⟨Q, hQ⟩
    · simp [h]
    · rw [Finset.mem_filter] at hQ
      have hsub : {P ∈ T.erase 0 | P.xRep = b} ⊆ {Q, -Q} := by
        intro P hP
        rw [Finset.mem_filter] at hP
        have hx : P.xRep = Q.xRep := by rw [hP.2, hQ.2]
        rcases WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hx with h | h
        · simp [h]
        · simp [h]
      calc {P ∈ T.erase 0 | P.xRep = b}.card
          ≤ ({Q, -Q} : Finset W.toAffine.Point).card := Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
  have hcount : (T.erase 0).card ≤
      2 * (S.image (fun x : F => ![x, 1])).card :=
    Finset.card_le_mul_card_image_of_maps_to hmaps 2 hfib
  have hEr : (T.erase 0).card = n.natAbs ^ 2 - 1 := by
    rw [Finset.card_erase_of_mem hzero_mem, hTcard]
  have himg : (S.image (fun x : F => ![x, 1])).card ≤ S.card := Finset.card_image_le
  have hSle : S.card ≤ (n.natAbs ^ 2 - 1) / 2 := by
    rw [hS, ← hdeg]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _)
  have hoddN : Odd (n.natAbs ^ 2) := by
    have hoddAbs : Odd n.natAbs := Int.natAbs_odd.mpr (Int.not_even_iff_odd.mp hodd)
    rw [pow_two]
    exact hoddAbs.mul hoddAbs
  have hdvd : 2 ∣ n.natAbs ^ 2 - 1 := (Nat.Odd.sub_odd hoddN odd_one).two_dvd
  have htwo : 2 * ((n.natAbs ^ 2 - 1) / 2) = n.natAbs ^ 2 - 1 :=
    Nat.mul_div_cancel' hdvd
  have hle1 : n.natAbs ^ 2 - 1 ≤ 2 * S.card := by
    calc n.natAbs ^ 2 - 1 = (T.erase 0).card := hEr.symm
      _ ≤ 2 * (S.image (fun x : F => ![x, 1])).card := hcount
      _ ≤ 2 * S.card := Nat.mul_le_mul_left 2 himg
  have hle2 : 2 * S.card ≤ n.natAbs ^ 2 - 1 := by
    calc 2 * S.card ≤ 2 * ((n.natAbs ^ 2 - 1) / 2) := Nat.mul_le_mul_left 2 hSle
      _ = n.natAbs ^ 2 - 1 := htwo
  have hSeq : S.card = (n.natAbs ^ 2 - 1) / 2 := by omega
  have hdegS : S.card = (W.preΨ n).natDegree := by rw [hSeq, hdeg]
  have hnodup : (W.preΨ n).roots.Nodup := by
    rw [← Multiset.toFinset_card_eq_card_iff_nodup, ← hsplit.natDegree_eq_card_roots]
    exact hdegS
  exact (Polynomial.nodup_roots_iff_of_splits hpre hsplit).mp hnodup

/-! ## 2. The exact concrete inputs -/

/-- Exact first input (detection).  Every l-torsion point of the concrete
Gaussian curve has its x-coordinate among the roots of prePsi_l.

This is the forward half of the S1361/S1329 group-law criterion, and is
exactly the statement named DivisionPolynomialDetectsTorsion in
LeanFormal.IUT.ABCBridge.Galois.EllipticTorsionAlgebraicity.  That file proves
it for n = 2 and n = 3 in every characteristic; for l >= 5 it is not available
in Mathlib v4.32.2 or in the tree. -/
def S1366TorsionDetection (l : PrimeGeFive) : Prop :=
  ∀ P : (S1329Curve l).Point,
    (l.value : ℤ) • P = 0 →
      (S1329Curve l).evalDivisionPolynomialAtPoint (l.value : ℤ) P = 0

/-- Exact second input (cardinality).  The actual S1298 projective l-torsion
carrier has l ^ 2 elements.  This is the numerical half of
S1298TorsionCardinalityCard, and the S1329 D5 first field. -/
def S1366TorsionCardinality (l : PrimeGeFive) : Prop :=
  Nat.card (S1298TorsionCarrier l) = l.value ^ 2

/-- The polynomial separability form of the S1329 second input. -/
def S1366PreΨSeparableInput (l : PrimeGeFive) : Prop :=
  (S1329Curve l).preΨ (l.value : ℤ) |>.Separable

/-- The root-count form of the S1329 second input. -/
def S1366RootCount (l : PrimeGeFive) : Prop :=
  ((S1329Curve l).preΨ (l.value : ℤ)).roots.toFinset.card = (l.value ^ 2 - 1) / 2

/-- The root-count form is literally the S1329 ConcreteSeparable statement. -/
theorem s1366RootCount_iff_s1329 (l : PrimeGeFive) :
    S1366RootCount l ↔ S1329ConcreteSeparable l :=
  Iff.rfl

/-- The cardinality input, in the affine Finset form consumed by the counting
theorem: it is equivalent to the S1298 carrier statement. -/
theorem s1366ExistsTorsionFinset_of_cardinality (l : PrimeGeFive)
    (hcard : S1366TorsionCardinality l) :
    ∃ T : Finset (S1329Curve l).Point,
      T.card = l.value ^ 2 ∧
        ∀ P : (S1329Curve l).Point, P ∈ T ↔ (l.value : ℤ) • P = 0 := by
  classical
  let n : ℤ := (l.value : ℤ)
  have haff : Nat.card (AddSubgroup.torsionBy (S1329Curve l).Point n) = l.value ^ 2 := by
    rw [← s1329NatCard_carrier_eq l]
    exact hcard
  have hsub : Nat.card (AddSubgroup.torsionBy (S1329Curve l).Point n) =
      Nat.card {P : (S1329Curve l).Point // n • P = 0} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
    intro P
    exact Submodule.mem_torsionBy_iff (R := ℤ) (M := (S1329Curve l).Point) n P
  have hsubcard : Nat.card {P : (S1329Curve l).Point // n • P = 0} = l.value ^ 2 :=
    hsub.symm.trans haff
  have hne : Nat.card {P : (S1329Curve l).Point // n • P = 0} ≠ 0 := by
    rw [hsubcard]
    exact pow_ne_zero 2 (Nat.Prime.ne_zero l.prime)
  have hfin_sub : Finite {P : (S1329Curve l).Point // n • P = 0} :=
    (Nat.card_ne_zero.mp hne).2
  have hsetfin : {P : (S1329Curve l).Point | n • P = 0}.Finite :=
    Set.finite_coe_iff.mp hfin_sub
  refine ⟨hsetfin.toFinset, ?_, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card _ hsetfin]
    rw [← Nat.card_coe_set_eq]
    change Nat.card {P : (S1329Curve l).Point // n • P = 0} = l.value ^ 2
    exact hsubcard
  · intro P
    rw [Set.Finite.mem_toFinset]
    rfl

/-! ## 3. Specialisation: detection plus cardinality gives the S1329 second input -/

/-- The concrete counting theorem.  Detection plus the S1298 cardinality input
implies separability of the concrete prePsi_l. -/
theorem s1366PreΨSeparable_of_detection_and_cardinality (l : PrimeGeFive)
    (hdet : S1366TorsionDetection l) (hcard : S1366TorsionCardinality l) :
    S1366PreΨSeparableInput l := by
  classical
  have hodd : ¬ Even (l.value : ℤ) := s1329Concrete_odd_int l
  have hchar : ((l.value : ℤ) : S1329Closure l) ≠ 0 :=
    s1329Concrete_l_ne_zero l
  obtain ⟨T, hTcard, hTmem⟩ := s1366ExistsTorsionFinset_of_cardinality l hcard
  have hsep : ((S1329Curve l : WeierstrassCurve (S1329Closure l)).preΨ (l.value : ℤ)).Separable :=
    s1366Separable_of_detection_and_card
      (W := (S1329Curve l : WeierstrassCurve (S1329Closure l)))
      (n := (l.value : ℤ)) hodd hchar
      (by simpa [S1366TorsionDetection] using hdet)
      T (by simpa using hTcard) (by simpa using hTmem)
  simpa [S1366PreΨSeparableInput] using hsep

/-- Separability of the concrete prePsi_l gives the exact root count. -/
theorem s1366ConcreteSeparable_of_preΨSeparable (l : PrimeGeFive)
    (hsep : S1366PreΨSeparableInput l) : S1329ConcreteSeparable l := by
  classical
  have hpre : (S1329Curve l).preΨ (l.value : ℤ) ≠ 0 := s1329Concrete_preΨ_ne_zero l
  have hsplit : ((S1329Curve l).preΨ (l.value : ℤ)).Splits := IsAlgClosed.splits _
  have hdeg : ((S1329Curve l).preΨ (l.value : ℤ)).natDegree = (l.value ^ 2 - 1) / 2 := by
    rw [WeierstrassCurve.natDegree_preΨ (W := (S1329Curve l))
      (n := (l.value : ℤ)) (by simpa using s1329Concrete_l_ne_zero l)]
    rw [if_neg (s1329Concrete_odd_int l)]
    simp
  have hsep' : ((S1329Curve l).preΨ (l.value : ℤ)).Separable := by
    simpa [S1366PreΨSeparableInput] using hsep
  have hnodup : ((S1329Curve l).preΨ (l.value : ℤ)).roots.Nodup :=
    (Polynomial.nodup_roots_iff_of_splits hpre hsplit).mpr hsep'
  have hto : ((S1329Curve l).preΨ (l.value : ℤ)).roots.toFinset.card =
      ((S1329Curve l).preΨ (l.value : ℤ)).roots.card :=
    Multiset.toFinset_card_eq_card_iff_nodup.mpr hnodup
  have hcard : ((S1329Curve l).preΨ (l.value : ℤ)).roots.card =
      ((S1329Curve l).preΨ (l.value : ℤ)).natDegree :=
    (hsplit.natDegree_eq_card_roots).symm
  unfold S1329ConcreteSeparable s1329RootFinset
  rw [hto, hcard, hdeg]

/-- The exact root count gives separability. -/
theorem s1366PreΨSeparable_of_concreteSeparable (l : PrimeGeFive)
    (h : S1329ConcreteSeparable l) : S1366PreΨSeparableInput l := by
  classical
  have hpre : (S1329Curve l).preΨ (l.value : ℤ) ≠ 0 := s1329Concrete_preΨ_ne_zero l
  have hsplit : ((S1329Curve l).preΨ (l.value : ℤ)).Splits := IsAlgClosed.splits _
  have hdeg : ((S1329Curve l).preΨ (l.value : ℤ)).natDegree = (l.value ^ 2 - 1) / 2 := by
    rw [WeierstrassCurve.natDegree_preΨ (W := (S1329Curve l))
      (n := (l.value : ℤ)) (by simpa using s1329Concrete_l_ne_zero l)]
    rw [if_neg (s1329Concrete_odd_int l)]
    simp
  unfold S1329ConcreteSeparable s1329RootFinset at h
  have hcarddeg : ((S1329Curve l).preΨ (l.value : ℤ)).roots.toFinset.card =
      ((S1329Curve l).preΨ (l.value : ℤ)).natDegree := by
    rw [h, hdeg]
  have hnodup : ((S1329Curve l).preΨ (l.value : ℤ)).roots.Nodup := by
    rw [← Multiset.toFinset_card_eq_card_iff_nodup, ← hsplit.natDegree_eq_card_roots]
    exact hcarddeg
  unfold S1366PreΨSeparableInput
  exact (Polynomial.nodup_roots_iff_of_splits hpre hsplit).mp hnodup

/-- The exact equivalence: the S1329 second input is the separability of the
concrete prePsi_l. -/
theorem s1366ConcreteSeparable_iff_preΨSeparable (l : PrimeGeFive) :
    S1329ConcreteSeparable l ↔ S1366PreΨSeparableInput l :=
  ⟨s1366PreΨSeparable_of_concreteSeparable l,
    s1366ConcreteSeparable_of_preΨSeparable l⟩

/-- The concrete S1329 second input from the two exact group-law inputs. -/
theorem s1366ConcreteSeparable_of_inputs (l : PrimeGeFive)
    (hdet : S1366TorsionDetection l) (hcard : S1366TorsionCardinality l) :
    S1329ConcreteSeparable l :=
  s1366ConcreteSeparable_of_preΨSeparable l
    (s1366PreΨSeparable_of_detection_and_cardinality l hdet hcard)

/-- Detection is exactly the tree's DivisionPolynomialDetectsTorsion interface
at the concrete curve. -/
theorem s1366TorsionDetection_iff_detectsTorsion (l : PrimeGeFive) :
    S1366TorsionDetection l ↔
      WeierstrassCurve.DivisionPolynomialDetectsTorsion
        (S1329Curve l : WeierstrassCurve (S1329Closure l)) (l.value : ℤ) :=
  Iff.rfl

/-- The bare cardinality input is the numerical half of
S1298TorsionCardinalityCard. -/
theorem s1366TorsionCardinality_iff_cardinalityCard (l : PrimeGeFive) :
    S1366TorsionCardinality l ↔ S1298TorsionCardinalityCard l :=
  ⟨s1329TorsionCardinalityCard_of_natCard, fun h => h.2⟩

/-- The full S1329 criterion discharges detection. -/
theorem s1366TorsionDetection_of_criterion (l : PrimeGeFive)
    (hcrit : S1329ConcreteCriterion l) : S1366TorsionDetection l :=
  fun P hP => (hcrit P).mp hP

/-- Under the S1329 group-law criterion, cardinality alone gives the second
input; this is the exact form in which the two S1329 fields interact. -/
theorem s1366ConcreteSeparable_of_criterion_and_cardinality (l : PrimeGeFive)
    (hcrit : S1329ConcreteCriterion l) (hcard : S1366TorsionCardinality l) :
    S1329ConcreteSeparable l :=
  s1366ConcreteSeparable_of_inputs l
    (s1366TorsionDetection_of_criterion l hcrit) hcard

/-- Cardinality alone gives the S1329 D5 basis, with no criterion and no
separability input. -/
theorem s1366Basis_nonempty_of_cardinality (l : PrimeGeFive)
    (hcard : S1366TorsionCardinality l) :
    Nonempty (S1329TorsionBasis l) :=
  (s1329Basis_nonempty_iff_natCard l).mpr hcard

/-! ## 4. The consolidated first lemma, in generic form -/

/-- The exact first mathematical lemma (odd form).

For every elliptic Weierstrass curve over a characteristic-zero field and every
odd nonzero integer n, the odd division polynomial prePsi_n is separable.
This is the characteristic-zero, odd-n part of Tau Ceti's WeierstrassCurve.separable_prePsi
(TauCeti commit df319cee...,
AlgebraicGeometry/EllipticCurve/Isogeny/MulByInt/DivisionPolynomialSeparable.lean),
which proves it for every field in which n is invertible.

This file does not inhabit this proposition.  It proves that the proposition
implies S1329ConcreteSeparable, and that the concrete statement is exactly the
separability form consumed by S1329. -/
def S1366GenericOddPreΨSeparableInput : Prop :=
  ∀ (F : Type) [Field F] [CharZero F]
    (W : WeierstrassCurve F) [W.IsElliptic] (n : ℤ),
    ¬ Even n → n ≠ 0 → (W.preΨ n).Separable

/-- The generic first lemma implies the concrete separability input. -/
theorem s1366GenericInput_to_concrete
    (h : S1366GenericOddPreΨSeparableInput) :
    ∀ l : PrimeGeFive, S1366PreΨSeparableInput l := by
  intro l
  have hl : (l.value : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.Prime.ne_zero l.prime)
  have hsep :
      ((S1329Curve l : WeierstrassCurve (S1329Closure l)).preΨ (l.value : ℤ)).Separable :=
    h (S1329Closure l) (S1329Curve l : WeierstrassCurve (S1329Closure l))
      (l.value : ℤ) (s1329Concrete_odd_int l) hl
  simpa [S1366PreΨSeparableInput] using hsep

/-- The consolidated first lemma gives the S1329 second input. -/
theorem s1366ConcreteSeparable_of_genericInput
    (h : S1366GenericOddPreΨSeparableInput) (l : PrimeGeFive) :
    S1329ConcreteSeparable l :=
  s1366ConcreteSeparable_of_preΨSeparable l
    (s1366GenericInput_to_concrete h l)

/-- The consolidated first lemma gives the S1329 D5 basis under the S1329
group-law criterion. -/
theorem s1366Basis_nonempty_of_genericInput_and_criterion
    (h : S1366GenericOddPreΨSeparableInput) (l : PrimeGeFive)
    (hcrit : S1329ConcreteCriterion l) :
    Nonempty (S1329TorsionBasis l) :=
  (s1329ConcreteBasis_iff_separable l hcrit).mpr
    (s1366ConcreteSeparable_of_genericInput h l)

/-! ## 5. Axiom footprint -/

#print axioms s1366Separable_of_detection_and_card
#print axioms s1366RootCount_iff_s1329
#print axioms s1366ExistsTorsionFinset_of_cardinality
#print axioms s1366PreΨSeparable_of_detection_and_cardinality
#print axioms s1366ConcreteSeparable_of_preΨSeparable
#print axioms s1366PreΨSeparable_of_concreteSeparable
#print axioms s1366ConcreteSeparable_iff_preΨSeparable
#print axioms s1366ConcreteSeparable_of_inputs
#print axioms s1366TorsionDetection_iff_detectsTorsion
#print axioms s1366TorsionCardinality_iff_cardinalityCard
#print axioms s1366TorsionDetection_of_criterion
#print axioms s1366ConcreteSeparable_of_criterion_and_cardinality
#print axioms s1366Basis_nonempty_of_cardinality
#print axioms s1366GenericInput_to_concrete
#print axioms s1366ConcreteSeparable_of_genericInput
#print axioms s1366Basis_nonempty_of_genericInput_and_criterion

end LeanFormal.IUT.XiFPaper.S1366PrePsiSeparabilityFix
