import tmp.sheaf.xif.paper.S1329RankTwoTorsionBasisActual
import LeanFormal.IUT.ABCBridge.Galois.EllipticTorsionAlgebraicity

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1361DivisionCriterionActual

open Polynomial
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1298TorsionClauseActual
open LeanFormal.IUT.XiFPaper.S1329RankTwoTorsionBasisActual

/-!
# S1361: the group-law criterion s1329DivisionCriterion, and its exact Mathlib gap

S1329 reduced the rank-two l-torsion basis to two classical facts.  Its first
field is the division-polynomial criterion

  s1329DivisionCriterion W l :
    forall P : W.Point, (l : Int) • P = 0 <-> W.evalDivisionPolynomialAtPoint l P = 0

for the concrete curve y^2 + xy = x^3 + 5 over AlgebraicClosure Q(i) and every
PrimeGeFive l.  This file attacks that criterion with the Mathlib API for
Weierstrass curves, division polynomials, nsmul and torsion.

## What is proved here

1.  The target is split into its two honest halves, forward detection
    n • P = 0 -> psi_n(P) = 0 and reverse detection psi_n(P) = 0 -> n • P = 0;
    the full criterion is exactly their conjunction.

2.  The standard missing Mathlib coordinate formula
    x([n]P) = Phi_n(P) / psi_n(P)^2  (for psi_n(P) != 0)
    is isolated as s1361XCoordinateFormula, and it is proved that this formula
    implies forward detection.  The formula itself is proved here for n = 1
    and n = 2 from Mathlib's tangent/addition formulae; the general-n proof is
    exactly the missing piece.

3.  The reverse statement is isolated as s1361ZeroCriterion, and the full
    criterion is proved from the coordinate formula plus s1361ZeroCriterion.

4.  The concrete Gaussian curve and the concrete criterion are specialised,
    and the same reduction is proved there.  For odd l the point-level
    criterion is proved equivalent to the affine prePsi form
    prePsi_l(x(P)) = 0, which is the formulation used in S1329.

5.  The low-degree boundary is recorded: the full criterion is proved here
    for n = 1, the tree has the full n = 2 criterion, and it has forward
    detection for n = 3; none of these gives the criterion for PrimeGeFive
    l >= 5.

## What is NOT proved and NOT assumed

Neither half of the criterion is proved here.  No instance of
s1361XCoordinateFormula or s1361ZeroCriterion is asserted, no axiom, sorry or
opaque declaration is introduced, and the criterion is not claimed.  The exact
Mathlib gap is documented in the final section.

## The exact gap

Mathlib (v4.32.2 checkout in this workspace) has the bivariate psi_n, phi_n and
the univariate Phi_n, prePsi_n, PsiSq_n, and the coordinate-ring congruences
mk_psi, mk_phi, mk_Psi_sq (DivisionPolynomial/Basic.lean lines 128, 338, 482).
It does *not* define the bivariate omega_n: the definition is written in the
module docstring at Basic.lean lines 28-30, but the declaration is an explicit
TODO at Basic.lean line 71.  Hence it cannot even state the standard
y-coordinate formula y([n]P) = omega_n(P) / psi_n(P)^3.  More importantly for
the present criterion, it has no lemma of the form

  x([n]P) = Phi_n(P) / psi_n(P)^2

for any n outside the two-point addition/deletion formulae.  The only genuine
nsmul-to-division-polynomial equivalence in the tree is the n = 2 lemma at
EllipticDivisionPolynomialEvaluation.lean:267; n = 3 has only the forward
direction at EllipticTorsionAlgebraicity.lean:141.  Mathlib's affine Point
instance itself only installs nsmulBinRec (Affine/Point.lean:769-772), with no
coordinate formula for nsmul.  The first missing lemma needed for the
criterion is therefore the x-coordinate formula recorded below; the reverse
direction additionally needs the zero/divisor statement s1361ZeroCriterion
(equivalently div(psi_n) = n^2(O) - sum_{T in E[n]} T), which is also absent
from Mathlib.  The file's #guard_msgs probes record that the corresponding
Mathlib names do not exist in this checkout.
-/

/-! ## 1. Generic reduction: the criterion is forward plus reverse -/

section Generic

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve.Affine K)

/-- The x-coordinate of an affine point, none at infinity. -/
noncomputable def s1361XCoord : W.Point → Option K
  | .zero => none
  | .some x _ _ => some x

@[simp]
lemma s1361XCoord_zero : s1361XCoord W (0 : W.Point) = none := rfl

@[simp]
lemma s1361XCoord_some {x y : K} (h : W.Nonsingular x y) :
    s1361XCoord W (WeierstrassCurve.Affine.Point.some x y h) = some x := rfl

/-- **The first missing Mathlib lemma.**  Away from the zeros of psi_n,
multiplication by n is affine and its x-coordinate is
Phi_n(x) / psi_n(x,y)^2.  This is the standard formula
x([n]P) = phi_n(P) / psi_n(P)^2, rewritten through the coordinate-ring
congruence mk_phi.  Mathlib has no such lemma for n >= 4. -/
def s1361XCoordinateFormula (n : ℤ) : Prop :=
  ∀ (x y : K) (h : W.Nonsingular x y),
    W.evalDivisionPolynomial x y n ≠ 0 →
      s1361XCoord W (n • WeierstrassCurve.Affine.Point.some x y h) =
        some ((W.Φ n).eval x / (W.evalDivisionPolynomial x y n) ^ 2)

/-- The forward detection statement: n-torsion vanishes at the n-division polynomial.
This is exactly the interface DivisionPolynomialDetectsTorsion of
LeanFormal.IUT.ABCBridge.Galois.EllipticTorsionAlgebraicity. -/
def s1361Detection (n : ℤ) : Prop :=
  ∀ P : W.Point, n • P = 0 → W.evalDivisionPolynomialAtPoint n P = 0

/-- The reverse detection statement: a zero of the n-division polynomial is n-torsion.
This is the second missing half, whose standard proof uses the divisor of psi_n. -/
def s1361ZeroCriterion (n : ℤ) : Prop :=
  ∀ P : W.Point, W.evalDivisionPolynomialAtPoint n P = 0 → n • P = 0

/-- The affine prePsi form of the criterion: at every nonsingular affine point, n-torsion
is exactly the vanishing of the univariate polynomial prePsi_n at its x-coordinate.
For odd n this is equivalent to the full point-level criterion. -/
def s1361PreΨCriterion (n : ℤ) : Prop :=
  ∀ (x y : K) (h : W.Nonsingular x y),
    n • WeierstrassCurve.Affine.Point.some x y h = 0 ↔ (W.preΨ n).eval x = 0

/-- For odd n, the point-level criterion is exactly the affine prePsi criterion.
This is the precise sense in which s1329DivisionCriterion is equivalent to
prePsi_l(x(P)) = 0. -/
theorem s1361Criterion_iff_preΨ_of_odd {n : ℤ} (hn : ¬ Even n) :
    (∀ P : W.Point, n • P = 0 ↔ W.evalDivisionPolynomialAtPoint n P = 0) ↔
      s1361PreΨCriterion W n := by
  constructor
  · intro h x y hns
    rw [h (WeierstrassCurve.Affine.Point.some x y hns),
      WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
      W.evalDivisionPolynomial_eq_eval_preΨ_of_odd hns.1 hn]
  · intro h P
    cases P with
    | zero => exact iff_of_true (zsmul_zero n) (by simp)
    | some x y hns =>
        rw [h x y hns, WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
          W.evalDivisionPolynomial_eq_eval_preΨ_of_odd hns.1 hn]

/-- The full group-law criterion is exactly the conjunction of the two missing directions. -/
theorem s1361Criterion_iff (n : ℤ) :
    (∀ P : W.Point, n • P = 0 ↔ W.evalDivisionPolynomialAtPoint n P = 0) ↔
      s1361Detection W n ∧ s1361ZeroCriterion W n := by
  constructor
  · intro h
    exact ⟨fun P hP => (h P).mp hP, fun P hP => (h P).mpr hP⟩
  · rintro ⟨hdet, hzero⟩ P
    exact ⟨hdet P, hzero P⟩

/-- The x-coordinate formula implies the forward detection.  This is a genuine
reduction: the only extra input is the missing coordinate formula. -/
theorem s1361Detection_of_xCoordinateFormula {n : ℤ}
    (hX : s1361XCoordinateFormula W n) : s1361Detection W n := by
  intro P hP
  cases P with
  | zero => simp
  | some x y hns =>
      by_contra hne
      have hx := hX x y hns hne
      rw [hP] at hx
      simp [s1361XCoord] at hx

/-- The x-coordinate formula at n = 1 is immediate. -/
theorem s1361XCoordinateFormula_one : s1361XCoordinateFormula W 1 := by
  intro x y h hne
  simp


/-- The x-coordinate formula at n = 2, from the tangent formula.  This is a
genuine proof of the missing formula in the first nontrivial case. -/
theorem s1361XCoordinateFormula_two : s1361XCoordinateFormula W 2 := by
  intro x y h hne
  have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 :=
    (WeierstrassCurve.Affine.equation_iff' (W := W.toAffine) x y).mp h.1
  have hB : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    simpa [WeierstrassCurve.evalDivisionPolynomial_two] using hne
  have hy : y ≠ W.negY x y := by
    intro hy
    exact hne ((WeierstrassCurve.evalDivisionPolynomial_two_eq_zero_iff_negY (W := W)).mpr hy)
  set A : K := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y with hA
  set B : K := 2 * y + W.a₁ * x + W.a₃ with hBdef
  have hBne : B ≠ 0 := by simpa [hBdef] using hB
  have hslope : W.slope x x y y = A / B := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
    rw [WeierstrassCurve.Affine.negY]
    simp only [hA, hBdef]
    congr 1
    ring
  have hpoly : A ^ 2 + W.a₁ * A * B - (W.a₂ + 2 * x) * B ^ 2 -
      (W.Φ 2).eval x =
      (-(W.a₁ ^ 2 + 4 * W.a₂ + 8 * x)) *
        (y ^ 2 + W.a₁ * x * y + W.a₃ * y -
          (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) := by
    rw [hA, hBdef, WeierstrassCurve.Φ_two]
    simp only [WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
    ring
  have hAB : W.addX x x (A / B) * B ^ 2 =
      A ^ 2 + W.a₁ * A * B - (W.a₂ + 2 * x) * B ^ 2 := by
    rw [WeierstrassCurve.Affine.addX]
    field_simp [hBne]
    ring
  have hmain : W.addX x x (A / B) * B ^ 2 - (W.Φ 2).eval x = 0 := by
    rw [hAB, hpoly, hE]
    ring
  have hformula : W.addX x x (A / B) = (W.Φ 2).eval x / B ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hBne)]
    linear_combination hmain
  rw [two_zsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
  rw [s1361XCoord_some, WeierstrassCurve.evalDivisionPolynomial_two]
  rw [hslope, hformula]

/-- The forward detection at n = 2, derived from the coordinate formula. -/
theorem s1361Detection_two : s1361Detection W 2 :=
  s1361Detection_of_xCoordinateFormula W (s1361XCoordinateFormula_two W)

/-- The full criterion at n = 1, unconditionally. -/
theorem s1361OneCriterion :
    ∀ P : W.Point, (1 : ℤ) • P = 0 ↔ W.evalDivisionPolynomialAtPoint 1 P = 0 := by
  intro P
  cases P with
  | zero => exact iff_of_true (by rfl) (by simp)
  | some x y h =>
      simp [WeierstrassCurve.Affine.Point.some_ne_zero h]

/-- The reverse detection at n = 1, unconditionally. -/
theorem s1361ZeroCriterion_one : s1361ZeroCriterion W 1 := by
  intro P hP
  cases P with
  | zero => rfl
  | some x y h => simp at hP

/-- The full criterion follows from the two explicit missing statements. -/
theorem s1361Criterion_of_xCoordinateFormula_and_zeroCriterion {n : ℤ}
    (hX : s1361XCoordinateFormula W n) (hZ : s1361ZeroCriterion W n) :
    ∀ P : W.Point, n • P = 0 ↔ W.evalDivisionPolynomialAtPoint n P = 0 :=
  (s1361Criterion_iff W n).mpr ⟨s1361Detection_of_xCoordinateFormula W hX, hZ⟩

/-! ### Boundary: the two cases that Mathlib/the tree actually has -/

/-- The full n = 2 criterion, from Mathlib's two-nsmul computation.  This is the
only full nsmul-to-division-polynomial equivalence available for n >= 2. -/
theorem s1361TwoCriterion :
    ∀ P : W.Point, (2 : ℤ) • P = 0 ↔ W.evalDivisionPolynomialAtPoint 2 P = 0 := by
  intro P
  have h : (2 : ℤ) • P = (2 : ℕ) • P := natCast_zsmul P 2
  rw [h]
  exact W.two_nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_two_eq_zero P

/-- Forward detection at n = 3, in every characteristic, from the tree's
three-nsmul syzygy proof.  The reverse direction at n = 3 is not available. -/
theorem s1361ThreeDetection : s1361Detection W 3 := by
  intro P hP
  have h : (3 : ℤ) • P = (3 : ℕ) • P := natCast_zsmul P 3
  have hP' : (3 : ℕ) • P = 0 := by
    rwa [h] at hP
  exact W.evalDivisionPolynomialAtPoint_three_eq_zero_of_three_nsmul_eq_zero P hP'

end Generic

/-! ## 2. Specialisation to the concrete Gaussian curve -/

section Concrete

local instance s1361ClosureDecEq (l : PrimeGeFive) :
    DecidableEq (S1329Closure l) := Classical.decEq _

/-- The algebraic closure used by the concrete Gaussian input. -/
abbrev s1361Closure (l : PrimeGeFive) : Type := S1329Closure l

/-- The concrete affine curve y^2 + xy = x^3 + 5 over the closure. -/
abbrev s1361Curve (l : PrimeGeFive) :
    WeierstrassCurve.Affine (s1361Closure l) := S1329Curve l

/-- The S1329 criterion at the concrete curve. -/
abbrev s1361ConcreteCriterion (l : PrimeGeFive) : Prop := S1329ConcreteCriterion l

/-- The concrete forward detection half. -/
abbrev s1361ConcreteDetection (l : PrimeGeFive) : Prop :=
  s1361Detection (s1361Curve l) (l.value : ℤ)

/-- The concrete reverse detection half. -/
abbrev s1361ConcreteZeroCriterion (l : PrimeGeFive) : Prop :=
  s1361ZeroCriterion (s1361Curve l) (l.value : ℤ)

/-- The concrete missing x-coordinate formula. -/
abbrev s1361ConcreteXCoordinateFormula (l : PrimeGeFive) : Prop :=
  s1361XCoordinateFormula (s1361Curve l) (l.value : ℤ)

/-- The concrete affine prePsi form of the criterion. -/
abbrev s1361ConcretePreΨCriterion (l : PrimeGeFive) : Prop :=
  s1361PreΨCriterion (s1361Curve l) (l.value : ℤ)

/-- At the concrete curve, the point-level criterion is exactly the affine prePsi
criterion prePsi_l(x(P)) = 0, since l is odd. -/
theorem s1361ConcreteCriterion_iff_preΨ (l : PrimeGeFive) :
    s1361ConcreteCriterion l ↔ s1361ConcretePreΨCriterion l := by
  change (∀ P : (s1361Curve l).Point,
      (l.value : ℤ) • P = 0 ↔
        (s1361Curve l).evalDivisionPolynomialAtPoint (l.value : ℤ) P = 0) ↔ _
  exact s1361Criterion_iff_preΨ_of_odd (s1361Curve l) (s1329Concrete_odd_int l)

/-- The concrete criterion is exactly forward detection plus reverse detection. -/
theorem s1361ConcreteCriterion_iff (l : PrimeGeFive) :
    s1361ConcreteCriterion l ↔
      s1361ConcreteDetection l ∧ s1361ConcreteZeroCriterion l := by
  change (∀ P : (s1361Curve l).Point,
      (l.value : ℤ) • P = 0 ↔
        (s1361Curve l).evalDivisionPolynomialAtPoint (l.value : ℤ) P = 0) ↔ _
  exact s1361Criterion_iff (s1361Curve l) (l.value : ℤ)

/-- The concrete criterion from the two explicit missing statements. -/
theorem s1361ConcreteCriterion_of_xCoordinateFormula_and_zeroCriterion
    (l : PrimeGeFive) (hX : s1361ConcreteXCoordinateFormula l)
    (hZ : s1361ConcreteZeroCriterion l) : s1361ConcreteCriterion l := by
  rw [s1361ConcreteCriterion_iff l]
  exact ⟨s1361Detection_of_xCoordinateFormula (s1361Curve l) hX, hZ⟩

/-- Forward detection for the concrete curve from the x-coordinate formula. -/
theorem s1361ConcreteDetection_of_xCoordinateFormula (l : PrimeGeFive)
    (hX : s1361ConcreteXCoordinateFormula l) : s1361ConcreteDetection l :=
  s1361Detection_of_xCoordinateFormula (s1361Curve l) hX

end Concrete

/-! ## 3. The exact Mathlib gap, checked in this environment

The following #check commands document the available Mathlib interface.  The
#guard_msgs commands record that the corresponding Mathlib declarations are
absent from this checkout.  The absence of omega_n is explicitly acknowledged
by the TODO in Mathlib's DivisionPolynomial/Basic.lean.
-/

section MathlibAPI

#check WeierstrassCurve.preΨ
#check WeierstrassCurve.ΨSq
#check WeierstrassCurve.Φ
#check WeierstrassCurve.ψ
#check WeierstrassCurve.φ
#check WeierstrassCurve.Affine.CoordinateRing.mk_ψ
#check WeierstrassCurve.Affine.CoordinateRing.mk_φ
#check WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq
#check WeierstrassCurve.Affine.Point.toClass
#check WeierstrassCurve.Affine.Point.xRep

/-- error: Unknown constant `WeierstrassCurve.ω` -/
#guard_msgs in
#check WeierstrassCurve.ω

/-- error: Unknown constant `WeierstrassCurve.Affine.CoordinateRing.mk_ω` -/
#guard_msgs in
#check WeierstrassCurve.Affine.CoordinateRing.mk_ω

/-- error: Unknown constant `WeierstrassCurve.Affine.Point.x_nsmul` -/
#guard_msgs in
#check WeierstrassCurve.Affine.Point.x_nsmul

/-- error: Unknown constant `WeierstrassCurve.Affine.Point.nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_eq_zero` -/
#guard_msgs in
#check WeierstrassCurve.Affine.Point.nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_eq_zero

end MathlibAPI

/-! ## 4. Axiom footprint of the new statements -/

#print axioms s1361Criterion_iff
#print axioms s1361Criterion_iff_preΨ_of_odd
#print axioms s1361Detection_of_xCoordinateFormula
#print axioms s1361XCoordinateFormula_one
#print axioms s1361XCoordinateFormula_two
#print axioms s1361Detection_two
#print axioms s1361OneCriterion
#print axioms s1361ZeroCriterion_one
#print axioms s1361Criterion_of_xCoordinateFormula_and_zeroCriterion
#print axioms s1361TwoCriterion
#print axioms s1361ThreeDetection
#print axioms s1361ConcreteCriterion_iff
#print axioms s1361ConcreteCriterion_iff_preΨ
#print axioms s1361ConcreteCriterion_of_xCoordinateFormula_and_zeroCriterion
#print axioms s1361ConcreteDetection_of_xCoordinateFormula

end LeanFormal.IUT.XiFPaper.S1361DivisionCriterionActual
