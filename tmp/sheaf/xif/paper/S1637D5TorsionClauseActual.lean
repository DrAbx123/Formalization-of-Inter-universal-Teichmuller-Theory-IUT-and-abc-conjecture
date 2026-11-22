import tmp.sheaf.xif.paper.S1626AddXYZSmulEvalPortActual
import tmp.sheaf.xif.paper.S1329RankTwoTorsionBasisActual
import tmp.sheaf.xif.paper.S1362PrePsiSeparabilityActual
import tmp.sheaf.xif.paper.S1491NormEDSNetActual
import tmp.sheaf.xif.paper.S1521OmegaInvariantCancellationActual
import tmp.sheaf.xif.paper.S1602PhiNeZeroActual
import tmp.sheaf.xif.paper.S1298TorsionClauseActual
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation

/-!
# S1637: faithful D5 components from the universal point formula

This file assembles the `SourceTorsionClause` components of IUT I, Definition
3.1(c) over the concrete Gaussian input of S1280, and records exactly which of
them are actual and which are independent arithmetic inputs.

## What the recent division-polynomial layer supplies

* S1491: the division-polynomial sequence `ψ` is an elliptic net
  (`isEllipticNet_ψ`); S1521: the invariant identities, the `ω` defining
  identity, and `normEDS_six`, the closed form of `ψ₆`.
* S1602: `φ_n` does not vanish in the universal field and `smulX` separates
  integers up to sign, so the universal point has infinite order.
* S1622/S1626: the TauCeti formula `n • P = (φ_n(P) : ω_n(P) : ψ_n(P))` for an
  arbitrary nonsingular affine point `P` of an arbitrary Weierstrass curve.

That formula is what the earlier S1394/S1329 files lacked: they recorded the
"group-law criterion" `n • P = 0 ↔ ψ_n(P) = 0` as an unproved input.  With the
point formula the criterion is now a theorem (Section 1).  Applied to the
concrete Gaussian curve (Section 2) it removes the criterion hypothesis from
S1329/S1362: the D5 rank-two l-torsion basis is now exactly the separability of
the concrete l-division polynomial `preΨ_l`.

## The four `SourceTorsionClause` fields

* the l-torsion basis: exact type `(Fin 2 → ZMod l) ≃ₗ E[l]`; equivalent to
  `Nat.card E[l] = l^2` and, after Section 1, to separability of `preΨ_l`.
  Still not constructed (Section 4).
* `imageContainsSL2`: the literal containment `SL₂(F_l) ≤ image(ρ_l)` for the
  actual matrix representation on the chosen basis.  Its first missing input is
  the rank-two basis; beyond that it needs the independent Serre open-image
  theorem for this curve (Section 5).
* `sixTorsionIndependent`: the paper condition (b) that the 2·3-torsion is
  rational over `F`, instantiated as `Torsion23Rational` of the actual curve
  (Section 6).  Not constructed.  Section 6 also proves the *independence*
  statement that no nonzero l-torsion point is 6-torsion, which is the part of
  the field name that is available unconditionally.
* `lTorsionCompatible`: the paper condition (c) coprimality of `l` with the bad
  residue characteristics.  This one is *actual*: the only bad place above 5 has
  residue characteristic 5, so the field holds exactly for `l ≠ 5` and is
  refuted at `l = 5` (Section 7).  Consequently the faithful D5 gap over this
  curve is empty at `l = 5`.

No fake basis, no `True` image field, no `PUnit`, no axiom and no `sorry` is used.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

namespace LeanFormal.IUT.XiFPaper.S1637D5TorsionClauseActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.TorsionCarrierReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1626AddXYZSmulEvalPortActual
open LeanFormal.IUT.XiFPaper.S1329RankTwoTorsionBasisActual
open LeanFormal.IUT.XiFPaper.S1362PrePsiSeparabilityActual
open LeanFormal.IUT.XiFPaper.S1298TorsionClauseActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.NumberFieldFinitePlace

variable {F : Type*} [Field F]

/-! ## 1. The pointwise group-law criterion, from the universal point formula -/

/-- The third coordinate of the evaluated universal triple is `ψₙ(x, y)`. -/
theorem s1637SmulEval_z (W : WeierstrassCurve F) (x y : F) (n : ℤ) :
    s1626SmulEval W x y n 2 = (W.ψ n).evalEval x y :=
  rfl

/-- **A root of `ψₙ` annihilates the point.**  This is TauCeti's
`zsmul_eq_zero_of_evalEval_ψ_eq_zero`, derived from the point formula
`n • P = [φₙ : ωₙ : ψₙ]` and the fact that a nonsingular class with vanishing
`Z`-coordinate is the point at infinity. -/
theorem s1637ZsmulEqZeroOfEvalPsi (W : WeierstrassCurve F) {x y : F}
    (hns : W.toAffine.Nonsingular x y) (n : ℤ)
    (hψ : (W.ψ n).evalEval x y = 0) :
    n • (Jacobian.Point.fromAffine (Affine.Point.some x y hns)) = 0 := by
  have heval := s1626ZSMulPointEqSmulEval W hns n
  rw [Jacobian.Point.ext_iff, heval, Jacobian.Point.zero_point]
  refine Quotient.sound (Jacobian.equiv_zero_of_Z_eq_zero (W := W) ?_ ?_)
  · rw [← Jacobian.nonsingularLift_iff, ← heval]
    exact (n • Jacobian.Point.fromAffine (Affine.Point.some x y hns)).nonsingular
  · rw [s1637SmulEval_z]
    exact hψ

/-- **An `n`-torsion point is a root of `ψₙ`.**  Converse of the previous
statement, through the same point formula. -/
theorem s1637EvalPsiEqZeroOfZsmul (W : WeierstrassCurve F) {x y : F}
    (hns : W.toAffine.Nonsingular x y) (n : ℤ)
    (hP : n • (Jacobian.Point.fromAffine (Affine.Point.some x y hns)) = 0) :
    (W.ψ n).evalEval x y = 0 := by
  have heval := s1626ZSMulPointEqSmulEval W hns n
  rw [Jacobian.Point.ext_iff] at hP
  rw [heval, Jacobian.Point.zero_point] at hP
  have hZ : s1626SmulEval W x y n 2 = 0 :=
    (Jacobian.Z_eq_zero_of_equiv (Quotient.exact hP)).mpr rfl
  rwa [s1637SmulEval_z] at hZ

/-- The square bridge: on the curve, `ψₙ² = ΨSqₙ(x)`. -/
theorem s1637EvalPsiSq (W : WeierstrassCurve F) {x y : F}
    (h : W.toAffine.Equation x y) (n : ℤ) :
    (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x := by
  have h1 : (W.ψ n).evalEval x y = (W.Ψ n).evalEval x y :=
    W.evalDivisionPolynomial_eq_evalEval_Ψ h n
  rw [h1, W.evalEval_Ψ_sq_eq_eval_ΨSq h n]

/-- **The pointwise criterion: `ΨSqₙ(x) = 0` exactly when `P` is `n`-torsion.** -/
theorem s1637EvalPsiSqEqZeroIffZsmul (W : WeierstrassCurve F) {x y : F}
    (hns : W.toAffine.Nonsingular x y) (n : ℤ) :
    (W.ΨSq n).eval x = 0 ↔
      n • (Jacobian.Point.fromAffine (Affine.Point.some x y hns)) = 0 := by
  rw [← s1637EvalPsiSq W hns.1 n, pow_eq_zero_iff two_ne_zero]
  exact ⟨s1637ZsmulEqZeroOfEvalPsi W hns n, s1637EvalPsiEqZeroOfZsmul W hns n⟩

/-- The same criterion in `ψ` form, both directions. -/
theorem s1637EvalPsiEqZeroIffZsmul (W : WeierstrassCurve F) {x y : F}
    (hns : W.toAffine.Nonsingular x y) (n : ℤ) :
    (W.ψ n).evalEval x y = 0 ↔
      n • (Jacobian.Point.fromAffine (Affine.Point.some x y hns)) = 0 :=
  ⟨s1637ZsmulEqZeroOfEvalPsi W hns n, s1637EvalPsiEqZeroOfZsmul W hns n⟩

/-- Torsion does not see the affine/Jacobian coordinate change. -/
theorem s1637ZsmulFromAffine [DecidableEq F] (W : WeierstrassCurve F)
    {P : Affine.Point W} {n : ℤ} :
    n • Jacobian.Point.fromAffine P = 0 ↔ n • P = 0 := by
  let e := Jacobian.Point.toAffineAddEquiv W
  have h : e (n • Jacobian.Point.fromAffine P) = n • P := by
    rw [map_zsmul]
    congr 1
    exact AddEquiv.apply_symm_apply e P
  rw [← h, AddEquiv.map_eq_zero_iff e]

/-- **The group-law criterion of S1329 at every natural number.**  This is the
statement S1329/S1362/S1578 recorded as an unproved input; it now follows from
the point formula. -/
theorem s1637DivisionCriterion [DecidableEq F] (W : WeierstrassCurve.Affine F) (n : ℕ) :
    s1329DivisionCriterion W n := by
  intro P
  rcases P with _ | ⟨x, y, hns⟩
  · constructor
    · intro _
      rfl
    · intro _
      exact zsmul_zero (α := W.Point) (n : ℤ)
  · rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some]
    rw [show W.evalDivisionPolynomial x y (n : ℤ) = (W.ψ (n : ℤ)).evalEval x y from rfl]
    constructor
    · intro hP
      have hJ : (n : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some x y hns) = 0 :=
        (s1637ZsmulFromAffine W).mpr hP
      have hsq := (s1637EvalPsiSqEqZeroIffZsmul W hns (n : ℤ)).mpr hJ
      rw [← s1637EvalPsiSq W hns.1 (n : ℤ)] at hsq
      exact (pow_eq_zero_iff two_ne_zero).mp hsq
    · intro hψ
      have hsq : (W.ΨSq (n : ℤ)).eval x = 0 := by
        rw [← s1637EvalPsiSq W hns.1 (n : ℤ), pow_eq_zero_iff two_ne_zero]
        exact hψ
      exact (s1637ZsmulFromAffine W).mp
        ((s1637EvalPsiSqEqZeroIffZsmul W hns (n : ℤ)).mp hsq)

/-! ## 2. The concrete Gaussian criterion and the exact D5 reduction -/

local instance s1637GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s1637ClosureDecEq (l : PrimeGeFive) :
    DecidableEq (S1329Closure l) :=
  Classical.decEq _

/-- **The S1329 concrete group-law criterion, now a theorem.** -/
theorem s1637ConcreteCriterion (l : PrimeGeFive) : S1329ConcreteCriterion l :=
  s1637DivisionCriterion (S1329Curve l) l.value

/-- The exact count of the actual l-torsion, with no criterion hypothesis. -/
theorem s1637NatCard_eq (l : PrimeGeFive) :
    Nat.card (S1298TorsionCarrier l) =
      1 + 2 * (s1329RootFinset (S1329Curve l) l.value).card :=
  s1329ConcreteNatCard_eq l (s1637ConcreteCriterion l)

/-- **The D5 first field is exactly the separability of the concrete
l-division polynomial.**  This is S1329's sharp reduction with its criterion
hypothesis discharged. -/
theorem s1637Basis_iff_separable (l : PrimeGeFive) :
    Nonempty (S1329TorsionBasis l) ↔ S1329ConcreteSeparable l :=
  s1329ConcreteBasis_iff_separable l (s1637ConcreteCriterion l)

/-- The basis field is exactly the separability of `preΨ_l`. -/
theorem s1637Basis_iff_prePsiSeparable (l : PrimeGeFive) :
    Nonempty (S1329TorsionBasis l) ↔ S1362PreΨSeparable l :=
  (s1637Basis_iff_separable l).trans
    ((s1362RootCount_iff_s1329ConcreteSeparable l).symm.trans
      (s1362RootCount_iff_separable l))

/-- The basis field is exactly the numerical cardinality `Nat.card E[l] = l^2`. -/
theorem s1637Basis_iff_natCard (l : PrimeGeFive) :
    Nonempty (S1329TorsionBasis l) ↔
      Nat.card (S1298TorsionCarrier l) = l.value ^ 2 :=
  (s1637Basis_iff_separable l).trans
    (s1329ConcreteNatCard_eq_sq_iff l (s1637ConcreteCriterion l)).symm

/-- The conditional basis construction, with the criterion discharged: the
separability of `preΨ_l` is now the *only* missing input. -/
theorem s1637Basis_of_separable (l : PrimeGeFive) (hsep : S1329ConcreteSeparable l) :
    Nonempty (S1298TorsionBasisType l) :=
  s1329ConcreteBasis_of_criterion_and_separable l (s1637ConcreteCriterion l) hsep

/-! ## 3. The direct uses of S1491, S1521 and S1602 -/

-- S1491: the division-polynomial sequence of every Weierstrass curve is an
-- elliptic net.  This is the net structure the S1593/S16xx layer consumes.
#check @isEllipticNet_ψ

-- S1602: the x-coordinates of the multiples of the universal point separate
-- the integers up to sign, which is what makes the universal point of infinite
-- order (consumed by S1622 through `s1626ZSMulPoint_injective`).
#check @WeierstrassCurve.Universal.s1602SmulX_eq_smulX_iff
#check @LeanFormal.IUT.XiFPaper.S1626AddXYZSmulEvalPortActual.s1626ZSMulPoint_injective

/-- **S1521's `normEDS_six` at the curve**: the sixth division polynomial is
the product of the second, the third and `ψ₅ - preΨ₄²`. -/
theorem s1637PsiSix {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    W.ψ 6 = (W.ψ 5 - (C W.preΨ₄) ^ 2) * W.ψ₂ * C W.Ψ₃ := by
  have h : W.ψ = _root_.normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) :=
    WeierstrassCurve.ψ_eq_normEDS W
  rw [h]
  exact WeierstrassCurve.normEDS_six _ _ _

/-- **The six-torsion criterion**, from Section 1 at `n = 6`. -/
theorem s1637SixTorsionCriterion (W : WeierstrassCurve F) {x y : F}
    (hns : W.toAffine.Nonsingular x y) :
    (6 : ℤ) • (Jacobian.Point.fromAffine (Affine.Point.some x y hns)) = 0 ↔
      (W.ψ 6).evalEval x y = 0 :=
  (s1637EvalPsiEqZeroIffZsmul W hns 6).symm

/-! ## 4. The l-torsion basis field -/

/-- The exact D5 basis field, over the concrete Gaussian curve. -/
abbrev S1637TorsionBasis (l : PrimeGeFive) : Type :=
  (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] (S1280Arithmetic l).curve.LTorsion l

/-- It is literally the S1298/S1329 type. -/
theorem s1637TorsionBasis_eq_s1298 (l : PrimeGeFive) :
    S1637TorsionBasis l = S1298TorsionBasisType l := rfl

/-- The exact equivalence of the basis field with the cardinality. -/
theorem s1637TorsionBasis_nonempty_iff_natCard (l : PrimeGeFive) :
    Nonempty (S1637TorsionBasis l) ↔
      Nat.card ((S1280Arithmetic l).curve.LTorsion l) = l.value ^ 2 :=
  s1637Basis_iff_natCard l

/-- The exact equivalence of the basis field with `preΨ_l` separability. -/
theorem s1637TorsionBasis_nonempty_iff_separable (l : PrimeGeFive) :
    Nonempty (S1637TorsionBasis l) ↔ S1362PreΨSeparable l :=
  s1637Basis_iff_prePsiSeparable l

/-- Exact first missing object of the torsion side: the basis itself.  The
type is honest (a linear equivalence), and no inhabitant is asserted. -/
def S1637TorsionBasisMissing (l : PrimeGeFive) : Prop :=
  Nonempty (S1637TorsionBasis l)

theorem s1637TorsionBasisMissing_iff (l : PrimeGeFive) :
    S1637TorsionBasisMissing l ↔ Nonempty (S1637TorsionBasis l) := Iff.rfl

/-! ## 5. The image field -/

/-- The literal `SL₂` containment for the actual matrix representation attached
to a chosen rank-two basis.  This is the first tail field of the source D5
datum `SourceTorsionDatum`. -/
def S1637ImageContainsSL2 (l : PrimeGeFive) (b : S1637TorsionBasis l) : Prop :=
  Subgroup.map Matrix.SpecialLinearGroup.toGL
    (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
    ((S1280Arithmetic l).curve.galoisLTorsionMatrixRepresentation l b).range

/-- The Serre-style large-image statement is the existential over the actual
basis; this is definitionally the source card. -/
theorem s1637ImageContainsSL2_exists_iff (l : PrimeGeFive) :
    (∃ b : S1637TorsionBasis l, S1637ImageContainsSL2 l b) ↔
      SerreStyleLargeImageStatement (S1280Arithmetic l).curve l :=
  Iff.rfl

/-- The large-image statement has the basis as its first field. -/
theorem s1637LargeImage_basis (l : PrimeGeFive)
    (h : SerreStyleLargeImageStatement (S1280Arithmetic l).curve l) :
    Nonempty (S1637TorsionBasis l) :=
  ⟨h.choose⟩

/-- Any proof of the containment for a basis has that basis as its witness. -/
theorem s1637ImageContainsSL2_basis (l : PrimeGeFive) (b : S1637TorsionBasis l)
    (h : S1637ImageContainsSL2 l b) : Nonempty (S1637TorsionBasis l) :=
  ⟨b⟩

/-- **The exact first missing field of `imageContainsSL2`**: the rank-two
basis.  Once a basis is supplied, the remaining content is the Serre
open-image statement for the concrete curve, which is the independent
arithmetic input (no version of it exists in the tree; the only unconditional
odd-level rank-two basis in the tree is for the different curve
`y^2 = x^3 - x` at `l = 3`). -/
def S1637LargeImageMissing (l : PrimeGeFive) : Prop :=
  SerreStyleLargeImageStatement (S1280Arithmetic l).curve l

theorem s1637LargeImageMissing_iff (l : PrimeGeFive) :
    S1637LargeImageMissing l ↔
      ∃ b : S1637TorsionBasis l, S1637ImageContainsSL2 l b :=
  Iff.rfl

/-! ## 6. The six-torsion field -/

/-- The paper's condition (b): every 2·3-torsion point is rational over the
base field.  This is the literal `Torsion23Rational` of the actual curve. -/
def S1637SixTorsionIndependent (l : PrimeGeFive) : Prop :=
  PuncturedEllipticCurve.Torsion23Rational (S1280Arithmetic l).curve

theorem s1637SixTorsionIndependent_iff (l : PrimeGeFive) :
    S1637SixTorsionIndependent l ↔
      PuncturedEllipticCurve.Torsion23Rational (S1280Arithmetic l).curve :=
  Iff.rfl

/- **Audit note (not formalized here).**  The paper condition (b) is *refuted*
for the concrete Gaussian curve `y^2 + xy = x^3 + 5` over `Q(i)`:
the 2-torsion points are `(x, -x/2)` with `4x^3 + x^2 + 20 = 0`, so a
rational 2-torsion point would give a root of that cubic in `Q(i)`.  The cubic
has no rational root (rational root test), hence is irreducible over `Q`; if
`z ∈ Q(i)` were a root, its conjugate would be a root as well and the third
root would be `-1/4 - z - z̄ ∈ Q(i) ∩ Q`, a rational root, a contradiction.
An independent computer-algebra check confirms that the cubic is irreducible
over `Q`.  Consequently `Torsion23Rational` of this curve is false and the
faithful D5 gap over this curve is empty for this second, curve-intrinsic
reason as well.  The formalization would need (i) the 2-torsion coordinate
computation, (ii) the base-change/descent x-coordinate lemma, and (iii) the
rational-root test for `4X^3 + X^2 + 20`; none of the three is in the tree, so
this file only records the argument.

The *independence* half of the field name is nevertheless actual, see
`s1637SixTorsion_disjoint_lTorsion` below. -/
/-- The exact target of the audit note above: the negation of the paper
condition (b) for the concrete curve.  Not proved in this file. -/
def S1637SixTorsionRationalityRefuted (l : PrimeGeFive) : Prop :=
  ¬ S1637SixTorsionIndependent l

/-- The unconditional *independence* content of the field name: no nonzero
l-torsion point is 6-torsion.  This is proved from the group structure, since
`l ≥ 5` is prime to 6. -/
theorem s1637SixTorsion_disjoint_lTorsion (l : PrimeGeFive)
    {x y : S1329Closure l} (hns : (S1329Curve l).toAffine.Nonsingular x y)
    (hl : l.value • (Affine.Point.some x y hns) = 0)
    (h6 : 6 • (Affine.Point.some x y hns) = 0) :
    False := by
  have hdvd_l : addOrderOf (Affine.Point.some x y hns) ∣ l.value :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr hl
  have hdvd_6 : addOrderOf (Affine.Point.some x y hns) ∣ 6 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr h6
  have hgcd : addOrderOf (Affine.Point.some x y hns) ∣ Nat.gcd 6 l.value :=
    Nat.dvd_gcd hdvd_6 hdvd_l
  have h2 : Nat.Coprime 2 l.value :=
    (Nat.coprime_primes Nat.prime_two l.prime).mpr (by have := l.ge_five; omega)
  have h3 : Nat.Coprime 3 l.value :=
    (Nat.coprime_primes Nat.prime_three l.prime).mpr (by have := l.ge_five; omega)
  have h6cop : Nat.Coprime 6 l.value := by
    rw [show (6 : Nat) = 2 * 3 by norm_num, Nat.coprime_mul_iff_left]
    exact ⟨h2, h3⟩
  have hg : Nat.gcd 6 l.value = 1 := h6cop
  rw [hg] at hgcd
  have hone : addOrderOf (Affine.Point.some x y hns) = 1 := Nat.dvd_one.mp hgcd
  exact Affine.Point.some_ne_zero hns (AddMonoid.addOrderOf_eq_one_iff.mp hone)

/-! ## 7. The clause-(c) coprimality field -/

/-- The literal clause (c) condition of Definition 3.1: `l` is prime to the
residue characteristics of the bad moduli places.  This is exactly the
`paperLTorsionCompatible` statement specialized to the actual S1280 selection. -/
def S1637LTorsionCompatible (l : PrimeGeFive) : Prop :=
  ∀ p : NumberField.FinitePlace (S1280Arithmetic l).Fmod,
    p ∈ (S1280Selection l).V_mod_bad →
      Nat.Coprime l.value (NumberFieldFinitePlace.residueCharacteristic p)

/-- **The field is actual**: since the only bad place is the place above 5, the
condition is exactly `l ≠ 5`. -/
theorem s1637LTorsionCompatible_iff (l : PrimeGeFive) :
    S1637LTorsionCompatible l ↔ l.value ≠ 5 := by
  constructor
  · intro h h5
    rcases (S1280Selection l).V_mod_bad_nonempty with ⟨p, hp⟩
    have hcop := h p hp
    have hp_eq : p = concreteGaussianFivePlace := by
      have hmem := hp
      rw [S1280Selection_V_mod_bad] at hmem
      exact Set.eq_of_mem_singleton hmem
    rw [hp_eq] at hcop
    rw [show (concreteGaussianFivePlace : NumberField.FinitePlace (S1280Arithmetic l).Fmod) =
        S1280Place l from rfl] at hcop
    rw [S1280Place_residueCharacteristic l, h5] at hcop
    exact absurd hcop (by decide)
  · intro h5 p hp
    have hp_eq : p = concreteGaussianFivePlace := by
      have hmem := hp
      rw [S1280Selection_V_mod_bad] at hmem
      exact Set.eq_of_mem_singleton hmem
    rw [hp_eq]
    rw [show (concreteGaussianFivePlace : NumberField.FinitePlace (S1280Arithmetic l).Fmod) =
        S1280Place l from rfl]
    rw [S1280Place_residueCharacteristic l]
    exact (Nat.coprime_primes l.prime Nat.prime_five).mpr h5

/-- The actual proof of the field for every `l ≠ 5`. -/
theorem s1637LTorsionCompatible_of_ne_five (l : PrimeGeFive) (h5 : l.value ≠ 5) :
    S1637LTorsionCompatible l :=
  (s1637LTorsionCompatible_iff l).mpr h5

/-- The field is refuted at `l = 5`: the bad residue characteristic is 5. -/
theorem s1637LTorsionCompatible_refuted_at_five :
    ¬ S1637LTorsionCompatible S1280Five := by
  intro h
  exact (s1637LTorsionCompatible_iff S1280Five).mp h S1280Five_value

/-! ## 8. The faithful D5 clause -/

/-- The exact gap of the faithful D5 clause over the concrete Gaussian curve:
the four fields of `SourceTorsionClause` beyond the actual carriers, label and
general-linear representation. -/
structure S1637D5Gap (l : PrimeGeFive) where
  /-- The rank-two l-torsion basis (the first missing field). -/
  basis : S1637TorsionBasis l
  /-- The literal `SL₂` containment for the actual matrix representation. -/
  largeImage : S1637ImageContainsSL2 l basis
  /-- The paper condition (b): 2·3-torsion rationality. -/
  sixTorsion : S1637SixTorsionIndependent l
  /-- The paper condition (c): coprimality with the bad residue characteristics. -/
  lCompatible : S1637LTorsionCompatible l

/-- **The faithful `SourceTorsionClause`.**  The carrier, its primitive-root
`Fin 6` label, the absolute Galois group, the actual general-linear
representation on `E[l]`, its range and the range-restricted surjection are the
actual S1298 objects; the four remaining fields are the exact gap. -/
noncomputable def s1637SourceTorsionClause (l : PrimeGeFive) (G : S1637D5Gap l) :
    SourceTorsionClause.{0, 0, 0} l where
  torsionCarrier := S1298SixTorsionCarrier l
  torsionCarrierLaw := s1298SixTorsionCarrierGroup l
  torsionLabel := s1298SixTorsionLabel l
  torsionNonempty := ⟨1⟩
  representationCarrier := SourceAbsoluteGalois (S1280Arithmetic l)
  representationCarrierLaw := inferInstance
  representationGroup := S1298RepresentationGroup l
  representationGroupLaw := inferInstance
  representation := S1298Representation l
  representation_surjective :=
    (S1298GeneralLinearRepresentation l).rangeRestrict_surjective
  imageContainsSL2 := S1637ImageContainsSL2 l G.basis
  imageContainsSL2_proved := G.largeImage
  sixTorsionIndependent := S1637SixTorsionIndependent l
  sixTorsionIndependent_proved := G.sixTorsion
  lTorsionCompatible := S1637LTorsionCompatible l
  lTorsionCompatible_proved := G.lCompatible

@[simp] theorem s1637SourceTorsionClause_torsionCarrier (l : PrimeGeFive)
    (G : S1637D5Gap l) :
    (s1637SourceTorsionClause l G).torsionCarrier = S1298SixTorsionCarrier l := rfl

@[simp] theorem s1637SourceTorsionClause_torsionLabel (l : PrimeGeFive)
    (G : S1637D5Gap l) :
    (s1637SourceTorsionClause l G).torsionLabel = s1298SixTorsionLabel l := rfl

@[simp] theorem s1637SourceTorsionClause_representation (l : PrimeGeFive)
    (G : S1637D5Gap l) :
    (s1637SourceTorsionClause l G).representation = S1298Representation l := rfl

@[simp] theorem s1637SourceTorsionClause_imageContainsSL2 (l : PrimeGeFive)
    (G : S1637D5Gap l) :
    (s1637SourceTorsionClause l G).imageContainsSL2 =
      S1637ImageContainsSL2 l G.basis := rfl

@[simp] theorem s1637SourceTorsionClause_sixTorsionIndependent (l : PrimeGeFive)
    (G : S1637D5Gap l) :
    (s1637SourceTorsionClause l G).sixTorsionIndependent =
      S1637SixTorsionIndependent l := rfl

@[simp] theorem s1637SourceTorsionClause_lTorsionCompatible (l : PrimeGeFive)
    (G : S1637D5Gap l) :
    (s1637SourceTorsionClause l G).lTorsionCompatible =
      S1637LTorsionCompatible l := rfl

/-- The first field of the clause is the basis. -/
theorem s1637SourceTorsionClause_basis (l : PrimeGeFive) (G : S1637D5Gap l) :
    Nonempty (S1637TorsionBasis l) := ⟨G.basis⟩

/-- The basis of the clause is, by Section 2, a separability statement. -/
theorem s1637SourceTorsionClause_separable (l : PrimeGeFive) (G : S1637D5Gap l) :
    S1362PreΨSeparable l :=
  (s1637TorsionBasis_nonempty_iff_separable l).mp ⟨G.basis⟩

/-- Exact decomposition of the gap. -/
theorem s1637D5Gap_nonempty_iff (l : PrimeGeFive) :
    Nonempty (S1637D5Gap l) ↔
      (∃ b : S1637TorsionBasis l, S1637ImageContainsSL2 l b) ∧
        S1637SixTorsionIndependent l ∧ S1637LTorsionCompatible l := by
  constructor
  · rintro ⟨G⟩
    exact ⟨⟨G.basis, G.largeImage⟩, G.sixTorsion, G.lCompatible⟩
  · rintro ⟨⟨b, hb⟩, h6, hc⟩
    exact ⟨⟨b, hb, h6, hc⟩⟩

/-- At `l ≠ 5` the clause-(c) field is automatic, so the gap is exactly the
basis-plus-image and the six-torsion rationality. -/
theorem s1637D5Gap_nonempty_iff_of_ne_five (l : PrimeGeFive) (h5 : l.value ≠ 5) :
    Nonempty (S1637D5Gap l) ↔
      (∃ b : S1637TorsionBasis l, S1637ImageContainsSL2 l b) ∧
        S1637SixTorsionIndependent l := by
  rw [s1637D5Gap_nonempty_iff]
  constructor
  · rintro ⟨hbi, h6, _⟩
    exact ⟨hbi, h6⟩
  · rintro ⟨hbi, h6⟩
    exact ⟨hbi, h6, s1637LTorsionCompatible_of_ne_five l h5⟩

/-- **The faithful D5 gap is impossible at `l = 5`** over the concrete Gaussian
arithmetic input, because the only bad place has residue characteristic 5. -/
theorem s1637D5Gap_impossible_at_five : ¬ Nonempty (S1637D5Gap S1280Five) := by
  rintro ⟨G⟩
  exact s1637LTorsionCompatible_refuted_at_five G.lCompatible


/-! ## 9. Summary of the exact gap and axiom footprint -/

/-- The three clause fields of the assembled clause, restated. -/
theorem s1637SourceTorsionClause_allFields (l : PrimeGeFive) (G : S1637D5Gap l) :
    (s1637SourceTorsionClause l G).imageContainsSL2 ∧
      (s1637SourceTorsionClause l G).sixTorsionIndependent ∧
      (s1637SourceTorsionClause l G).lTorsionCompatible :=
  ⟨G.largeImage, G.sixTorsion, G.lCompatible⟩

/-- The exact first missing field of the whole D5 gap: the rank-two basis.
Every other field is conditional on it (`imageContainsSL2`) or independent of it
(`sixTorsionIndependent`, `lTorsionCompatible`). -/
def S1637D5FirstMissing (l : PrimeGeFive) : Prop :=
  Nonempty (S1637TorsionBasis l)

theorem s1637D5FirstMissing_iff (l : PrimeGeFive) :
    S1637D5FirstMissing l ↔ S1362PreΨSeparable l :=
  s1637TorsionBasis_nonempty_iff_separable l

/-- Even with the basis supplied, the image field is an independent arithmetic
input: it is the Serre large-image statement for the concrete curve.  This is
the exact type that must be produced, and it is not derivable from the
torsion/cardinality machinery. -/
def S1637ImageArithmeticInput (l : PrimeGeFive) : Prop :=
  S1637LargeImageMissing l

theorem s1637ImageArithmeticInput_iff (l : PrimeGeFive) :
    S1637ImageArithmeticInput l ↔
      ∃ b : S1637TorsionBasis l, S1637ImageContainsSL2 l b :=
  Iff.rfl

/-- The large-image statement forces the torsion-side gap: it supplies a basis,
hence `preΨ_l` is separable.  This is the exact sense in which the Serre
arithmetic input sits *above* the torsion gap rather than beside it. -/
theorem s1637LargeImage_implies_separable (l : PrimeGeFive)
    (h : S1637LargeImageMissing l) : S1362PreΨSeparable l :=
  (s1637TorsionBasis_nonempty_iff_separable l).mp
    (s1637LargeImage_basis l h)

/-- The full conditional chain of the D5 clause: a witness of the image
arithmetic input, the paper condition (b), and the clause-(c) coprimality give
the faithful `SourceTorsionClause`. -/
theorem s1637Clause_of_fields (l : PrimeGeFive)
    (hI : S1637ImageArithmeticInput l)
    (h6 : S1637SixTorsionIndependent l)
    (hc : S1637LTorsionCompatible l) :
    ∃ T : SourceTorsionClause.{0, 0, 0} l,
      T.imageContainsSL2 ∧ T.sixTorsionIndependent ∧ T.lTorsionCompatible := by
  obtain ⟨b, hb⟩ := s1637ImageArithmeticInput_iff l |>.mp hI
  exact ⟨s1637SourceTorsionClause l ⟨b, hb, h6, hc⟩,
    s1637SourceTorsionClause_allFields l ⟨b, hb, h6, hc⟩⟩

#print axioms s1637SmulEval_z
#print axioms s1637ZsmulEqZeroOfEvalPsi
#print axioms s1637EvalPsiEqZeroOfZsmul
#print axioms s1637EvalPsiSqEqZeroIffZsmul
#print axioms s1637DivisionCriterion
#print axioms s1637ConcreteCriterion
#print axioms s1637NatCard_eq
#print axioms s1637Basis_iff_separable
#print axioms s1637Basis_iff_prePsiSeparable
#print axioms s1637Basis_iff_natCard
#print axioms s1637PsiSix
#print axioms s1637SixTorsionCriterion
#print axioms s1637SixTorsion_disjoint_lTorsion
#print axioms s1637LTorsionCompatible_iff
#print axioms s1637LTorsionCompatible_refuted_at_five
#print axioms s1637SourceTorsionClause
#print axioms s1637SourceTorsionClause_allFields
#print axioms s1637D5Gap_nonempty_iff
#print axioms s1637D5Gap_impossible_at_five
#print axioms s1637D5FirstMissing_iff
#print axioms s1637LargeImage_implies_separable
#print axioms s1637Clause_of_fields

end LeanFormal.IUT.XiFPaper.S1637D5TorsionClauseActual

end