import tmp.sheaf.xif.paper.S1329RankTwoTorsionBasisActual
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# S1362: separability and the exact root count of the concrete l-division polynomial

This file attacks the second exact mathematical field isolated by
`S1329RankTwoTorsionBasisActual`: for the concrete Gaussian curve
`y ^ 2 + x * y = x ^ 3 + 5` over `AlgebraicClosure (GaussianField)`, the odd
`l`-division polynomial `prePsi_l` should have exactly `(l ^ 2 - 1) / 2`
distinct roots, equivalently it should be separable (equivalently squarefree).

## What is proved unconditionally here

1. `s1362PrePsi_natDegree`: `natDegree (prePsi_l) = (l ^ 2 - 1) / 2`, from
   Mathlib's division-polynomial degree formula (Degree.lean), using only
   `l != 0` in the characteristic-zero closure and oddness of `l`.
2. `s1362PrePsi_splits`: `prePsi_l` splits over the algebraic closure.
3. `s1362RootFinset_card_le`: the root finset has at most the degree
   `(l ^ 2 - 1) / 2` elements, with no separability input.
4. The exact equivalences
   `root count = (l ^ 2 - 1) / 2`
     <-> `prePsi_l.roots.Nodup`
     <-> `prePsi_l.Separable`
     <-> `Squarefree prePsi_l`.
   These use Mathlib's `nodup_roots_iff_of_splits` and the standard
   perfect-field equivalence `separable_iff_squarefree`; no group-law input is
   used.  Thus the *only* missing polynomial statement is separability (or,
   equivalently, squarefreeness / simple roots); the degree, splitting and the
   upper bound are already unconditional.

## Exact l-torsion-theoretic boundary

Under the S1329 group-law criterion `l • P = 0 <-> psi_l(P) = 0`, the root
count is exactly the D5 l-torsion cardinality:
`S1362RootCount l <-> Nat.card (S1298TorsionCarrier l) = l ^ 2`
(and, equivalently, the rank-two basis is inhabited).  Conversely, the
l-torsion cardinality plus the criterion implies separability.  Hence the
second exact field is equivalent, given the criterion, to the frozen
cardinality `#E[l] = l ^ 2`; neither that cardinality nor the group-law
criterion is proved in Mathlib 4.32.2 or in the tree.

The single missing lemma for the polynomial half is therefore

* `S1362PreΨSeparable l : (S1362PreΨ l).Separable`,

equivalently `Squarefree (S1362PreΨ l)`, and, under the criterion,
equivalent to `S1298TorsionCardinalityCard l`.  No inhabitant, axiom, or
placeholder is asserted here.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1362PrePsiSeparabilityActual

open Polynomial
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1298TorsionClauseActual
open LeanFormal.IUT.XiFPaper.S1329RankTwoTorsionBasisActual

local instance s1362GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- Decidable equality on the Gaussian closure, from classical logic. -/
local instance s1362ClosureDecEq (l : PrimeGeFive) :
    DecidableEq (S1329Closure l) :=
  Classical.decEq _

/-! ## 1. The concrete polynomial and the target predicates -/

/-- The algebraic closure of the Gaussian field used by the concrete input. -/
abbrev S1362Closure (l : PrimeGeFive) : Type := S1329Closure l

/-- The affine concrete curve over the Gaussian closure. -/
abbrev S1362Curve (l : PrimeGeFive) : WeierstrassCurve.Affine (S1362Closure l) :=
  S1329Curve l

/-- The concrete odd `l`-division polynomial. -/
def S1362PreΨ (l : PrimeGeFive) : Polynomial (S1362Closure l) :=
  (S1362Curve l).preΨ (l.value : ℤ)

/-- The root count of the concrete division polynomial. -/
def S1362RootCount (l : PrimeGeFive) : Prop :=
  (S1362PreΨ l).roots.toFinset.card = (l.value ^ 2 - 1) / 2

/-- The polynomial separability statement. -/
def S1362PreΨSeparable (l : PrimeGeFive) : Prop :=
  (S1362PreΨ l).Separable

/-- The squarefree form of the same statement. -/
def S1362PreΨSquarefree (l : PrimeGeFive) : Prop :=
  Squarefree (S1362PreΨ l)

/-- The root-count statement is literally the S1329 separability statement. -/
theorem s1362RootCount_iff_s1329ConcreteSeparable (l : PrimeGeFive) :
    S1362RootCount l ↔ S1329ConcreteSeparable l :=
  Iff.rfl

/-! ## 2. Unconditional degree, splitting, and the upper bound -/

/-- `prePsi_l` is nonzero: its leading coefficient is `l`, nonzero in the
characteristic-zero closure. -/
theorem s1362PreΨ_ne_zero (l : PrimeGeFive) : S1362PreΨ l ≠ 0 := by
  unfold S1362PreΨ S1362Curve
  exact WeierstrassCurve.preΨ_ne_zero (W := S1329Curve l) (by
    simpa using s1329Concrete_l_ne_zero l)

/-- Mathlib's degree formula specialised to the concrete curve:
`natDegree (prePsi_l) = (l ^ 2 - 1) / 2` for odd `l`. -/
theorem s1362PreΨ_natDegree (l : PrimeGeFive) :
    (S1362PreΨ l).natDegree = (l.value ^ 2 - 1) / 2 := by
  unfold S1362PreΨ S1362Curve
  rw [WeierstrassCurve.natDegree_preΨ (W := S1329Curve l) (n := (l.value : ℤ)) (by
    simpa using s1329Concrete_l_ne_zero l)]
  rw [if_neg (s1329Concrete_odd_int l)]
  simp

/-- Over the algebraically closed Gaussian closure, `prePsi_l` splits. -/
theorem s1362PreΨ_splits (l : PrimeGeFive) : (S1362PreΨ l).Splits := by
  unfold S1362PreΨ
  exact IsAlgClosed.splits _

/-- Unconditional upper bound: the root finset has at most the degree
`(l ^ 2 - 1) / 2` elements.  No separability is assumed. -/
theorem s1362RootFinset_card_le (l : PrimeGeFive) :
    (S1362PreΨ l).roots.toFinset.card ≤ (l.value ^ 2 - 1) / 2 := by
  rw [← s1362PreΨ_natDegree l]
  calc (S1362PreΨ l).roots.toFinset.card ≤ (S1362PreΨ l).roots.card :=
        Multiset.toFinset_card_le _
    _ ≤ (S1362PreΨ l).natDegree := Polynomial.card_roots' _

/-! ## 3. The exact polynomial equivalences -/

/-- Full root count is exactly the statement that the root multiset has no
repeated roots. -/
theorem s1362RootCount_iff_roots_nodup (l : PrimeGeFive) :
    S1362RootCount l ↔ (S1362PreΨ l).roots.Nodup := by
  have hsplit : (S1362PreΨ l).Splits := s1362PreΨ_splits l
  unfold S1362RootCount
  rw [← s1362PreΨ_natDegree l]
  change (S1362PreΨ l).roots.toFinset.card = (S1362PreΨ l).natDegree ↔
    (S1362PreΨ l).roots.Nodup
  rw [hsplit.natDegree_eq_card_roots]
  exact Multiset.toFinset_card_eq_card_iff_nodup

/-- Full root count is equivalent to separability.  This is the unconditional
bridge from the numerical root count to the polynomial property; it uses only
degree, splitting, and Mathlib's `nodup_roots_iff_of_splits`. -/
theorem s1362RootCount_iff_separable (l : PrimeGeFive) :
    S1362RootCount l ↔ S1362PreΨSeparable l := by
  have hp : S1362PreΨ l ≠ 0 := s1362PreΨ_ne_zero l
  have hsplit : (S1362PreΨ l).Splits := s1362PreΨ_splits l
  unfold S1362PreΨSeparable
  rw [s1362RootCount_iff_roots_nodup l]
  exact Polynomial.nodup_roots_iff_of_splits hp hsplit

/-- Over the algebraically closed characteristic-zero closure, separability
and squarefreeness agree. -/
theorem s1362PreΨSeparable_iff_squarefree (l : PrimeGeFive) :
    S1362PreΨSeparable l ↔ S1362PreΨSquarefree l := by
  unfold S1362PreΨSeparable S1362PreΨSquarefree
  exact PerfectField.separable_iff_squarefree

/-- Full root count is equivalent to squarefreeness. -/
theorem s1362RootCount_iff_squarefree (l : PrimeGeFive) :
    S1362RootCount l ↔ S1362PreΨSquarefree l :=
  (s1362RootCount_iff_separable l).trans (s1362PreΨSeparable_iff_squarefree l)

/-- Separability is equivalent to the root multiset having no repeated roots. -/
theorem s1362PreΨSeparable_iff_roots_nodup (l : PrimeGeFive) :
    S1362PreΨSeparable l ↔ (S1362PreΨ l).roots.Nodup :=
  (s1362RootCount_iff_separable l).symm.trans (s1362RootCount_iff_roots_nodup l)

/-! ## 4. The l-torsion-theoretic form under the S1329 criterion -/

/-- Under the S1329 group-law criterion, the root count is exactly the bare
l-torsion cardinality `Nat.card E[l] = l ^ 2`. -/
theorem s1362RootCount_iff_natCard_of_criterion (l : PrimeGeFive)
    (hcrit : S1329ConcreteCriterion l) :
    S1362RootCount l ↔ Nat.card (S1298TorsionCarrier l) = l.value ^ 2 := by
  rw [s1362RootCount_iff_s1329ConcreteSeparable l]
  exact (s1329ConcreteNatCard_eq_sq_iff l hcrit).symm

/-- Under the criterion, the root count is exactly the D5 cardinality card
(finiteness plus `Nat.card = l ^ 2`). -/
theorem s1362RootCount_iff_cardinalityCard_of_criterion (l : PrimeGeFive)
    (hcrit : S1329ConcreteCriterion l) :
    S1362RootCount l ↔ S1298TorsionCardinalityCard l := by
  rw [s1362RootCount_iff_natCard_of_criterion l hcrit]
  constructor
  · intro h
    exact ⟨s1329Finite_of_natCard h, h⟩
  · rintro ⟨-, h⟩
    exact h

/-- Under the criterion, the root count is exactly the existence of the
rank-two l-torsion basis of the S1298 first field. -/
theorem s1362RootCount_iff_basisNonempty_of_criterion (l : PrimeGeFive)
    (hcrit : S1329ConcreteCriterion l) :
    S1362RootCount l ↔ Nonempty (S1329TorsionBasis l) := by
  rw [s1362RootCount_iff_s1329ConcreteSeparable l]
  exact (s1329ConcreteBasis_iff_separable l hcrit).symm

/-- The separability form of the same reduction: under the criterion,
separability is equivalent to the l-torsion cardinality `l ^ 2`. -/
theorem s1362Separable_iff_natCard_of_criterion (l : PrimeGeFive)
    (hcrit : S1329ConcreteCriterion l) :
    S1362PreΨSeparable l ↔ Nat.card (S1298TorsionCarrier l) = l.value ^ 2 :=
  (s1362RootCount_iff_separable l).symm.trans
    (s1362RootCount_iff_natCard_of_criterion l hcrit)

/-- Under the criterion, separability is equivalent to the D5 cardinality
card. -/
theorem s1362Separable_iff_cardinalityCard_of_criterion (l : PrimeGeFive)
    (hcrit : S1329ConcreteCriterion l) :
    S1362PreΨSeparable l ↔ S1298TorsionCardinalityCard l :=
  (s1362RootCount_iff_separable l).symm.trans
    (s1362RootCount_iff_cardinalityCard_of_criterion l hcrit)

/-- Under the criterion, separability is equivalent to the rank-two basis
field being inhabited. -/
theorem s1362Separable_iff_basisNonempty_of_criterion (l : PrimeGeFive)
    (hcrit : S1329ConcreteCriterion l) :
    S1362PreΨSeparable l ↔ Nonempty (S1329TorsionBasis l) :=
  (s1362RootCount_iff_separable l).symm.trans
    (s1362RootCount_iff_basisNonempty_of_criterion l hcrit)

/-! ## 5. The exact gap -/

/-- The exact polynomial gap: separability of the concrete `prePsi_l`. -/
def S1362PreΨSeparabilityGap (l : PrimeGeFive) : Prop :=
  S1362PreΨSeparable l

/-- The exact l-torsion-theoretic form of the same gap. -/
def S1362LTorsionCardinalityGap (l : PrimeGeFive) : Prop :=
  S1298TorsionCardinalityCard l

/-- Under the S1329 criterion, the polynomial separability gap is exactly the
l-torsion cardinality gap.  This is the precise reduction of the second exact
field to the frozen cardinality `#E[l] = l ^ 2`; neither side is asserted. -/
theorem s1362Gap_equiv_of_criterion (l : PrimeGeFive)
    (hcrit : S1329ConcreteCriterion l) :
    S1362PreΨSeparabilityGap l ↔ S1362LTorsionCardinalityGap l := by
  unfold S1362PreΨSeparabilityGap S1362LTorsionCardinalityGap
  exact s1362Separable_iff_cardinalityCard_of_criterion l hcrit

/-- The gap is exactly the missing separability statement, restated for
consumers. -/
theorem s1362Gap_iff_separable (l : PrimeGeFive) :
    S1362PreΨSeparabilityGap l ↔ S1362PreΨSeparable l :=
  Iff.rfl

/-- A proof of the gap would give the exact root count. -/
theorem s1362RootCount_of_gap (l : PrimeGeFive)
    (h : S1362PreΨSeparabilityGap l) : S1362RootCount l :=
  (s1362RootCount_iff_separable l).mpr h

/-- A proof of the gap gives the S1329 concrete separability statement. -/
theorem s1362ConcreteSeparable_of_gap (l : PrimeGeFive)
    (h : S1362PreΨSeparabilityGap l) : S1329ConcreteSeparable l :=
  (s1362RootCount_iff_s1329ConcreteSeparable l).mp (s1362RootCount_of_gap l h)

/-- A proof of the gap, together with the S1329 group-law criterion, gives the
actual rank-two l-torsion basis of the D5 first field. -/
theorem s1362Basis_of_gap_and_criterion (l : PrimeGeFive)
    (h : S1362PreΨSeparabilityGap l) (hcrit : S1329ConcreteCriterion l) :
    Nonempty (S1329TorsionBasis l) :=
  (s1329ConcreteBasis_iff_separable l hcrit).mpr (s1362ConcreteSeparable_of_gap l h)

/-! ## 6. Axiom footprint -/

#print axioms s1362PreΨ_ne_zero
#print axioms s1362PreΨ_natDegree
#print axioms s1362PreΨ_splits
#print axioms s1362RootFinset_card_le
#print axioms s1362RootCount_iff_roots_nodup
#print axioms s1362RootCount_iff_separable
#print axioms s1362PreΨSeparable_iff_squarefree
#print axioms s1362RootCount_iff_squarefree
#print axioms s1362RootCount_iff_natCard_of_criterion
#print axioms s1362RootCount_iff_cardinalityCard_of_criterion
#print axioms s1362RootCount_iff_basisNonempty_of_criterion
#print axioms s1362Separable_iff_natCard_of_criterion
#print axioms s1362Separable_iff_cardinalityCard_of_criterion
#print axioms s1362Separable_iff_basisNonempty_of_criterion
#print axioms s1362Gap_equiv_of_criterion
#print axioms s1362RootCount_of_gap
#print axioms s1362ConcreteSeparable_of_gap
#print axioms s1362Basis_of_gap_and_criterion

end LeanFormal.IUT.XiFPaper.S1362PrePsiSeparabilityActual
