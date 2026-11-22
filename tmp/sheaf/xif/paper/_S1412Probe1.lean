import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Data.Finsupp.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open Polynomial
open scoped BigOperators

namespace Probe1412

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
variable (W : WeierstrassCurve.Affine F) [W.IsElliptic]

#check IsAlgClosed.exists_root
#check WeierstrassCurve.Affine.equation_iff'
#check WeierstrassCurve.Affine.equation_iff_nonsingular
#check WeierstrassCurve.Affine.Y_eq_of_X_eq
#check WeierstrassCurve.Affine.Point.some_ne_zero
#check WeierstrassCurve.Affine.Point.neg_some
#check WeierstrassCurve.Affine.Point.some.injEq
#check Polynomial.mem_roots
#check Polynomial.rootMultiplicity_pos
#check Polynomial.count_roots
#check Multiset.toFinset_sum_count_eq
#check Polynomial.card_roots'
#check Multiset.toFinset_card_le
#check IsAlgClosed.card_roots_eq_natDegree
#check WeierstrassCurve.natDegree_preΨ
#check WeierstrassCurve.preΨ_ne_zero
#check WeierstrassCurve.evalDivisionPolynomialAtPoint_some
#check WeierstrassCurve.evalDivisionPolynomial_eq_eval_preΨ_of_odd
#check Finsupp.support_finsetSum
#check Finsupp.finsetSum_apply
#check Finsupp.sum_finsetSum_index
#check Finsupp.support_add
#check Finsupp.support_smul
#check Finsupp.support_single_subset
#check Finsupp.single_eq_same
#check Finsupp.single_eq_of_ne
#check Finsupp.mem_support_iff
#check Finsupp.smul_apply
#check Finset.single_le_sum
#check Finset.sum_eq_zero_iff_of_nonneg
#check Finset.eq_of_subset_of_card_le
#check Finset.card_erase_of_mem
#check Finset.card_union_le
#check Nat.mul_div_cancel'
#check Nat.Odd.sub_odd

end Probe1412
