/- R3 (造源 first half): the ACTUAL multiplication kernel E[m] = ker([m]) as the primary object.

  User ruling: the source must be built from the actual multiplication kernel E[m] = ker([m])
  (m = 3, 5, l), with division polynomials only as COORDINATE TOOLS; three things must be
  covered by the coordinate description: (i) BOTH y over each x, (ii) the point at infinity O,
  (iii) enumeration completeness; and the coordinate-generated field must equal the actual
  torsion field. Doubling identities do NOT replace these.

  THIS FILE: the kernel object and its elementary group structure (`0`, add, neg), plus the
  actual iff for m = 2 and m = 3 via the DONE criteria (Mathlib n=2 donor and
  `S1373ZeroCriterionActual` for n=3). For m = 5 and m = l the actual nsmul criterion is
  NOT yet available (henry's M4/G2); those iffs remain OPEN and are NOT claimed here.
  No sorry/axiom. -/
import tmp.sheaf.xif.paper.S1373ZeroCriterionActual
import tmp.sheaf.xif.paper.Mzk1G1R3TorsionCriterionActual
import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1R3TorsionKernelActual
open LeanFormal.IUT

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

/-- **实际乘法核** `E[m] = ker([m])`（不用除法多项式定义）。 -/
def mulKernel (m : ℤ) : Set W.toAffine.Point := {P | m • P = 0}

/-- 无穷远点（零元）属于核。 -/
theorem zero_mem_mulKernel (m : ℤ) : (0 : W.toAffine.Point) ∈ mulKernel W m := by
  simp [mulKernel]

/-- 核对加法封闭。 -/
theorem add_mem_mulKernel {m : ℤ} {P Q : W.toAffine.Point}
    (hP : P ∈ mulKernel W m) (hQ : Q ∈ mulKernel W m) : P + Q ∈ mulKernel W m := by
  simp only [mulKernel, Set.mem_setOf_eq] at hP hQ ⊢
  rw [smul_add, hP, hQ, add_zero]

/-- 核对取负封闭。 -/
theorem neg_mem_mulKernel {m : ℤ} {P : W.toAffine.Point} (hP : P ∈ mulKernel W m) :
    -P ∈ mulKernel W m := by
  simp only [mulKernel, Set.mem_setOf_eq] at hP ⊢
  rw [smul_neg, hP, neg_zero]

/-- **m = 2 的实际 iff**（Mathlib donor）。 -/
theorem mulKernel_two_iff (P : W.toAffine.Point) :
    P ∈ mulKernel W 2 ↔ W.evalDivisionPolynomialAtPoint 2 P = 0 := by
  simp only [mulKernel, Set.mem_setOf_eq]
  rw [show (2 : ℤ) • P = (2 : ℕ) • P from natCast_zsmul P 2]
  exact W.two_nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_two_eq_zero P

/-- **m = 3 的实际 iff**（S1373 donor）。 -/
theorem mulKernel_three_iff (P : W.toAffine.Point) :
    P ∈ mulKernel W 3 ↔ W.evalDivisionPolynomialAtPoint 3 P = 0 := by
  simp only [mulKernel, Set.mem_setOf_eq]
  exact W.three_nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_three_eq_zero P

#print axioms zero_mem_mulKernel
#print axioms add_mem_mulKernel
#print axioms neg_mem_mulKernel
#print axioms mulKernel_two_iff
#print axioms mulKernel_three_iff

end LeanFormal.IUT.XiFPaper.Mzk1G1R3TorsionKernelActual
