/- Branch set of `psiFixed` as a `Finset ℂ`, with the transport to the analytic
critical-value set. Design doc: `Mzk1G1PsiBranchSpec.md`.

The integer polynomial `u = protectedToZeroPolynomial T = ∏(X - C t)` is the
lambda-chart coordinate of `psiFixed` (via `psiChart0Coord`), so the finite branch
values of `psiFixed` are `u` evaluated at the roots of `u'`, i.e. exactly
`criticalValuesOverC u`. The inversion `Branch(psiFixed) = inv '' Branch(psi)` is
realised on the finite part by `branchFixedFinite`; the image of `0` is `∞`, which
is automatically allowed in the target for a nonconstant polynomial.
-/
import tmp.sheaf.xif.paper.Mzk1G1NoncriticalPsiActual
import tmp.sheaf.xif.paper.Mzk1G1ProtectedToZeroMapActual
import tmp.sheaf.xif.paper.RestatedLemma24InterfaceActual
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiBranchSetActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProtectedToZeroMapActual

variable (T : Finset ℚ)

/-- `u = ∏(X - C t)` has degree `T.card`. -/
theorem natDegree_protectedToZeroPolynomial :
    (protectedToZeroPolynomial T).natDegree = T.card := by
  rw [protectedToZeroPolynomial]
  simpa using (Polynomial.natDegree_finsetProd_X_sub_C_eq_card (s := T) (f := fun t : ℚ => t))

/-- The complexification of `u'`: its roots are the finite ramification points. -/
noncomputable def branchPoly : ℂ[X] :=
  (Polynomial.derivative (protectedToZeroPolynomial T)).map (algebraMap ℚ ℂ)

theorem branchPoly_ne_zero (hT : 2 ≤ T.card) : branchPoly T ≠ 0 := by
  unfold branchPoly
  rw [Polynomial.map_ne_zero_iff (show Function.Injective (algebraMap ℚ ℂ) from
    fun a b h => by exact_mod_cast h)]
  exact Polynomial.derivative_ne_zero.mpr (by
    rw [natDegree_protectedToZeroPolynomial]
    omega)

/-- The finite branch values of `psiFixed`, as a `Finset ℂ`: `u` at the roots of `u'`. -/
noncomputable def branchValuesFinite : Finset ℂ :=
  (((branchPoly T).roots.attach).map
    (fun r => Polynomial.aeval r.1 (protectedToZeroPolynomial T))).toFinset

/-- The finite part of the branch set of `psiFixed = inv ∘ psi`: inversion applied to
the nonzero finite branch values of `psi` (the value `0` maps to `∞`, harmless). -/
noncomputable def branchFixedFinite : Finset ℂ :=
  ((branchValuesFinite T).filter (fun z => z ≠ 0)).image (fun z => z⁻¹)

/-- `aeval` at a complex number is the evaluation of the complexified polynomial. -/
theorem aeval_derivative_eq_branchPoly_eval (z : ℂ) :
    Polynomial.aeval z (Polynomial.derivative (protectedToZeroPolynomial T)) =
      (branchPoly T).eval z := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  rfl

/-- Membership in the finite branch value set. -/
theorem mem_branchValuesFinite_iff (c : ℂ) :
    c ∈ branchValuesFinite T ↔
      ∃ z ∈ (branchPoly T).roots, Polynomial.aeval z (protectedToZeroPolynomial T) = c := by
  rw [branchValuesFinite]
  constructor
  · intro h
    rw [Multiset.mem_toFinset, Multiset.mem_map] at h
    obtain ⟨r, -, hval⟩ := h
    exact ⟨r.1, r.2, hval⟩
  · rintro ⟨z, hz, hval⟩
    rw [Multiset.mem_toFinset, Multiset.mem_map]
    exact ⟨⟨z, hz⟩, by simp, hval⟩

/-- (Gap 1) The finite branch values are the analytic critical values of `u`. -/
theorem coe_branchValuesFinite (hT : 2 ≤ T.card) :
    (↑(branchValuesFinite T) : Set ℂ) =
      criticalValuesOverC (protectedToZeroPolynomial T) := by
  ext c
  rw [Finset.mem_coe, mem_branchValuesFinite_iff]
  constructor
  · rintro ⟨z, hz, hval⟩
    refine ⟨z, ?_, ?_, hval⟩
    · rw [natDegree_protectedToZeroPolynomial]
      omega
    · rw [aeval_derivative_eq_branchPoly_eval]
      exact (Polynomial.mem_roots (branchPoly_ne_zero T hT)).mp hz
  · rintro ⟨z, -, hder, hval⟩
    refine ⟨z, ?_, hval⟩
    rw [Polynomial.mem_roots (branchPoly_ne_zero T hT)]
    show (branchPoly T).eval z = 0
    rw [← aeval_derivative_eq_branchPoly_eval]
    exact hder

/-- (Gap 2) The finite part of `Branch(psiFixed)` is the inversion image of the
nonzero finite branch values of `psi`. -/
theorem coe_branchFixedFinite (hT : 2 ≤ T.card) :
    (↑(branchFixedFinite T) : Set ℂ) =
      (fun z : ℂ => z⁻¹) '' (criticalValuesOverC (protectedToZeroPolynomial T) \ {0}) := by
  rw [branchFixedFinite, Finset.coe_image]
  have hset : (↑((branchValuesFinite T).filter (fun z => z ≠ 0)) : Set ℂ) =
      (↑(branchValuesFinite T) : Set ℂ) \ {0} := by
    ext x
    simp
  rw [hset, coe_branchValuesFinite T hT]

#print axioms natDegree_protectedToZeroPolynomial
#print axioms branchPoly_ne_zero
#print axioms aeval_derivative_eq_branchPoly_eval
#print axioms mem_branchValuesFinite_iff
#print axioms coe_branchValuesFinite
#print axioms coe_branchFixedFinite
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiBranchSetActual-- t
