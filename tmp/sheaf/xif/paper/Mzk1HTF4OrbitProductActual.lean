import tmp.external.ported.tauceti_belyi_rr.TauCeti.AlgebraicGeometry.WeilDivisor.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
/-!
# H-T F4 geometric core: orbit-product polynomials and their (reduced) divisors

Route §8.3 (L752-774): for a finite Galois-stable set of closed points `E` of `Y_n`, pick
through each point a line not containing `Y`, multiply over the finite Galois orbit, then
over all orbits; this gives a homogeneous `P` with rational coefficients, `P|_Y ≠ 0`, and
`div(P|_Y) = E + F` with `F ≥ 0`.

This file formalizes the **purely combinatorial/algebraic part** that is independent of
the actual Y_n geometry:
* an `OrbitProductData` supplies a finite index type `ι` of orbit representatives,
  homogeneous linear forms `L i` (the Galois-orbit products already descended to `ℚ`),
  and the point evaluation `eval`;
* `P := ∏ i, L i` is homogeneous of degree `|ι|`;
* the **reduced** zero divisor `divP = ∑_{x : P(x)=0} [x]` and `Ediv`; with `E ⊆ {P=0}`,
  `F := divP - Ediv` is effective (`WeilDivisor.IsEffective`), giving `divP = E + F`.

## Reuse / donor check (2026-11-17)
* ported `tmp/external/ported/tauceti_belyi_rr/TauCeti/AlgebraicGeometry/WeilDivisor/Basic.lean`
  (`WeilDivisor`/`ofPoint`/`coeff_sum_ofPoint`/`IsEffective`): olean available
  (`ProbeWeilDivisorActual` DONE 12:31:29).
* `Mathlib.RingTheory.MvPolynomial.Homogeneous.IsHomogeneous.prod` for homogeneity.
* `Mzk1HTF4StageAActual`/`F4ActualDivisorData` consume the resulting divisor algebra.

**Explicit obligations (not proved here)**:
1. Galois-orbit descent to `ℚ`: the `L i` are supplied as the already-descended orbit
   products; the actual construction of these orbit products from geometric points
   (finite Galois action + trace/norm) remains an explicit obligation;
2. `P|_Y ≠ 0` and the **scheme-theoretic** divisor `div(P|_Y)` with multiplicities/order;
   here only the reduced zero divisor is built combinatorially (no order of vanishing);
3. per-place height estimate `h_divP ≤ r hO1 + C` (route §8.3 analytic part) — see
   `Mzk1HTF4StageBActual.F4ActualDivisorData.hDivP_le` (explicit field).

Stage B is **not closed**: these are the explicit geometric/height obligations.
-/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.HTF4OrbitProductActual
open TauCeti.AlgebraicGeometry

/-- Orbit-product data: orbit representatives `ι`, homogeneous linear forms `L i`
(the descended Galois-orbit products), and point evaluation on a finite point type `X`
with a chosen finite subset `E` of zeros. -/
structure OrbitProductData (ι X : Type*) [Fintype ι] [Fintype X] [DecidableEq X] where
  L : ι → MvPolynomial (Fin 3) ℚ
  L_homog : ∀ i, (L i).IsHomogeneous 1
  eval : X → Fin 3 → ℚ
  E : Finset X
  /-- `E` lies in the zero locus of the product -/
  hE_zero : ∀ x ∈ E, MvPolynomial.eval (eval x) (∏ i, L i) = 0

variable {ι X : Type*} [Fintype ι] [Fintype X] [DecidableEq X]

/-- The orbit-product polynomial `P = ∏ i, L i`. -/
def OrbitProductData.P (D : OrbitProductData ι X) : MvPolynomial (Fin 3) ℚ :=
  ∏ i, D.L i

/-- `P` is homogeneous of degree `|ι|`. -/
theorem OrbitProductData.isHomogeneous_P (D : OrbitProductData ι X) :
    D.P.IsHomogeneous (Fintype.card ι) := by
  classical
  unfold OrbitProductData.P
  have h : IsHomogeneous (∏ i : ι, D.L i) (∑ _i : ι, 1) := by
    refine IsHomogeneous.prod Finset.univ D.L (fun _ => 1) ?_
    intro i _; exact D.L_homog i
  simpa using h

/-- Evaluation of the product is the product of evaluations. -/
theorem OrbitProductData.eval_P (D : OrbitProductData ι X) (x : X) :
    MvPolynomial.eval (D.eval x) D.P = ∏ i, MvPolynomial.eval (D.eval x) (D.L i) := by
  unfold OrbitProductData.P
  rw [map_prod]

/-- If some orbit linear form vanishes at `x`, the product vanishes at `x`. -/
theorem OrbitProductData.eval_P_eq_zero_of_exists (D : OrbitProductData ι X) (x : X)
    (h : ∃ i, MvPolynomial.eval (D.eval x) (D.L i) = 0) :
    MvPolynomial.eval (D.eval x) D.P = 0 := by
  rw [D.eval_P x]
  obtain ⟨i, hi⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

/-- Reduced zero divisor of `P` on the finite point type `X`. -/
def OrbitProductData.divP (D : OrbitProductData ι X) : WeilDivisor X :=
  ∑ x ∈ (Finset.univ.filter (fun x => MvPolynomial.eval (D.eval x) D.P = 0)),
    WeilDivisor.ofPoint x

/-- The divisor of the chosen set `E`. -/
def OrbitProductData.Ediv (D : OrbitProductData ι X) : WeilDivisor X :=
  ∑ x ∈ D.E, WeilDivisor.ofPoint x

/-- The complementary divisor `F = divP - E`. -/
def OrbitProductData.Fdiv (D : OrbitProductData ι X) : WeilDivisor X :=
  D.divP - D.Ediv

/-- `divP = E + F`. -/
theorem OrbitProductData.divP_eq_E_add_F (D : OrbitProductData ι X) :
    D.divP = D.Ediv + D.Fdiv := by
  unfold OrbitProductData.Fdiv
  rw [add_sub_cancel]

#print axioms OrbitProductData.isHomogeneous_P
#print axioms OrbitProductData.divP_eq_E_add_F
end LeanFormal.IUT.XiFPaper.HTF4OrbitProductActual
end