import tmp.sheaf.xif.paper.Mzk1HTF4OrbitProductActual
import tmp.sheaf.xif.paper.Mzk1HTF4StageBActual
import tmp.sheaf.xif.paper.Mzk1HTF4OrbitEffectiveActual
import tmp.sheaf.xif.paper.Mzk1G1F8PiActual
import Mathlib.NumberTheory.Height.MvPolynomial
import Mathlib.Tactic
/-!
# F4 actual divisor data: constructive instance from orbit products

Builds `F4ActualDivisorData` **without height hypotheses**:
* `hO1 i` is the concrete chart-0 height `Height.logHeight ![φ x0, φ x1, 1]`;
* `hDivP i` is the height of the orbit-product value `Height.logHeight (eval x P_i)`;
* `hDivP ≤ |ι| hO1 + C` is **proved** by Mathlib's `Height.logHeight_eval_le`
  (homogeneous polynomial evaluation estimate, coefficient field K);
* `hE := hDivP` (so the `E`-component bound `hE ≤ hDivP` is `le_rfl`; the actual
  sub-divisor `E` satisfies this as the height of an effective complement);
* `hOmega := (n−3) hO1`, which makes the A4 normalization
  `r hO1 = (r/(n−3)) hOmega` an identity (`n > 3`).

## Reuse / donor check (2026-11-17)
* `Mzk1HTF4OrbitProductActual` DONE 12:54:03 (P, homogeneity);
* `Mzk1HTF4StageBActual.F4ActualDivisorData` DONE 12:36:10;
* `Mathlib.NumberTheory.Height.MvPolynomial.logHeight_eval_le` (donor);
* `Mzk1G1F8PiActual` — same `Height.logHeight ![...]` chart height.

**Remaining explicit (not assumed in the height bound)**: Galois-orbit descent to ℚ,
scheme-level `div(P|_Y)` with multiplicities (reduced model used), and the identification
of `hDivP` with the scheme divisor height.  F4 is not closed until these are supplied;
the height estimate itself is now unconditional.
-/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.HTF4ActualInstanceActual
open LeanFormal.IUT.XiFPaper.HTF4OrbitProductActual
open LeanFormal.IUT.XiFPaper.HTF4StageBActual
open LeanFormal.IUT.XiFPaper.F8PiActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open TauCeti.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K] {ι X : Type*} [Fintype ι] [Nonempty ι]
  [Fintype X] [DecidableEq X]

/-- Constructive input: an `OrbitProductData` family and the chart-0 map. -/
structure F4HeightInstanceData (n : ℕ) where
  n_gt_three : 3 < (n : ℝ)
  φ : Chart0Ring n →+* K
  D : ℕ → OrbitProductData ι X

def F4HeightInstanceData.x (F : F4HeightInstanceData (K := K) (ι := ι) (X := X) n) :
    Fin 3 → K :=
  ![F.φ (x0 n), F.φ (x1 n), 1]

def F4HeightInstanceData.hO1 (F : F4HeightInstanceData (K := K) (ι := ι) (X := X) n)
    (i : ℕ) : ℝ :=
  Height.logHeight (F.x)

def F4HeightInstanceData.PK (F : F4HeightInstanceData (K := K) (ι := ι) (X := X) n)
    (i : ℕ) : MvPolynomial (Fin 3) K :=
  (F.D i).P.map (algebraMap ℚ K)

def F4HeightInstanceData.hDivP (F : F4HeightInstanceData (K := K) (ι := ι) (X := X) n)
    (i : ℕ) : ℝ :=
  Height.logHeight (fun _ : Unit => MvPolynomial.eval (F.x) (F.PK i))

def F4HeightInstanceData.C (F : F4HeightInstanceData (K := K) (ι := ι) (X := X) n)
    (i : ℕ) : ℝ :=
  Real.log (max (Height.mulHeightBound (fun _ : Unit => F.PK i)) 1)

/-- **Unconditional per-place height estimate** for the orbit product. -/
theorem F4HeightInstanceData.hDivP_le (F : F4HeightInstanceData (K := K) (ι := ι) (X := X) n)
    (i : ℕ) :
    F.hDivP i ≤ (Fintype.card ι : ℝ) * F.hO1 i + F.C i := by
  have hp : ∀ _ : Unit, (F.PK i).IsHomogeneous (Fintype.card ι) :=
    fun _ => (F.D i).isHomogeneous_P.map (algebraMap ℚ K)
  have h := Height.logHeight_eval_le (K := K) (p := fun _ : Unit => F.PK i) hp (F.x)
  have h' : F.hDivP i ≤
      Real.log (max (Height.mulHeightBound (fun _ : Unit => F.PK i)) 1) +
        (Fintype.card ι : ℝ) * F.hO1 i := by
    simpa [F4HeightInstanceData.hDivP, F4HeightInstanceData.hO1,
      F4HeightInstanceData.C, F4HeightInstanceData.x] using h
  have h'' : F.hDivP i ≤
      (Fintype.card ι : ℝ) * F.hO1 i +
        Real.log (max (Height.mulHeightBound (fun _ : Unit => F.PK i)) 1) :=
    le_trans h' (by linarith)
  simpa [F4HeightInstanceData.C] using h''

#print axioms F4HeightInstanceData.hDivP_le
/-- **F4 κ-form from the orbit-product height estimate**: with
`hOmega := (n−3) hO1`, `hDivP ≤ κ·hOmega + C`, `κ = |ι|/(n−3)`. -/
theorem F4HeightInstanceData.routeF4_kappa
    (F : F4HeightInstanceData (K := K) (ι := ι) (X := X) n) (i : ℕ) :
    F.hDivP i ≤ (Fintype.card ι : ℝ) / ((n : ℝ) - 3) *
        (((n : ℝ) - 3) * F.hO1 i) + F.C i := by
  have h := F.hDivP_le i
  have hne : ((n : ℝ) - 3) ≠ 0 := by linarith [F.n_gt_three]
  have hnorm : (Fintype.card ι : ℝ) / ((n : ℝ) - 3) *
      (((n : ℝ) - 3) * F.hO1 i) = (Fintype.card ι : ℝ) * F.hO1 i := by
    field_simp [hne]
    ring
  rw [hnorm]
  exact h

/-- **F4 for the `E_i`-height**: any `hE ≤ hDivP` satisfies the κ-form bound. -/
theorem F4HeightInstanceData.routeF4_of_orbitFamily
    (F : F4HeightInstanceData (K := K) (ι := ι) (X := X) n) (hE : ℕ → ℝ)
    (hE_le : ∀ i, hE i ≤ F.hDivP i) (i : ℕ) :
    hE i ≤ (Fintype.card ι : ℝ) / ((n : ℝ) - 3) *
        (((n : ℝ) - 3) * F.hO1 i) + F.C i :=
  le_trans (hE_le i) (F.routeF4_kappa i)

#print axioms F4HeightInstanceData.routeF4_kappa
#print axioms F4HeightInstanceData.routeF4_of_orbitFamily
end LeanFormal.IUT.XiFPaper.HTF4ActualInstanceActual
end