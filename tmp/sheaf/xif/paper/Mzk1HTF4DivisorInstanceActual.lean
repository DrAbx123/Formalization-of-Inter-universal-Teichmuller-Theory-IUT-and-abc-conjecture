import tmp.sheaf.xif.paper.Mzk1HTF4StageBActual
import tmp.sheaf.xif.paper.Mzk1HTF4OrbitEffectiveActual
import Mathlib.Tactic
/-!
# F4 geometric core: constructing `F4ActualDivisorData` from orbit-product divisors

Connects the combinatorial orbit-product construction
(`Mzk1HTF4OrbitProductActual` + `Mzk1HTF4OrbitEffectiveActual`) to the Stage B interface
`F4ActualDivisorData` (`Mzk1HTF4StageBActual`): the divisors `divP i`, `E i`, `F i` are
**constructed** as `(D i).divP`, `(D i).Ediv`, `(D i).Fdiv`, and `F i` is effective by
`Fdiv_effective`; the equality `divP i = E i + F i` is `divP_eq_E_add_F`.

The real-number height letters `hE`, `hDivP`, `hO1`, `C`, `hOmega` and the inequalities
`hE ≤ hDivP`, `hDivP ≤ r hO1 + C`, `hnorm` remain explicit inputs (route §8.3
per-place height estimate / A4 normalization); this stage **does not** prove them.

## Reuse / donor check (2026-11-17)
* `Mzk1HTF4OrbitProductActual` DONE 12:54:03 (`OrbitProductData`/`divP`/`Ediv`/`Fdiv`/
  `divP_eq_E_add_F`);
* `Mzk1HTF4OrbitEffectiveActual` DONE 13:15:24 (`Fdiv_effective`);
* `Mzk1HTF4StageBActual` DONE 12:36:10 (`F4ActualDivisorData`);
* ported `WeilDivisor/Basic` donor (probe 12:31:29).
-/
noncomputable section
open MvPolynomial
namespace LeanFormal.IUT.XiFPaper.HTF4DivisorInstanceActual
open LeanFormal.IUT.XiFPaper.HTF4OrbitProductActual
open LeanFormal.IUT.XiFPaper.HTF4OrbitEffectiveActual
open LeanFormal.IUT.XiFPaper.HTF4StageBActual
open LeanFormal.IUT.XiFPaper.F8PiActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open TauCeti.AlgebraicGeometry

variable {k : Type} [Field k] [NumberField k]

/-- Orbit-product family data: one `OrbitProductData` per index `i`, sharing the point
type `X`, plus the explicit real height letters and the route §8.3/A4 inequalities. -/
structure F4OrbitFamilyData (n : ℕ) (ι X : Type) [Fintype ι] [Fintype X] [DecidableEq X] where
  n_gt_three : 3 < (n : ℝ)
  φ : Chart0Ring n →+* k
  D : ℕ → OrbitProductData ι X
  hO1 : ℕ → ℝ
  hO1_eq : ∀ i, hO1 i = Height.logHeight ![(φ (x0 n)), (φ (x1 n)), 1]
  hOmega : ℕ → ℝ
  hE : ℕ → ℝ
  C : ℕ → ℝ
  C_nonneg : ∀ i, 0 ≤ C i
  hDivP : ℕ → ℝ
  hE_le_hDivP : ∀ i, hE i ≤ hDivP i
  hDivP_le : ∀ i, hDivP i ≤ (Fintype.card ι : ℝ) * hO1 i + C i
  hnorm : ∀ i, (Fintype.card ι : ℝ) * hO1 i =
    (Fintype.card ι : ℝ) / ((n : ℝ) - 3) * hOmega i

/-- The constructed Stage B data: divisors from the orbit-product construction, the
real height letters and inequalities from the explicit fields. -/
def F4OrbitFamilyData.toActual {n : ℕ} {ι X : Type} [Fintype ι] [Fintype X]
    [DecidableEq X] (F : F4OrbitFamilyData (k := k) n ι X) :
    F4ActualDivisorData (k := k) n where
  n_gt_three := F.n_gt_three
  φ := F.φ
  P := fun i => (F.D i).P
  r := fun _ => Fintype.card ι
  homog := fun i => (F.D i).isHomogeneous_P
  X := X
  divP := fun i => (F.D i).divP
  E := fun i => (F.D i).Ediv
  F := fun i => (F.D i).Fdiv
  F_effective := fun i => Fdiv_effective (F.D i)
  hdiv := fun i => (F.D i).divP_eq_E_add_F
  hO1 := F.hO1
  hO1_eq := F.hO1_eq
  hOmega := F.hOmega
  hE := F.hE
  C := F.C
  C_nonneg := F.C_nonneg
  hDivP := F.hDivP
  hE_le_hDivP := F.hE_le_hDivP
  hDivP_le := F.hDivP_le
  hnorm := F.hnorm

theorem F4OrbitFamilyData.hE_le_r {n : ℕ} {ι X : Type} [Fintype ι] [Fintype X]
    [DecidableEq X] (F : F4OrbitFamilyData (k := k) n ι X) (i : ℕ) :
    F.hE i ≤ (Fintype.card ι : ℝ) * F.hO1 i + F.C i :=
  F.toActual.hE_le_r i

theorem F4OrbitFamilyData.hE_le_kappa {n : ℕ} {ι X : Type} [Fintype ι] [Fintype X]
    [DecidableEq X] (F : F4OrbitFamilyData (k := k) n ι X) (i : ℕ) :
    F.hE i ≤ (Fintype.card ι : ℝ) / ((n : ℝ) - 3) * F.hOmega i + F.C i :=
  F.toActual.hE_le_kappa i

#print axioms F4OrbitFamilyData.toActual
#print axioms F4OrbitFamilyData.hE_le_r
#print axioms F4OrbitFamilyData.hE_le_kappa
end LeanFormal.IUT.XiFPaper.HTF4DivisorInstanceActual
end