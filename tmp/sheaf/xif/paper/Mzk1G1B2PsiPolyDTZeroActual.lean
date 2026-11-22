/- B2 general-T: generalised zero sets `DTZeroElem u` (chart-0 restriction of `u`), chart-infinity
  dual, and the B1 adapter with an arbitrary chart-0 function instead of `P(chartX)`.

  Design (per Lead): `DTZero P := {P(chartX) = 0}` only covers zeros from x-coordinates; for
  points with `y = 0` or at infinity the explicit `u0` uses `y` or the `r/s` coordinate, which
  cannot be written as `P(chartX)` (and `P(chartX)` has non-simple zeros there). Hence:
  * `DTZeroElem u`  = chart-0 points where the chart-0 restriction of `u : R n` vanishes;
  * `DTZeroElemInf u1` = chart-infinity points where the chart-infinity restriction of `u1 : R2 n`
    vanishes;
  * `DTZeroElemAll u0 u1` = their union (the actual zero set of the two-chart ψ);
  * `b1BranchDTZeroElem T u` := `T ⊆ DTZeroElem u` (B1 adapter shape, no `P(chartX)` restriction).
  `DTZero P` is kept as the x-only special case and identified with `DTZeroElem (aeval chartX P)`.

  Header RECON: `mem_DTZeroElem_iff` is the same `IsOpenEmbedding.injective` argument as
  `Mzk1G1B2PsiPolyActual.mem_DTZero_iff` (no duplicate math); chart-infinity uses
  `fermatChartInfToCurve` (open immersion instance exists, Mzk1G1FermatTwoChartGluingActual).
  No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1B2PsiPolyActual
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1B2PsiPolyDTZeroActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B2PsiPolyActual

variable (n : Nat)

/-- **一般零点集（chart-0）**：`u` 在 chart-0 上消失的点集。 -/
noncomputable def DTZeroElem (u : R n) : Set (fermatCurveScheme n) :=
  (fermatChart0ToCurve n) '' {p : PrimeSpectrum (R n) | u ∈ p.asIdeal}

/-- `DTZeroElem` 的成员判定。 -/
theorem mem_DTZeroElem_iff (u : R n) (p : PrimeSpectrum (R n)) :
    (fermatChart0ToCurve n).base p ∈ DTZeroElem n u ↔ u ∈ p.asIdeal := by
  constructor
  · rintro ⟨q, hq, heq⟩
    have hinj : Function.Injective (fermatChart0ToCurve n) :=
      (fermatChart0ToCurve n).isOpenEmbedding.injective
    have hqp : q = p := hinj heq
    rw [← hqp]
    exact hq
  · intro h
    exact ⟨p, h, rfl⟩

/-- `DTZero P` 是一般零点集的特例（`u = aeval (chartX) P`）。 -/
theorem DTZero_eq_DTZeroElem (P : Polynomial ℚ) :
    DTZero n P = DTZeroElem n (Polynomial.aeval (chartX n) P) := rfl

/-- **一般零点集（chart-∞）**：`u1` 在 chart-∞ 上消失的点集。 -/
noncomputable def DTZeroElemInf (u1 : R2 n) : Set (fermatCurveScheme n) :=
  (fermatChartInfToCurve n) '' {q : PrimeSpectrum (R2 n) | u1 ∈ q.asIdeal}

/-- `DTZeroElemInf` 的成员判定。 -/
theorem mem_DTZeroElemInf_iff (u1 : R2 n) (q : PrimeSpectrum (R2 n)) :
    (fermatChartInfToCurve n).base q ∈ DTZeroElemInf n u1 ↔ u1 ∈ q.asIdeal := by
  constructor
  · rintro ⟨q', hq', heq⟩
    have hinj : Function.Injective (fermatChartInfToCurve n) :=
      (fermatChartInfToCurve n).isOpenEmbedding.injective
    have hqq : q' = q := hinj heq
    rw [← hqq]
    exact hq'
  · intro h
    exact ⟨q, h, rfl⟩

/-- 两片零点集的并（两 chart ψ 的实际零点集）。 -/
noncomputable def DTZeroElemAll (u0 : R n) (u1 : R2 n) : Set (fermatCurveScheme n) :=
  DTZeroElem n u0 ∪ DTZeroElemInf n u1

/-- **B1 适配（一般函数版）**：`T ⊆ DTZeroElem u`。 -/
def b1BranchDTZeroElem (T : Finset (fermatCurveScheme n)) (u : R n) : Prop :=
  (↑T : Set (fermatCurveScheme n)) ⊆ DTZeroElem n u

/-- `psiPolyCoord` 给出的点都在其一般零点集中（Galois-invariant 显式 u0）。 -/
theorem b1BranchDTZeroElem_psiPolyCoord (S : Finset (PrimeSpectrum (R n))) :
    ∀ p ∈ S, (fermatChart0ToCurve n).base p ∈ DTZeroElem n (psiPolyCoord n S) :=
  fun p hp => (mem_DTZeroElem_iff n (psiPolyCoord n S) p).mpr (psiPolyCoord_mem n S hp)

#print axioms mem_DTZeroElem_iff
#print axioms mem_DTZeroElemInf_iff
#print axioms DTZero_eq_DTZeroElem
#print axioms b1BranchDTZeroElem_psiPolyCoord

end LeanFormal.IUT.XiFPaper.Mzk1G1B2PsiPolyDTZeroActual
