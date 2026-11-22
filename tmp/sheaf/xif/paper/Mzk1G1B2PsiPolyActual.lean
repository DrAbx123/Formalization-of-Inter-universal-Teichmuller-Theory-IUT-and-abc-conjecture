/- B2 general-T `psiPoly`: local-coordinate minpoly construction (route §4.1 explicit s0).

  For a finite set `S` of closed points of the chart-0 curve `Spec (R n)` attach to each point
  `p` a local coordinate `coordAt p` (the chart coordinate `x` if `y ∉ p`, else `y`), take its
  minimal polynomial over ℚ in the residue field `κ(p) = R n ⧸ p`, and evaluate it at `coordAt p`.
  `psiPolyCoord S = prod_{p in S} (minpoly_{κ p} (coord p))(coord p)` vanishes at every `p ∈ S`
  (and, being built from minimal polynomials, on the whole Galois orbit of `p`).
  This is the explicit `u0` of the route-equivalent construction.

  THIS FILE (minimal green slice, per Lead): `DTZero`, `mem_DTZero_iff`, `b1BranchDTZero`
  (B1 adapter interface) + value-level vanishing lemmas. The morphism `psiPoly` and
  `psiPoly_preimage_p1Zero_eq_DTZero`, `psiPoly_unramified_on_zero` are the next slice:
  they need the two-chart gluing of `chartMorphism0 u0` with its infinity-chart dual, and the
  scheme-level zero-divisor/simplicity analysis (registered obligations; see
  coord/A3-EVALDATA-MAP.md and emmy's Mzk1G1B1BranchPolyAdapterActual 13:56:55).
  Header RECON: rational case = `Mzk1G1PsiChartMapsActual.psiChart0Coord`; `minpoly` API from
  Mathlib; `IsOpenImmersion.isOpenEmbedding` for `mem_DTZero_iff`; no duplicate. No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1PsiChartMapsActual
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveActual
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1B2PsiPolyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual

variable (n : Nat)

/-- `p` 处的局部坐标函数：`y = 0` 时用 `y`，否则用 `x`。 -/
noncomputable def coordAt (p : PrimeSpectrum (R n)) : R n := by
  classical
  exact if chartY n ∈ p.asIdeal then chartY n else chartX n

/-- `p` 处局部坐标的极小多项式（在 residue field 中取）。 -/
noncomputable def minpolyAt (p : PrimeSpectrum (R n)) : Polynomial ℚ :=
  minpoly ℚ (algebraMap (R n) (R n ⧸ p.asIdeal) (coordAt n p))

/-- general-T 的显式 `u0`。 -/
noncomputable def psiPolyCoord (S : Finset (PrimeSpectrum (R n))) : R n :=
  ∏ p ∈ S, Polynomial.aeval (coordAt n p) (minpolyAt n p)

/-- 单点消失引理：`(minpoly_κ(coord p))(coord p) ∈ p`。 -/
theorem aeval_minpoly_mem (p : PrimeSpectrum (R n)) :
    Polynomial.aeval (coordAt n p) (minpolyAt n p) ∈ p.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  show (Ideal.Quotient.mk p.asIdeal) (Polynomial.aeval (coordAt n p) (minpolyAt n p)) = 0
  have h : (Ideal.Quotient.mk p.asIdeal) (Polynomial.aeval (coordAt n p) (minpolyAt n p)) =
      Polynomial.aeval (algebraMap (R n) (R n ⧸ p.asIdeal) (coordAt n p)) (minpolyAt n p) := by
    have hnat := Polynomial.aeval_algHom_apply
      (Ideal.Quotient.mkₐ ℚ p.asIdeal) (coordAt n p) (minpolyAt n p)
    simpa using hnat.symm
  rw [h, minpolyAt]
  have := minpoly.aeval ℚ (algebraMap (R n) (R n ⧸ p.asIdeal) (coordAt n p))
  simpa [Polynomial.aeval_def] using this

/-- **`psiPolyCoord` 在所选闭点集上消失**。 -/
theorem psiPolyCoord_mem (S : Finset (PrimeSpectrum (R n)))
    {p : PrimeSpectrum (R n)} (hp : p ∈ S) : psiPolyCoord n S ∈ p.asIdeal := by
  unfold psiPolyCoord
  exact Ideal.prod_mem p.asIdeal hp (aeval_minpoly_mem n p)

/-- **`DTZero P`（chart-0 定义）**：`P(x) = 0` 的零点集。 -/
noncomputable def DTZero (P : Polynomial ℚ) : Set (fermatCurveScheme n) :=
  (fermatChart0ToCurve n) ''
    {p : PrimeSpectrum (R n) | Polynomial.aeval (chartX n) P ∈ p.asIdeal}

/-- `DTZero` 的 chart-0 成员判定。 -/
theorem mem_DTZero_iff (P : Polynomial ℚ) (p : PrimeSpectrum (R n)) :
    (fermatChart0ToCurve n).base p ∈ DTZero n P ↔
      Polynomial.aeval (chartX n) P ∈ p.asIdeal := by
  constructor
  · rintro ⟨q, hq, heq⟩
    have hinj : Function.Injective (fermatChart0ToCurve n) :=
      (fermatChart0ToCurve n).isOpenEmbedding.injective
    have hqp : q = p := hinj heq
    rw [← hqp]
    exact hq
  · intro h
    exact ⟨p, h, rfl⟩

/-- **B1 接口适配**：`T ⊆ DTZero P`（替代 `T ⊆ DTFixed n Tr`）。 -/
def b1BranchDTZero (T : Finset (fermatCurveScheme n)) (P : Polynomial ℚ) : Prop :=
  (↑T : Set (fermatCurveScheme n)) ⊆ DTZero n P

#print axioms aeval_minpoly_mem
#print axioms psiPolyCoord_mem
#print axioms mem_DTZero_iff

end LeanFormal.IUT.XiFPaper.Mzk1G1B2PsiPolyActual
