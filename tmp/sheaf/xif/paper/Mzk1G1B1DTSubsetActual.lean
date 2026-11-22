/- B1: selecting the rational parameter set Tr for the subset `T ⊆ DTFixed n Tr` (route §4.1).

  `Mzk1G1B2Fixed4Actual.DTFixed n Tr` is the chart-0 image of the primes containing
  `chartX - t` for some `t ∈ Tr`. Hence points of the FIRST chart whose chart-0 coordinate is
  RATIONAL can always be covered by a suitable `Tr`; this file supplies the selection lemma
  (with the rationality certificate as explicit data) plus the precise remaining gap:
  * arbitrary geometric T (points of the q-piece chart, or with non-rational chart-0 coordinate)
    is NOT covered by any finite rational Tr in this model — that is exactly the route §4.1
    general-T Riemann-Roch step (registered as a separate G-C obligation,
    see Mzk1G1PsiGeneralRRActual header).
  No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1B2Fixed5Actual
import tmp.sheaf.xif.paper.Mzk1G1PsiChartMapsActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1B1DTSubsetActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B2FixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual

variable (n : Nat)

/-- **Tr 选取（chart-0、有理坐标点）**：若 `S` 是一族带证书的 chart-0 点（每个点 `q` 都含
    `chartX - f q`），则 `S` 的 chart-0 像包含在 `DTFixed n (S.image f)` 中。 -/
theorem chart0_point_mem_DTFixed_of_rational
    (S : Finset (PrimeSpectrum (R n))) (f : PrimeSpectrum (R n) → ℚ)
    (hf : ∀ q ∈ S, chartX n - algebraMap ℚ (R n) (f q) ∈ q.asIdeal) :
    ∀ p ∈ S, (fermatChart0ToCurve n).base p ∈ DTFixed n (S.image f) := by
  intro p hp
  refine Set.mem_image_of_mem _ ?_
  exact ⟨f p, Finset.mem_image.mpr ⟨p, hp, rfl⟩, hf p hp⟩

/-- 单点版本（消费者常只需单点）。 -/
theorem chart0_point_mem_DTFixed (p : PrimeSpectrum (R n)) (t : ℚ)
    (hp : chartX n - algebraMap ℚ (R n) t ∈ p.asIdeal) :
    (fermatChart0ToCurve n).base p ∈ DTFixed n {t} := by
  refine Set.mem_image_of_mem _ ?_
  exact ⟨t, Finset.mem_singleton_self t, hp⟩

#print axioms chart0_point_mem_DTFixed
#print axioms chart0_point_mem_DTFixed_of_rational
#print axioms chart0_point_mem_DTFixed

/-- **证书存在形式**（andrew 的 B1Chart0 `hdata` 消费形状）：给定 chart-0 有理坐标的有限点集
    与坐标函数 `f`，存在一个有限 `Tr : Finset ℚ` 使所有点落入 `DTFixed n Tr`。 -/
theorem exists_finset_rational_certificate (S : Finset (PrimeSpectrum (R n)))
    (f : PrimeSpectrum (R n) → ℚ)
    (hf : ∀ q ∈ S, chartX n - algebraMap ℚ (R n) (f q) ∈ q.asIdeal) :
    ∃ Tr : Finset ℚ, ∀ p ∈ S, (fermatChart0ToCurve n).base p ∈ DTFixed n Tr :=
  ⟨S.image f, fun p hp => chart0_point_mem_DTFixed_of_rational n S f hf p hp⟩

#print axioms exists_finset_rational_certificate

end LeanFormal.IUT.XiFPaper.Mzk1G1B1DTSubsetActual
