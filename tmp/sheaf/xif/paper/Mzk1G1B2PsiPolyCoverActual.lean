/- B2 general-T: `DTZeroElem`-version of the B1 `hcover` input for the BranchPoly adapter.

  Emmy's adapter `Mzk1G1B1BranchPolyAdapterActual.b1FiniteProducer_of_branchPoly` needs
  `hcover : ∀T, ∃ Tr, Tr.Nonempty ∧ (T ∩ DTPoly T) ⊆ DTFixed n Tr`. This file supplies the
  DTZeroElem version in the RATIONAL-chart-0 case: if every point of `S` has a RATIONAL
  chart-0 x-coordinate (with certificate `chartX - t ∈ p`), then for any chart-0 function `u`
  the intersection `chart0 '' S ∩ DTZeroElem u` is covered by some `DTFixed n Tr`.
  This is the exact-class cover; the general Galois orbit case is the A3/RR obligation
  (registered in coord/A3-EVALDATA-MAP.md, NOT claimed here).

  Header RECON: reuses `Mzk1G1B1DTSubsetActual.chart0_point_mem_DTFixed_of_rational`
  (DONE 04:08:58) and `Mzk1G1B2PsiPolyDTZeroActual.DTZeroElem` (DONE); no duplicate math.
  No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1B2PsiPolyDTZeroActual
import tmp.sheaf.xif.paper.Mzk1G1B1DTSubsetActual
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1B2PsiPolyCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B2FixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B1DTSubsetActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B2PsiPolyDTZeroActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual

variable (n : Nat)

/-- **`hcover` 的 DTZeroElem 版（有理 chart-0 情形）**：若 `S` 的每个点有有理 chart-0 坐标
    （证书 `chartX − f p ∈ p`），则 `chart0 '' S ∩ DTZeroElem u` 被某个 `DTFixed n Tr` 覆盖。 -/
theorem exists_DTFixed_cover_DTZeroElem (S : Finset (PrimeSpectrum (R n))) (u : R n)
    (f : PrimeSpectrum (R n) → ℚ)
    (hf : ∀ p ∈ S, chartX n - algebraMap ℚ (R n) (f p) ∈ p.asIdeal)
    (hS : S.Nonempty) :
    ∃ Tr : Finset ℚ, Tr.Nonempty ∧
      ((fermatChart0ToCurve n) '' (S : Set (PrimeSpectrum (R n))) ∩
          DTZeroElem n u) ⊆ DTFixed n Tr := by
  classical
  refine ⟨S.image f, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := hS
    exact ⟨f p, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
  · rintro y ⟨⟨p, hp, rfl⟩, -⟩
    exact chart0_point_mem_DTFixed_of_rational n S f hf p hp

#print axioms exists_DTFixed_cover_DTZeroElem

end LeanFormal.IUT.XiFPaper.Mzk1G1B2PsiPolyCoverActual