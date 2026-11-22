/-
B1: instantiation of the `branchPoly` adapter with grace's `DTZeroElem` and the
chart-0 rational-point cover lemma (interface instantiation, no new mathematics).

Consumers / donors reused (all DONE, three axioms each):
* emmy (13:56:55) `Mzk1G1BranchPolyAdapterActual.b1FiniteProducer_of_branchPoly`:
  `(DTPoly) (hbranchPoly) (hcover) : B1FiniteProducer n`.
* grace `Mzk1G1B2PsiPolyDTZeroActual.DTZeroElem (u : R n) : Set (fermatCurveScheme n)`
  with `mem_DTZeroElem_iff`; `b1BranchDTZeroElem T u := (↑T : Set _) ⊆ DTZeroElem n u`.
* grace (DONE 14:22:55) `Mzk1G1B2PsiPolyCoverActual.exists_DTFixed_cover_DTZeroElem`:
  rational chart-0 coordinates on `S` give a rational `Tr` covering
  `chart0 '' S ∩ DTZeroElem n u`.
* `Mzk1G1B2PsiPolyActual.psiPolyCoord` / `psiPolyCoord_mem`: the explicit general-T `u0`
  vanishes at every `p ∈ S`.

What is PROVIDED here (pure glue; no geometry, no new assumptions beyond the interface):
1. `b1FiniteProducer_of_DTZeroElem_chart0`: `DTPoly T := DTZeroElem n (u T)`; the T/S
   relation `T ⊆ chart0 '' S T`, the vanishing `u T ∈ p` (`p ∈ S T`), the rational chart-0
   certificates for `f T` and the (T-indexed) polynomial avoidance data are explicit
   hypotheses; `hcover` is discharged by the donor cover lemma.
2. `b1FiniteProducer_of_psiPolyCoord_chart0`: the intended instantiation
   `u T := psiPolyCoord n (S T)`, where the vanishing hypothesis of (1) is *free*
   (`psiPolyCoord_mem`), i.e. the remaining inputs are exactly T ⊆ chart0 '' S, the rational
   x-coordinate certificates, `S.Nonempty` and the avoidance polynomial.
Remaining gap (NOT claimed here): the avoidance data `h, h.eval 0 ∉ {0,1}` and the inclusion
`T ⊆ chart0 '' S T` are inputs (the A3/RR and M2 obligations). No sorry, no new axiom,
no change of target type. -/
import tmp.sheaf.xif.paper.Mzk1G1B1BranchPolyAdapterActual
import tmp.sheaf.xif.paper.Mzk1G1B2PsiPolyDTZeroActual
import tmp.sheaf.xif.paper.Mzk1G1B2PsiPolyCoverActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1B1BranchPolyDTZeroInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiB1Actual
open LeanFormal.IUT.XiFPaper.B1FinalHAvoidActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B2FixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1BranchPolyAdapterActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B2PsiPolyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B2PsiPolyDTZeroActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B2PsiPolyCoverActual
/-- **B1 via the general zero set of a chart-0 function.**

`DTPoly T := DTZeroElem n (u T)`.  The T-indexed data are:
* `S T`: the finite set of chart-0 points whose image contains `T` (`hTS`);
* `u T` vanishes at every `p ∈ S T` (`hmem`), so `T ⊆ DTZeroElem n (u T)`;
* `f T` gives rational chart-0 coordinates on `S T` (`hf`, `hS`);
* `h T` is the avoidance polynomial (`hh`, `hdeg`, `h0`).

The cover hypothesis of the adapter is discharged by
`exists_DTFixed_cover_DTZeroElem`. -/
theorem b1FiniteProducer_of_DTZeroElem_chart0 (n : Nat) (hn : 0 < n)
    (u : Finset (fermatCurveScheme n) → R n)
    (S : Finset (fermatCurveScheme n) → Finset (PrimeSpectrum (R n)))
    (f : Finset (fermatCurveScheme n) → PrimeSpectrum (R n) → ℚ)
    (hTS : ∀ T : Finset (fermatCurveScheme n),
      (↑T : Set (fermatCurveScheme n)) ⊆
        (fermatChart0ToCurve n) '' (S T : Set (PrimeSpectrum (R n))))
    (hmem : ∀ (T : Finset (fermatCurveScheme n)) (p : PrimeSpectrum (R n)),
      p ∈ S T → u T ∈ p.asIdeal)
    (hf : ∀ (T : Finset (fermatCurveScheme n)) (p : PrimeSpectrum (R n)),
      p ∈ S T → chartX n - algebraMap ℚ (R n) (f T p) ∈ p.asIdeal)
    (hS : ∀ T : Finset (fermatCurveScheme n), (S T).Nonempty)
    (h : Finset (fermatCurveScheme n) → Polynomial ℚ)
    (hh : ∀ T : Finset (fermatCurveScheme n), h T ≠ 0)
    (hdeg : ∀ T : Finset (fermatCurveScheme n), 0 < (h T).natDegree)
    (h0 : ∀ T : Finset (fermatCurveScheme n), (h T).eval 0 ∉ ({0, 1} : Set ℚ)) :
    B1FiniteProducer n := by
  refine b1FiniteProducer_of_branchPoly n hn (fun T => DTZeroElem n (u T)) ?_ ?_
  · intro T
    refine ⟨h T, hh T, hdeg T, ?_, h0 T⟩
    intro x hx
    obtain ⟨p, hp, hpx⟩ := hTS T hx
    rw [← hpx]
    exact ⟨p, hmem T p hp, rfl⟩
  · intro T
    obtain ⟨Tr, hTr, hsub⟩ :=
      exists_DTFixed_cover_DTZeroElem n (S T) (u T) (f T) (hf T) (hS T)
    exact ⟨Tr, hTr, fun x hx => hsub ⟨hTS T hx.1, hx.2⟩⟩

#print axioms b1FiniteProducer_of_DTZeroElem_chart0

/-- **B1 with the explicit `psiPolyCoord` general-T chart-0 function.**

Same as `b1FiniteProducer_of_DTZeroElem_chart0` with `u T := psiPolyCoord n (S T)`; the
vanishing hypothesis is then supplied by `psiPolyCoord_mem`, so the only remaining inputs are
the T/S relation, the rational x-coordinate certificates, nonemptiness and the avoidance
polynomial. -/
theorem b1FiniteProducer_of_psiPolyCoord_chart0 (n : Nat) (hn : 0 < n)
    (S : Finset (fermatCurveScheme n) → Finset (PrimeSpectrum (R n)))
    (f : Finset (fermatCurveScheme n) → PrimeSpectrum (R n) → ℚ)
    (hTS : ∀ T : Finset (fermatCurveScheme n),
      (↑T : Set (fermatCurveScheme n)) ⊆
        (fermatChart0ToCurve n) '' (S T : Set (PrimeSpectrum (R n))))
    (hf : ∀ (T : Finset (fermatCurveScheme n)) (p : PrimeSpectrum (R n)),
      p ∈ S T → chartX n - algebraMap ℚ (R n) (f T p) ∈ p.asIdeal)
    (hS : ∀ T : Finset (fermatCurveScheme n), (S T).Nonempty)
    (h : Finset (fermatCurveScheme n) → Polynomial ℚ)
    (hh : ∀ T : Finset (fermatCurveScheme n), h T ≠ 0)
    (hdeg : ∀ T : Finset (fermatCurveScheme n), 0 < (h T).natDegree)
    (h0 : ∀ T : Finset (fermatCurveScheme n), (h T).eval 0 ∉ ({0, 1} : Set ℚ)) :
    B1FiniteProducer n :=
  b1FiniteProducer_of_DTZeroElem_chart0 n hn (fun T => psiPolyCoord n (S T)) S f hTS
    (fun T p hp => psiPolyCoord_mem n (S T) hp) hf hS h hh hdeg h0

#print axioms b1FiniteProducer_of_psiPolyCoord_chart0

end LeanFormal.IUT.XiFPaper.Mzk1G1B1BranchPolyDTZeroInstanceActual
