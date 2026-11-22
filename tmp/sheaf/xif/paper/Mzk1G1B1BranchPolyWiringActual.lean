/-
B1 wiring: from grace's chart-0 `psiPolyCoord` data to the main B1 producer
`B1FiniteProducer n` (pure interface wiring; no new mathematics, no new geometry).

Donors (all DONE, three axioms each):
* `Mzk1G1B1BranchPolyDTZeroInstanceActual.b1FiniteProducer_of_psiPolyCoord_chart0`
  (DONE 15:04:26): the general-`T` chart-0 instance.  Its inputs are the point family
  `S`, the rational chart-0 coordinates `f`, the inclusions `hTS`, the vanishing
  certificates `hf`, nonemptiness `hS`, and the avoidance polynomial family `h` with
  `hh`, `hdeg`, `h0`; conclusion `B1FiniteProducer n`.
* `Mzk1G1B2PsiPolyActual.psiPolyCoord` / `psiPolyCoord_mem`: the general-`T` `u0`.
  The instance theorem already instantiates `u T := psiPolyCoord n (S T)`, so the
  vanishing hypothesis is free there; nothing to add here.
* `Mzk1G1B2PsiPolyHavoidActual`: `psiPoly`, `psiPoly_preimage_p1Zero_eq_DTZeroElem`,
  `aeval_notMem_of_eval_zero_ne`, `chartMorphism0_aeval_notMem_boundary`.  That value
  layer is consumed *inside* the branchPoly adapter, hence it is not re-stated here.
* `Mzk1G1PsiM2AnalyticActual.M2AnalyticTarget`: the analytic target; its polynomial
  `q` supplies the avoidance polynomial family in the reduced form below
  (`0 < q.natDegree`, `q.eval 0 ∉ {0,1}`; the transport `ℂ -> ℚ` is
  `Mzk1G1PsiM2AnalyticActual.aeval_zero_eq`).

What is PROVIDED here (interface wiring only):
1. `PsiPolyB1Data n`: the hypothesis package of the instance theorem as a `structure`.
2. `b1FiniteProducer_of_psiPolyData`: `(D : PsiPolyB1Data n) : B1FiniteProducer n`,
   one line from the donor instance theorem.
3. `b1FiniteProducer_of_psiPolyData_M2` (the tighter (b) form): the avoidance family
   `h` is *built* from grace's `M2AnalyticTarget`, so the only explicit inputs left are
   the geometric ones `S, f, hTS, hf, hS`.

(obligation: chart0_cover)  for each finite `T` produce `S T` with
    `(↑T : Set _) ⊆ fermatChart0ToCurve n '' (S T)` and `(S T).Nonempty`;
(obligation: chart0_coord)  produce `f T p` (`p ∈ S T`) with
    `chartX n - algebraMap ℚ (R n) (f T p) ∈ p.asIdeal`;
(obligation: T_to_Branch)   map `T ↦ Branch : Finset ℂ` so that `M2AnalyticTarget Branch`
    applies uniformly in `T` (the constant-avoidance reduction below uses one fixed
    `Branch`, hence one fixed `q`, for all `T`).

No sorry, no new axiom, no change of the target type; `B1FiniteProducer` is reused verbatim. -/
import tmp.sheaf.xif.paper.Mzk1G1B1BranchPolyDTZeroInstanceActual
import tmp.sheaf.xif.paper.Mzk1G1PsiM2AnalyticActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1B1BranchPolyWiringActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiB1Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1B2PsiPolyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B1BranchPolyDTZeroInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiM2AnalyticActual

/-- **The `psiPolyCoord` chart-0 data package.**  This is exactly the hypothesis list of
`b1FiniteProducer_of_psiPolyCoord_chart0`, bundled:
* `S T`: the finite set of chart-0 points whose image contains `T` (`hTS`);
* `f T`: rational chart-0 coordinates on `S T` (`hf`);
* `hS`: `S T` is nonempty;
* `h T`: the avoidance polynomial family (`hh`, `hdeg`, `h0`).

The general-`T` chart-0 function is `u T := psiPolyCoord n (S T)`; its vanishing on
`S T` is free (`psiPolyCoord_mem`), which is why it does not appear here. -/
structure PsiPolyB1Data (n : Nat) where
  /-- The point family covering `T` in the chart-0 affine piece. -/
  S : Finset (fermatCurveScheme n) → Finset (PrimeSpectrum (R n))
  /-- Rational chart-0 coordinates on `S T`. -/
  f : Finset (fermatCurveScheme n) → PrimeSpectrum (R n) → ℚ
  /-- `T` lies in the image of `S T` under the chart-0 map. -/
  hTS : ∀ T : Finset (fermatCurveScheme n),
    (↑T : Set (fermatCurveScheme n)) ⊆
      (fermatChart0ToCurve n) '' (S T : Set (PrimeSpectrum (R n)))
  /-- The rational coordinates give the chart-0 value on `S T`. -/
  hf : ∀ (T : Finset (fermatCurveScheme n)) (p : PrimeSpectrum (R n)),
    p ∈ S T → chartX n - algebraMap ℚ (R n) (f T p) ∈ p.asIdeal
  /-- `S T` is nonempty (needed for the cover lemma). -/
  hS : ∀ T : Finset (fermatCurveScheme n), (S T).Nonempty
  /-- The avoidance polynomial family. -/
  h : Finset (fermatCurveScheme n) → Polynomial ℚ
  hh : ∀ T : Finset (fermatCurveScheme n), h T ≠ 0
  hdeg : ∀ T : Finset (fermatCurveScheme n), 0 < (h T).natDegree
  h0 : ∀ T : Finset (fermatCurveScheme n), (h T).eval 0 ∉ ({0, 1} : Set ℚ)

/-- **B1 from the packaged `psiPolyCoord` chart-0 data.**  One-line projection to the
instance theorem `b1FiniteProducer_of_psiPolyCoord_chart0` (DONE 15:04:26). -/
theorem b1FiniteProducer_of_psiPolyData (n : Nat) (hn : 0 < n) (D : PsiPolyB1Data n) :
    B1FiniteProducer n :=
  b1FiniteProducer_of_psiPolyCoord_chart0 n hn D.S D.f D.hTS D.hf D.hS D.h D.hh D.hdeg D.h0

#print axioms b1FiniteProducer_of_psiPolyData

/-- **B1 from grace's `psiPolyCoord` data plus the analytic target** (the tighter form):
the avoidance family is the *constant* family `h T := q`, where `q` is the polynomial of
`M2AnalyticTarget Branch`; `q ≠ 0`, `0 < q.natDegree` follow from `hdeg`, and
`q.eval 0 ∉ {0,1}` is the target's fourth conjunct transported from `ℂ` to `ℚ` by
`aeval_zero_eq`.  What remains explicit are exactly the geometric pieces
`(obligation: chart0_cover)`, `(obligation: chart0_coord)` for `S, f, hTS, hf, hS`, and
one fixed `(obligation: T_to_Branch)`: a `Branch : Finset ℂ` valid for every `T`. -/
theorem b1FiniteProducer_of_psiPolyData_M2 (n : Nat) (hn : 0 < n)
    (S : Finset (fermatCurveScheme n) → Finset (PrimeSpectrum (R n)))
    (f : Finset (fermatCurveScheme n) → PrimeSpectrum (R n) → ℚ)
    (hTS : ∀ T : Finset (fermatCurveScheme n),
      (↑T : Set (fermatCurveScheme n)) ⊆
        (fermatChart0ToCurve n) '' (S T : Set (PrimeSpectrum (R n))))
    (hf : ∀ (T : Finset (fermatCurveScheme n)) (p : PrimeSpectrum (R n)),
      p ∈ S T → chartX n - algebraMap ℚ (R n) (f T p) ∈ p.asIdeal)
    (hS : ∀ T : Finset (fermatCurveScheme n), (S T).Nonempty)
    {Branch : Finset ℂ} (hM2 : M2AnalyticTarget Branch) :
    B1FiniteProducer n := by
  obtain ⟨q, hdeg, -, -, h0m2⟩ := hM2
  have hq : q ≠ 0 := by
    rintro rfl
    simp at hdeg
  have hq0 : Polynomial.eval (0 : ℚ) q ∉ ({0, 1} : Set ℚ) := by
    intro hmem
    apply h0m2
    rw [aeval_zero_eq]
    rcases (show Polynomial.eval (0 : ℚ) q = 0 ∨ Polynomial.eval (0 : ℚ) q = 1 by
      simpa using hmem) with h | h <;> simp [h]
  exact b1FiniteProducer_of_psiPolyData n hn
    { S := S, f := f, hTS := hTS, hf := hf, hS := hS, h := fun _ => q,
      hh := fun _ => hq, hdeg := fun _ => hdeg, h0 := fun _ => hq0 }

#print axioms b1FiniteProducer_of_psiPolyData_M2

end LeanFormal.IUT.XiFPaper.Mzk1G1B1BranchPolyWiringActual
