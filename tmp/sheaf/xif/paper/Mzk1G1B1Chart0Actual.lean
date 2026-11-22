import tmp.sheaf.xif.paper.Mzk1G1B1DependentActual
import tmp.sheaf.xif.paper.Mzk1G1B1HAvoidFinalActual
import tmp.sheaf.xif.paper.Mzk1G1B1DTSubsetActual
import tmp.sheaf.xif.paper.Mzk1G1PsiM2BranchDataActual
import tmp.sheaf.xif.paper.Mzk1G1B2Fixed4Actual
import Mathlib.Tactic
/-!
# B1: **restricted-class conditional assembly** from chart-0 rational data

NOTE (Lead 2026-11-17): the hypothesis `hdata` below (every scheme `T` is a chart-0 image
with rational coordinate certificate) is an **explicit assumption**, not a theorem for an
arbitrary `T`.  Hence this file gives `B1FiniteProducer` only on the restricted class
"chart-0 rational-coordinate T"; **B1 in general remains OPEN (O5)** (needs grace's §4.1
RR / `hdata` construction).  It is not a closed node.

Route §4.1-4.3 restricted to the FIRST chart with rational coordinate: `T` is the
`fermatChart0ToCurve` image of a finite set of primes `S`, each containing
`chartX - f q` for a rational `f q`.  Grace's selection lemma
(`Mzk1G1B1DTSubsetActual.chart0_point_mem_DTFixed_of_rational`) gives `T ⊆ DTFixed n Tr`
with `Tr = S.image f`; emmy's `phiFixedL_T_avoid_data` gives avoidance; finiteness is
`phiFixedL_boundaryPreimage_finite` (inside `b1FiniteProducer_of_dependent`).
The arbitrary geometric `T` case remains the route §4.1 Riemann-Roch/G-C obligation.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.B1Chart0Actual
open LeanFormal.IUT.XiFPaper.B1DependentActual
open LeanFormal.IUT.XiFPaper.B1HAvoidFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B1DTSubsetActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiM2BranchDataActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B2FixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiB1Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual

/-- `h.eval 0 ∉ {0,1}` over `ℚ` transports to `aeval 0 h ∉ {0,1}` over `ℂ`. -/
theorem h0c_of_h0 {h : Polynomial ℚ} (h0 : h.eval 0 ∉ ({0, 1} : Set ℚ)) :
    Polynomial.aeval (0 : ℂ) h ∉ ({0, 1} : Set ℂ) := by
  intro hmem
  have hconv : Polynomial.aeval (0 : ℂ) h = algebraMap ℚ ℂ (h.eval 0) := by
    simpa only [map_zero] using
      (Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (R := ℚ) (A := ℂ) (x := (0:ℚ)) (p := h))
  rw [hconv] at hmem
  rcases hmem with hz | ho
  · have hz' : ((h.eval (0:ℚ) : ℚ) : ℂ) = ((0:ℚ) : ℂ) := by simpa using hz
    have hq : h.eval (0:ℚ) = 0 := by exact_mod_cast hz'
    exact h0 (by simp [hq])
  · have ho' : ((h.eval (0:ℚ) : ℚ) : ℂ) = ((1:ℚ) : ℂ) := by simpa using ho
    have hq : h.eval (0:ℚ) = 1 := by exact_mod_cast ho'
    exact h0 (by simp [hq])
theorem b1FiniteProducer_of_chart0_data (n : Nat) (hn : 0 < n)
    (hdata : ∀ T : Finset (fermatCurveScheme n),
      ∃ (S : Finset (PrimeSpectrum (R n))) (f : PrimeSpectrum (R n) → ℚ)
        (h : Polynomial ℚ) (hh : h ≠ 0),
        (↑T : Set (fermatCurveScheme n)) = (fermatChart0ToCurve n).base '' (S : Set (PrimeSpectrum (R n))) ∧
        (∀ q ∈ S, chartX n - algebraMap ℚ (R n) (f q) ∈ q.asIdeal) ∧
        (S.image f).Nonempty ∧ 0 < h.natDegree ∧
        h.eval 0 ∉ ({0, 1} : Set ℚ)) :
    B1FiniteProducer n :=
  b1FiniteProducer_of_dependent n hn
    (fun T => by
      obtain ⟨S, f, h, hh, hT, hf, hne, hdeg, h0⟩ := hdata T
      refine ⟨S.image f, h, hh, hne, hdeg, ?_, h0⟩
      rw [hT]
      intro x hx
      obtain ⟨p, hp, rfl⟩ := hx
      exact chart0_point_mem_DTFixed_of_rational n S f hf p hp)
    (fun T Tr h hh hT h0 =>
      phiFixedL_T_avoid_data n T Tr h hh hT (h0c_of_h0 h0))

#print axioms h0c_of_h0
#print axioms b1FiniteProducer_of_chart0_data
end LeanFormal.IUT.XiFPaper.B1Chart0Actual
end