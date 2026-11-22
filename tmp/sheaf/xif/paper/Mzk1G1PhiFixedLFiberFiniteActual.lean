/-
# B1 (owner emmy lane): three-point assembly of the `phiFixedL` fibre finiteness

`phiFixedL n T h hh = psiFixed n T ; hPolyL h hh` (`Mzk1G1PsiHPolyLambdaActual`).  This file
collects the fibre-finiteness statements for the B1 boundary set
`boundarySetGlued = {0, 1, infinity}` into one consumer interface, mirroring
`Mzk1G1PhiFiberFiniteFixedActual` for the older `phiFixed = psiFixed ; hPoly`.

## Contents (structure: old `phiFixed` file, with `phiFixed` replaced by `phiFixedL`)

1. `phiFixedL_fiber_subset` -- the fibre is covered by the first chart together with the fixed
   `r = 0` locus of the second piece (proved in `Mzk1G1PhiFixedLFiberActual`);
2. `phiFixedL_fiber_finite_of_chart0` -- a finite bound on the first-chart part gives the whole
   fibre (same file);
3. `phiFixedL_fiber_finite_p1Zero`, `_p1One` -- the lambda-chart points `lambda = 0, 1`, which
   with the chart swap are ordinary lambda-chart points of rational coordinate
   (`Mzk1G1PhiFixedLLambdaPointActual`);
4. `phiFixedL_fiber_finite_p1Infinity` -- `t = 0` i.e. `lambda = infinity`, which the first
   chart never hits (`Mzk1G1PhiFixedLInfinityActual`), so no condition on `h` is needed;
5. `phiFixedL_fiber_finite_of_boundary` -- the union of the three point fibres, i.e. the
   finiteness half of `B1FiniteProducer` for the candidate `phiFixedL`
   (`Mzk1G1PsiB1Actual.boundaryPreimage_finite_of_each`).

Declarations 1-4 are *re-exports* (the proofs live in the files named above); declaration 5 is
the new assembly.  No sorry, no admit, no new axioms.
-/
import tmp.sheaf.xif.paper.Mzk1G1PhiFixedLFiberActual
import tmp.sheaf.xif.paper.Mzk1G1PhiFixedLLambdaPointActual
import tmp.sheaf.xif.paper.Mzk1G1PhiFixedLInfinityActual
import tmp.sheaf.xif.paper.Mzk1G1PsiB1Actual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1600000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLFiberFiniteActual

open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatTwoChartGluingActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartFiniteGActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1InvActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiB1Actual
open scoped AlgebraicGeometry

/-! ## 1. Structural reduction (re-export) -/

/-- The fibre of `phiFixedL` is covered by the first chart together with the fixed `r = 0`
locus of the second piece.  (Proof: `Mzk1G1PhiFixedLFiberActual.phiFixedL_fiber_subset`.) -/
theorem phiFixedL_fiber_subset (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0)
    (q : projectiveLineGlued) :
    (phiFixedL n T h hh).base ⁻¹' {q} ⊆
      (fermatChart0ToCurve n).base '' ((fermatChart0ToCurve n).base ⁻¹'
        ((phiFixedL n T h hh).base ⁻¹' {q}))
      ∪ (qPiece n T).base '' {P : PrimeSpectrum (Localization.Away (psiChartInfDenom n T)) |
          algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T)) (chartR n) ∈
            P.asIdeal} :=
  Mzk1G1PhiFixedLFiberActual.phiFixedL_fiber_subset n T h hh q

/-- A finite bound on the first-chart part of the fibre of `phiFixedL` makes the whole fibre
finite (scoped `0 < n`).  (Proof: `Mzk1G1PhiFixedLFiberActual.phiFixedL_fiber_finite_of_chart0`.)
-/
theorem phiFixedL_fiber_finite_of_chart0 (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ)
    (hh : h ≠ 0) (hn : 0 < n) (q : projectiveLineGlued) (S : Set (PrimeSpectrum (R n)))
    (hS : S.Finite)
    (hsub : (fermatChart0ToCurve n).base ⁻¹' ((phiFixedL n T h hh).base ⁻¹' {q}) ⊆ S) :
    ((phiFixedL n T h hh).base ⁻¹' {q}).Finite :=
  Mzk1G1PhiFixedLFiberActual.phiFixedL_fiber_finite_of_chart0 n T h hh hn q S hS hsub

/-! ## 2. The three boundary points `{0, 1, infinity}` (re-export) -/

/-- The fibre of `phiFixedL` over `lambda = 0` is finite.
(Proof: `Mzk1G1PhiFixedLLambdaPointActual.phiFixedL_fiber_finite_p1Zero`.) -/
theorem phiFixedL_fiber_finite_p1Zero (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ)
    (hh : h ≠ 0) (hn : 0 < n) (hT : T.Nonempty) (hdeg : 0 < h.natDegree) :
    ((phiFixedL n T h hh).base ⁻¹' p1Zero).Finite :=
  Mzk1G1PhiFixedLLambdaPointActual.phiFixedL_fiber_finite_p1Zero n T h hh hn hT hdeg

/-- The fibre of `phiFixedL` over `lambda = 1` is finite.
(Proof: `Mzk1G1PhiFixedLLambdaPointActual.phiFixedL_fiber_finite_p1One`.) -/
theorem phiFixedL_fiber_finite_p1One (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ)
    (hh : h ≠ 0) (hn : 0 < n) (hT : T.Nonempty) (hdeg : 0 < h.natDegree) :
    ((phiFixedL n T h hh).base ⁻¹' p1One).Finite :=
  Mzk1G1PhiFixedLLambdaPointActual.phiFixedL_fiber_finite_p1One n T h hh hn hT hdeg

/-- The fibre of `phiFixedL` over `lambda = infinity` (`t = 0`) is finite: the first chart
never hits the point, so only the fixed `r = 0` locus contributes.
(Proof: `Mzk1G1PhiFixedLInfinityActual.phiFixedL_fiber_finite_p1Infinity`.) -/
theorem phiFixedL_fiber_finite_p1Infinity (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ)
    (hh : h ≠ 0) (hn : 0 < n) :
    ((phiFixedL n T h hh).base ⁻¹' p1Infinity).Finite :=
  Mzk1G1PhiFixedLInfinityActual.phiFixedL_fiber_finite_p1Infinity n T h hh hn

/-! ## 3. Assembly over the boundary set (new) -/

/-- **Finiteness half of `B1FiniteProducer` for `phiFixedL`**: the preimage of the boundary set
`{0, 1, infinity}` under `phiFixedL` is finite.  This is the union of the three point fibres
(`Mzk1G1PsiB1Actual.boundaryPreimage_finite_of_each`).  Conditions: `0 < n` (for the fixed
`r = 0` locus of the second chart), `T ≠ ∅` and `0 < h.natDegree` (for the two lambda-chart
points); the `lambda = infinity` fibre needs only `h ≠ 0`. -/
theorem phiFixedL_fiber_finite_of_boundary (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ)
    (hh : h ≠ 0) (hn : 0 < n) (hT : T.Nonempty) (hdeg : 0 < h.natDegree) :
    ((phiFixedL n T h hh).base ⁻¹' boundarySetGlued).Finite :=
  Mzk1G1PsiB1Actual.boundaryPreimage_finite_of_each (n := n) (phiFixedL n T h hh)
    (phiFixedL_fiber_finite_p1Zero n T h hh hn hT hdeg)
    (phiFixedL_fiber_finite_p1One n T h hh hn hT hdeg)
    (phiFixedL_fiber_finite_p1Infinity n T h hh hn)

/-! ## Axiom checks -/

#print axioms phiFixedL_fiber_subset
#print axioms phiFixedL_fiber_finite_of_chart0
#print axioms phiFixedL_fiber_finite_p1Zero
#print axioms phiFixedL_fiber_finite_p1One
#print axioms phiFixedL_fiber_finite_p1Infinity
#print axioms phiFixedL_fiber_finite_of_boundary

end LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLFiberFiniteActual
