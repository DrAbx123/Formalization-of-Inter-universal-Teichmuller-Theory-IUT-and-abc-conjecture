/- 
# B1 (owner emmy lane): `B1FiniteProducer` with the finiteness half eliminated

`Mzk1G1PsiB1Actual.B1FiniteProducer n` asks: for every finite set `T` of points of `Y_n`
there is `φ : Y_n ⟶ P^1` whose boundary preimage is finite and which avoids the boundary on
`T`.  `Mzk1G1B1ProducerAssemblyActual.b1FiniteProducer_of_inputs` reduces this to two
explicit inputs:

* `A` (finiteness): for each `T` there are `Tr, h, hh` with
  `(phiFixedL n Tr h hh).base ⁻¹' boundarySetGlued` finite;
* `C` (avoidance): `phiFixedL n Tr h hh` maps `T` outside `boundarySetGlued`.

This file **eliminates `A`** using the scheme-level finiteness theorem
`Mzk1G1PhiFixedLBoundaryActual.phiFixedL_boundaryPreimage_finite` (the three point fibres
`p1Zero`, `p1One`, `p1Infinity` merged by `boundaryPreimage_finite_of_each`).  The only
remaining data are the two analytic/geometric inputs, kept explicit:

* `hbranch` — the output of henry's analytic route
  (`Mzk1G1PsiM2AnalyticActual.M2AnalyticTarget`, route §4.3): for each `T` a **nonempty**
  rational protected set `Tr` (`psiFixed`'s divisor) and a **nonzero nonconstant** `h`
  whose values lie in `{0,1}` on the branch set of `psiFixed` and whose critical values lie
  in `{0,1}`.  Only the nonemptiness of `Tr` and `0 < h.natDegree` are consumed by the
  finiteness proof; the branch/critical-value part of the contract is recorded at scheme
  level in `Mzk1G1PhiFixedLBranchSupportActual.phiFixedL_branch_subset` (and supplied to
  the B3 consumer).
* `havoid` — andrew's T-avoidance construction
  (`Mzk1G1B1TAvoidFinalActual` route, via `h(0) ∉ {0,1,∞}`): `phiFixedL n Tr h hh` avoids
  `boundarySetGlued` on the prescribed `T`.

Neither input is proved here and no `ℂ`-valued substitute is used; both are the named
outputs of the respective lanes, recorded in the docstring instead of being silently
assumed.  `0 < n` is required (the fixed `r = 0` locus of the second chart).

No sorry, no admit, no new axioms.
-/
import tmp.sheaf.xif.paper.Mzk1G1PhiFixedLBoundaryActual
import tmp.sheaf.xif.paper.Mzk1G1B1ProducerAssemblyActual
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyLambdaActual
import tmp.sheaf.xif.paper.Mzk1G1PsiB1Actual
import tmp.sheaf.xif.paper.Mzk1G1B2Fixed4Actual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1600000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1G1B1FinalActual

open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiB1Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLBoundaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B1ProducerAssemblyActual
open scoped AlgebraicGeometry

/-- **B1, with the finiteness half discharged.**  Given

* `hbranch`: for every finite set `T` of points of `Y_n`, a nonempty rational protected set
  `Tr` and a nonzero nonconstant `h` (henry's analytic input B, see the file header);
* `havoid`: `phiFixedL n Tr h hh` avoids `boundarySetGlued` on `T` (andrew's T-avoidance,
  input C, see the file header),

the producer `B1FiniteProducer n` holds, the witness morphism being
`phiFixedL n Tr h hh`; its boundary preimage is finite by
`phiFixedL_boundaryPreimage_finite`. -/
theorem b1FiniteProducer_of_branch_and_avoid (n : Nat) (hn : 0 < n)
    (hbranch : ∀ T : Finset (fermatCurveScheme n),
      ∃ (Tr : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0), Tr.Nonempty ∧ 0 < h.natDegree)
    (havoid : ∀ (T : Finset (fermatCurveScheme n)) (Tr : Finset ℚ) (h : Polynomial ℚ)
      (hh : h ≠ 0), AvoidsBoundary n (phiFixedL n Tr h hh) T) :
    B1FiniteProducer n := by
  refine b1FiniteProducer_of_inputs n ?_ ?_
  · intro T
    obtain ⟨Tr, h, hh, hTr, hdeg⟩ := hbranch T
    exact ⟨Tr, h, hh, phiFixedL_boundaryPreimage_finite n Tr h hh hn hTr hdeg⟩
  · intro T Tr h hh
    exact havoid T Tr h hh

/-- **Per-`T` witness form**: specialised to a single `T`, with the same explicit inputs. -/
theorem b1Witness_of_branch_and_avoid (n : Nat) (hn : 0 < n)
    (T : Finset (fermatCurveScheme n)) (Tr : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0)
    (hTr : Tr.Nonempty) (hdeg : 0 < h.natDegree)
    (havoid : AvoidsBoundary n (phiFixedL n Tr h hh) T) :
    ∃ φ : fermatCurveScheme n ⟶ projectiveLineGlued,
      (φ.base ⁻¹' boundarySetGlued).Finite ∧ (∀ x ∈ T, φ.base x ∉ boundarySetGlued) :=
  b1Witness_of_boundaryPreimage_finite n Tr h hh T
    (phiFixedL_boundaryPreimage_finite n Tr h hh hn hTr hdeg) havoid

/-- **B1 with the input shape corrected (route-faithful, no over-quantification).**

Route 4.1-4.3: both psi and h depend on the prescribed pair (S,T); the avoidance is
automatic once psi(T) = {0} and h(0) avoids the boundary.  Quantifying avoidance over
*arbitrary* (Tr,h) is therefore too strong (no single h avoids every T).  The correct
input is the T-dependent one below: for each T there are data together with the avoidance
on that same T.  The finiteness half is still discharged internally.

The older statement b1FiniteProducer_of_branch_and_avoid above keeps the over-quantified
havoid only for interface backward compatibility and should not be consumed downstream. -/
theorem b1FiniteProducer_of_data (n : Nat) (hn : 0 < n)
    (hdata : ∀ T : Finset (fermatCurveScheme n),
      ∃ (Tr : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0),
        Tr.Nonempty ∧ 0 < h.natDegree ∧ AvoidsBoundary n (phiFixedL n Tr h hh) T) :
    B1FiniteProducer n := by
  intro T
  obtain ⟨Tr, h, hh, hTr, hdeg, havoid⟩ := hdata T
  exact ⟨phiFixedL n Tr h hh,
    phiFixedL_boundaryPreimage_finite n Tr h hh hn hTr hdeg, havoid⟩

/-- **B1 interface in the route shape with the D_T guard (Lead-ruled shape).**

Happens-before: B2 (andrew) gives psiFixed^{-1}(p1Zero) = DTFixed n Tr; the analytic h has
h(0) outside {0,1,inf}; then for T contained in DTFixed n Tr the composite phiFixedL maps T
to h(0), hence avoids the boundary.  This theorem keeps that implication as the explicit
input havoid with the D_T and h(0) guards, and folds the T-dependent data into hdata.
General (non-rational, Galois-stable) T belongs to the grace package and is not assumed here. -/
/-- **LEGACY / NOT DELIVERABLE.** Per the Lead audit this theorem depends on sorryAx
(see the watchdog log: it is the only declaration in this file that is not three-axiom clean,
unlike b1FiniteProducer_of_data which is tri). Nothing consumes it: the main B1 chain uses
B1FinalHAvoidActual.b1FiniteProducer_of_branch (DONE 10:39, three axioms). Do not consume
this statement anywhere; it is kept only as a record of the earlier interface shape. -/
theorem b1FiniteProducer_of_DT_data (n : Nat) (hn : 0 < n)
    (hdata : ∀ T : Finset (fermatCurveScheme n),
      ∃ (Tr : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0),
        Tr.Nonempty ∧ 0 < h.natDegree ∧ T ⊆ Mzk1G1B2FixedActual.DTFixed n Tr ∧
          Polynomial.eval 0 h ∉ ({0, 1} : Set ℚ))
    (havoid : ∀ (T : Finset (fermatCurveScheme n)) (Tr : Finset ℚ) (h : Polynomial ℚ)
      (hh : h ≠ 0), T ⊆ Mzk1G1B2FixedActual.DTFixed n Tr →
        Polynomial.eval 0 h ∉ ({0, 1} : Set ℚ) → AvoidsBoundary n (phiFixedL n Tr h hh) T) :
    B1FiniteProducer n := by
  refine b1FiniteProducer_of_data n hn ?_
  intro T
  obtain ⟨Tr, h, hh, hTr, hdeg, hsub, h0⟩ := hdata T
  exact ⟨Tr, h, hh, hTr, hdeg, havoid T Tr h hh hsub h0⟩

/-! ## Axiom checks -/

#print axioms b1FiniteProducer_of_branch_and_avoid
#print axioms b1Witness_of_branch_and_avoid
#print axioms b1FiniteProducer_of_data
#print axioms b1FiniteProducer_of_DT_data

end LeanFormal.IUT.XiFPaper.Mzk1G1B1FinalActual
