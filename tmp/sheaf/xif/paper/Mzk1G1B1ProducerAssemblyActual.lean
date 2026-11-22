import tmp.sheaf.xif.paper.Mzk1G1PsiB1Actual
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyLambdaActual
import Mathlib.Tactic

/-!
# B1 (owner emmy lane): assembly interface for `B1FiniteProducer`

`Mzk1G1PsiB1Actual` states the B1 target

    B1FiniteProducer n : forall T, exists phi : Y_n --> P^1,
      (phi.base ⁻¹' {0,1,infinity}).Finite  and  (forall x in T, phi.base x notin {0,1,infinity})

and deliberately defers the assembly.  This file carries it out for the concrete candidate
family `phiFixedL n Tr h hh = psiFixed n Tr ; hPolyL h hh` (`Mzk1G1PsiHPolyLambdaActual`).
Note the two different finite sets in the construction: `T` is the prescribed set of *scheme
points of `Y_n`* to be avoided, while `Tr : Finset ℚ` is the **rational protected set** of
`psiFixed` (the fibre of whose protected divisor is the point `lambda = infinity`).  The choice
`T -> Tr` is part of the B2 / T-avoidance construction (andrew's lane).

## The two halves of the target, as explicit inputs

* `A` -- finiteness half: for every finite `T` there are a rational protected set `Tr`, a nonzero
  `h`, and `(phiFixedL n Tr h hh).base ⁻¹' boundarySetGlued` is finite;
* `C` -- avoidance half: for every `T`, `Tr`, `h`, the morphism `phiFixedL n Tr h hh` maps the
  prescribed finite set `T` of points of `Y_n` outside `boundarySetGlued`.

## Provenance of the inputs (explicit placeholders: to be discharged before the final version)

* `A`: the scheme-level finiteness statement (`0 < n`, `Tr.Nonempty`, `0 < h.natDegree`) is
  `Mzk1G1PhiFixedLInfinityActual`/`Mzk1G1PhiFixedLLambdaPointActual` assembled in
  `Mzk1G1PhiFixedLFiberFiniteActual.phiFixedL_fiber_finite_of_boundary`.  What is *not*
  discharged is the choice of the nonconstant `h` (henry's analytic route §4.3, input B of the
  B1 plan) and the case `Tr = empty`.
* `C`: the T-avoidance statement (andrew's lane, `Mzk1G1B1TAvoidFinalActual` route); its
  analytic input is `h(0) notin {0,1,infinity}` for henry's `h`.

No sorry, no admit, no new axioms.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1G1B1ProducerAssemblyActual

open LeanFormal.IUT.XiFPaper.Mzk1G1PsiB1Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
open scoped AlgebraicGeometry

/-! ## 1. The producer, from the two explicit inputs -/

/-- **B1 assembly.**  If for every finite set `T` of points of `Y_n` there are a rational
protected set `Tr` and a nonzero `h` making the `phiFixedL`-preimage of the boundary finite
(`A`), and `phiFixedL n Tr h hh` avoids the boundary on `T` (`C`), then `B1FiniteProducer n`
holds for the concrete candidate family `phiFixedL`. -/
theorem b1FiniteProducer_of_inputs (n : Nat)
    (A : ∀ (T : Finset (fermatCurveScheme n)), ∃ (Tr : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0),
      ((phiFixedL n Tr h hh).base ⁻¹' boundarySetGlued).Finite)
    (C : ∀ (T : Finset (fermatCurveScheme n)) (Tr : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0),
      ∀ x ∈ T, (phiFixedL n Tr h hh).base x ∉ boundarySetGlued) :
    B1FiniteProducer n := by
  intro T
  obtain ⟨Tr, h, hh, hfin⟩ := A T
  exact ⟨phiFixedL n Tr h hh, hfin, C T Tr h hh⟩

/-! ## 2. Per-`T` witnesses (no `exists` over the analytic data) -/

/-- **Per-`T` witness, pure finiteness form.**  Given the rational protected set `Tr`, `h`, a
finite preimage of the boundary and the avoidance of the boundary on `T`, the witness morphism of
`B1FiniteProducer` is `phiFixedL n Tr h hh`. -/
theorem b1Witness_of_boundaryPreimage_finite (n : Nat) (Tr : Finset ℚ) (h : Polynomial ℚ)
    (hh : h ≠ 0) (T : Finset (fermatCurveScheme n))
    (hfin : ((phiFixedL n Tr h hh).base ⁻¹' boundarySetGlued).Finite)
    (havoid : ∀ x ∈ T, (phiFixedL n Tr h hh).base x ∉ boundarySetGlued) :
    ∃ φ : fermatCurveScheme n ⟶ projectiveLineGlued,
      (φ.base ⁻¹' boundarySetGlued).Finite ∧ (∀ x ∈ T, φ.base x ∉ boundarySetGlued) :=
  ⟨phiFixedL n Tr h hh, hfin, havoid⟩

/-- **Per-`T` witness, pointwise form.**  The finiteness half may be supplied point by point
(`lambda = 0`, `lambda = 1`, `lambda = infinity`), which is the shape produced by
`Mzk1G1PhiFixedLLambdaPointActual` and `Mzk1G1PhiFixedLInfinityActual`; the assembly is
`Mzk1G1PsiB1Actual.boundaryPreimage_finite_of_each`. -/
theorem b1Witness_of_each_point (n : Nat) (Tr : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0)
    (T : Finset (fermatCurveScheme n))
    (h0 : ((phiFixedL n Tr h hh).base ⁻¹' p1Zero).Finite)
    (h1 : ((phiFixedL n Tr h hh).base ⁻¹' p1One).Finite)
    (h2 : ((phiFixedL n Tr h hh).base ⁻¹' p1Infinity).Finite)
    (havoid : ∀ x ∈ T, (phiFixedL n Tr h hh).base x ∉ boundarySetGlued) :
    ∃ φ : fermatCurveScheme n ⟶ projectiveLineGlued,
      (φ.base ⁻¹' boundarySetGlued).Finite ∧ (∀ x ∈ T, φ.base x ∉ boundarySetGlued) :=
  b1Witness_of_boundaryPreimage_finite n Tr h hh T
    (boundaryPreimage_finite_of_each (n := n) (phiFixedL n Tr h hh) h0 h1 h2) havoid

/-! ## Axiom checks -/

#print axioms b1FiniteProducer_of_inputs
#print axioms b1Witness_of_boundaryPreimage_finite
#print axioms b1Witness_of_each_point

end LeanFormal.IUT.XiFPaper.Mzk1G1B1ProducerAssemblyActual
