/- 
# B1 (owner emmy lane): the boundary preimage of `phiFixedL` is finite (consumer form)

This is the named consumer form of the finiteness half of `B1FiniteProducer` for the
candidate morphism `phiFixedL n T h hh = psiFixed n T ≫ hPolyL h hh`:

  `(phiFixedL n T h hh).base ⁻¹' boundarySetGlued` is finite,

obtained by merging the three point fibres of the boundary set
`boundarySetGlued = p1Zero ∪ p1One ∪ p1Infinity` with
`Mzk1G1PsiB1Actual.boundaryPreimage_finite_of_each`:

* `p1Zero` (`lambda = 0`): `phiFixedL_fiber_finite_p1Zero`
  (`Mzk1G1PhiFixedLLambdaPointActual`),
* `p1One` (`lambda = 1`): `phiFixedL_fiber_finite_p1One`
  (`Mzk1G1PhiFixedLLambdaPointActual`),
* `p1Infinity` (`t = 0`, i.e. `lambda = infinity`): `phiFixedL_fiber_finite_p1Infinity`
  (`Mzk1G1PhiFixedLInfinityActual`).

Conditions (exactly those of the two lambda-chart point fibres; the infinity fibre needs
none of them beyond `0 < n`): `0 < n` (the fixed `r = 0` locus of the second chart),
`T ≠ ∅` and `0 < h.natDegree` (nonconstant `h`).

The remaining half of `B1FiniteProducer` — boundary *avoidance* on a prescribed finite set
of points of `Y_n` — is the separate B2/T-avoidance statement (andrew's lane), not part of
this file.  The parametrised assembly is `Mzk1G1B1FinalActual`.

No sorry, no admit, no new axioms.
-/
import tmp.sheaf.xif.paper.Mzk1G1PhiFixedLLambdaPointActual
import tmp.sheaf.xif.paper.Mzk1G1PhiFixedLInfinityActual
import tmp.sheaf.xif.paper.Mzk1G1PsiB1Actual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1600000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLBoundaryActual

open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatTwoChartGluingActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1InvActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLLambdaPointActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLInfinityActual
open scoped AlgebraicGeometry

/-- **B1 finiteness half for `phiFixedL`**: the preimage of the boundary set
`{0, 1, ∞}` under `phiFixedL` is finite.  Merges the three point fibres
(`p1Zero`, `p1One`, `p1Infinity`) via `boundaryPreimage_finite_of_each`. -/
theorem phiFixedL_boundaryPreimage_finite (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ)
    (hh : h ≠ 0) (hn : 0 < n) (hT : T.Nonempty) (hdeg : 0 < h.natDegree) :
    ((phiFixedL n T h hh).base ⁻¹' boundarySetGlued).Finite :=
  Mzk1G1PsiB1Actual.boundaryPreimage_finite_of_each (n := n) (phiFixedL n T h hh)
    (phiFixedL_fiber_finite_p1Zero n T h hh hn hT hdeg)
    (phiFixedL_fiber_finite_p1One n T h hh hn hT hdeg)
    (phiFixedL_fiber_finite_p1Infinity n T h hh hn)

/-! ## Axiom checks -/

#print axioms phiFixedL_boundaryPreimage_finite

end LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLBoundaryActual
