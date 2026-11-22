/-
# Probe: is `evalAt a q` definitionally `Polynomial.aeval a q` ?

Used to decide whether the lambda-chart dictionary of
`Mzk1G1PhiFixedLChart0BoundaryActual` can be stated with `Polynomial.aeval`
(`evalAt` is defined as `(Polynomial.aeval (R := ℚ) a).toRingHom`).
No sorry, no axiom.
-/
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineTransitionActual
import Mathlib.Tactic

noncomputable section
open Polynomial

namespace LeanFormal.IUT.XiFPaper.ProbeEvalAtAevalActual

open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual

/-- `evalAt a q` is `Polynomial.aeval a q` definitionally. -/
theorem evalAt_apply_aeval {R : Type} [CommRing R] [Algebra ℚ R] (a : R) (q : Polynomial ℚ) :
    evalAt a q = Polynomial.aeval a q := rfl

#print axioms evalAt_apply_aeval

end LeanFormal.IUT.XiFPaper.ProbeEvalAtAevalActual
