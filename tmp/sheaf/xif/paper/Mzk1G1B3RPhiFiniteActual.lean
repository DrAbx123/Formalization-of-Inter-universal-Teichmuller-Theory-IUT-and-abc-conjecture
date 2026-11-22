/- B3: finiteness of the ramification locus of phi = phiFixedL (route L334 / B1).
   Uses the ported LANA finite_ram (Mzk1G1BelyiRamificationActual, 23:24:10). The technical
   hypotheses (locally of finite presentation, irreducible/Noetherian/kdim<=1, generic smooth) are
   the donor's own; the kbar side supplies them via (h) kbar_integral. No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyLambdaActual
import tmp.sheaf.xif.paper.Mzk1G1PsiFixedActual
import tmp.sheaf.xif.paper.Mzk1G1BelyiRamificationActual
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveActual
import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1B3RPhiFiniteActual
open LeanFormal.IUT.XiFPaper.BelyiRamification
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual

/-- **R_φ 有限性**（`finite_ram` 的直接应用）。 -/
theorem ram_phi_finite (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0)
    (hLFP : LocallyOfFinitePresentation (phiFixedL n T h hh))
    (hI : IrreducibleSpace (fermatCurveScheme n))
    (hN : TopologicalSpace.NoetherianSpace (fermatCurveScheme n))
    (hdim : ∀ x : fermatCurveScheme n,
      Ring.KrullDimLE 1 ((fermatCurveScheme n).presheaf.stalk x))
    (hgen : genericPoint (fermatCurveScheme n) ∈ (phiFixedL n T h hh).smoothLocus) :
    (LeanFormal.IUT.XiFPaper.BelyiRamification.Ram (phiFixedL n T h hh)).Finite := by
  haveI := hLFP
  haveI := hI
  haveI := hN
  exact LeanFormal.IUT.XiFPaper.BelyiRamification.finite_ram (f := phiFixedL n T h hh) hdim hgen

#print axioms ram_phi_finite

end LeanFormal.IUT.XiFPaper.Mzk1G1B3RPhiFiniteActual