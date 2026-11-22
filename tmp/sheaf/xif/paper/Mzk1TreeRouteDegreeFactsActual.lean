import LeanFormal.IUT.IUTIII.Corollary312.Routes
import LeanFormal.IUT.IUTIII.Corollary312.Obligations
import tmp.sheaf.xif.paper.Mzk1RRInterfaceActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: Cor312 route distinctness + flt_core degree facts -> Cor312Route (Routes:32, deriving DecidableEq) + Audit obligations (Obligations:5/12/19) + Mzk1RRInterfaceActual.degree_single_interface/deg_eq_one_interface -> PROVED: the three routes are pairwise distinct; obligation sources recorded; degree facts re-exported. No new math; no closure.

# Mzk1TreeRouteDegreeFactsActual — route distinctness and degree facts

PROVED: pairwise route distinctness; obligation source strings; `Divisor.degree` single/place-degree
re-exports from the flt_core interface.  Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeRouteDegreeFactsActual

open LeanFormal.IUT
open LeanFormal.IUT.Audit
open LeanFormal.IUT.XiFPaper.Mzk1RRInterfaceActual

theorem route_ne_mochizuki_teich :
    Cor312Route.mochizuki3115 ≠ Cor312Route.arithmeticTeichmuller := by decide

theorem route_ne_mochizuki_sarkisyan :
    Cor312Route.mochizuki3115 ≠ Cor312Route.sarkisyanErdosKac := by decide

theorem route_ne_teich_sarkisyan :
    Cor312Route.arithmeticTeichmuller ≠ Cor312Route.sarkisyanErdosKac := by decide

theorem obligation_sources :
    ipl.source = "IUT III, Corollary 3.12 proof, Step (xi-a)" ∧
      she.source = "IUT III, Corollary 3.12 proof, Step (xi-b)" ∧
      apt.source = "IUT III, Corollary 3.12 proof, Step (xi-c)" := ⟨rfl, rfl, rfl⟩

/-- **PROVED:** degree of a single-place divisor, re-exported. -/
theorem degree_single_fact {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) (n : ℤ) :
    AlgebraicCurve.Divisor.degree (Finsupp.single v n) = n * v.deg :=
  degree_single_interface v n

def routeDegreeRows : List (String × String × String) :=
  [ ("route pairwise distinctness", "PROVED", "route_ne_* (Routes:32 deriving DecidableEq)")
  , ("obligation sources", "PROVED", "obligation_sources (Obligations:5/12/19)")
  , ("degree of single divisor", "PROVED", "degree_single_fact (flt_core interface)")
  , ("StepXI contract negation", "NAMED", "contract construction Obligation") ]

theorem routeDegreeRows_length : routeDegreeRows.length = 4 := rfl

#check route_ne_mochizuki_teich
#check obligation_sources
#check degree_single_fact
#check routeDegreeRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeRouteDegreeFactsActual
end