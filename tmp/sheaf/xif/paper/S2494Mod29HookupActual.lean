import tmp.sheaf.xif.paper.S2492Mod29FactorizationActual
import tmp.sheaf.xif.paper.S2493UnitScalingActual
import tmp.sheaf.xif.paper.S2493bPermBarScalingActual
noncomputable section
set_option maxHeartbeats 8000000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2494Mod29HookupActual
open LeanFormal.IUT.XiFPaper.S2492Mod29FactorizationActual
open LeanFormal.IUT.XiFPaper.S2493UnitScalingActual
open LeanFormal.IUT.XiFPaper.S2493bPermBarScalingActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2141D5FactorizationFieldsActual
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
lemma S2494_mod29_scaled_factorDegrees (u : ZMod 29) (hu : u ≠ 0) :
    factorDegrees (C u * (S2132Psi5Z.map (Int.castRingHom (ZMod 29)))) =
      ({2, 10} : Multiset ℕ) := by
  rw [← S2141Product]
  rw [factorDegrees_C_mul_unit (S2141Factor2 * S2141Factor10)
    (mul_ne_zero S2491Factor2_irreducible.ne_zero S2491Factor10_irreducible.ne_zero) hu]
  rw [S2141Product]
  exact S2491FactorDegrees
#print axioms S2494_mod29_scaled_factorDegrees
end LeanFormal.IUT.XiFPaper.S2494Mod29HookupActual
end
