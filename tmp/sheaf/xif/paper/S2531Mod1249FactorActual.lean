import tmp.sheaf.xif.paper.S2550TwoFactorCertificateActual
import tmp.sheaf.xif.paper.S2599IrreducibleF10Actual
import tmp.sheaf.xif.paper.S2132D5FactorizationActual
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
local instance : Fact (Nat.Prime 1249) := ⟨by norm_num⟩
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2531Mod1249FactorActual
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
def S2531Mod1249FactorDegrees : Prop :=
  ∃ (g2 g10 : (ZMod 1249)[X]),
    Irreducible g2 ∧ Irreducible g10 ∧
      g2.natDegree = 2 ∧ g10.natDegree = 10 ∧
      g2 * g10 = S2132Psi5Z.map (Int.castRingHom (ZMod 1249))
lemma g2_irreducible : Irreducible (C (415 : ZMod 1249) * S2550F2) := by
  have h415 : IsUnit (C (415 : ZMod 1249)) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by decide))
  have hassoc : Associated (C (415 : ZMod 1249) * S2550F2) S2550F2 :=
    associated_unit_mul_left S2550F2 (C (415 : ZMod 1249)) h415
  exact hassoc.symm.irreducible S2550F2_irreducible
lemma g2_natDegree : (C (415 : ZMod 1249) * S2550F2).natDegree = 2 := by
  unfold S2550F2
  compute_degree!
lemma g10_irreducible : Irreducible S2550F10 := by
  convert LeanFormal.IUT.XiFPaper.S2599IrreducibleF10Actual.irreducible_F10 using 2
lemma g10_natDegree : S2550F10.natDegree = 10 := by
  unfold S2550F10
  compute_degree!
lemma gprod : (C (415 : ZMod 1249) * S2550F2) * S2550F10 =
    S2132Psi5Z.map (Int.castRingHom (ZMod 1249)) := by
  rw [mul_assoc, ← S2550Product, S2550Psi5Mod1249_eq]
theorem S2531Mod1249FactorDegrees_actual : S2531Mod1249FactorDegrees :=
  ⟨C (415 : ZMod 1249) * S2550F2, S2550F10,
    g2_irreducible, g10_irreducible, g2_natDegree, g10_natDegree, gprod⟩
#print axioms S2531Mod1249FactorDegrees_actual
end LeanFormal.IUT.XiFPaper.S2531Mod1249FactorActual
end
