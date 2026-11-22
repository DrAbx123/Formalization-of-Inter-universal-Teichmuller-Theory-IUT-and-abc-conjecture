import tmp.sheaf.xif.paper.S2550TwoFactorCertificateActual
import tmp.sheaf.xif.paper.S2599IrreducibleF10Actual
import tmp.sheaf.xif.paper.S2531ResidueCertificateActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2531Mod1249FactorDegreesActual

open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2531ResidueCertificateActual

abbrev F2 : (ZMod 1249)[X] := S2550F2
abbrev F10 : (ZMod 1249)[X] := S2550F10
abbrev Psi : (ZMod 1249)[X] := S2550Psi5Mod1249

lemma F2_monic : F2.Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one 2
  · unfold F2 S2550F2; compute_degree!
  · simp [F2, S2550F2]

lemma F10_monic : F10.Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one 10
  · unfold F10 S2550F10; compute_degree!
  · simp [F10, S2550F10]

lemma F2_degree : F2.natDegree = 2 := by unfold F2 S2550F2; compute_degree!
lemma F10_degree : F10.natDegree = 10 := by unfold F10 S2550F10; compute_degree!

def mod1249FactorData : S2531FactorizationData (ZMod 1249) Psi where
  c := 415
  c_ne_zero := by decide
  g2 := F2
  g10 := F10
  product_eq := S2550Product
  g2_monic := F2_monic
  g10_monic := F10_monic
  g2_irreducible := S2550F2_irreducible
  g10_irreducible := LeanFormal.IUT.XiFPaper.S2599IrreducibleF10Actual.irreducible_F10
  g2_degree := F2_degree
  g10_degree := F10_degree

theorem S2531Mod1249FactorDegrees :
    factorDegrees (S2132Psi5Z.map (Int.castRingHom (ZMod 1249))) = ({2, 10} : Multiset Nat) := by
  rw [← S2550Psi5Mod1249_eq]
  exact S2531factorDegrees_of_factorization (ZMod 1249) Psi mod1249FactorData

lemma C415_unit : IsUnit (C (415 : ZMod 1249)) := by
  rw [isUnit_C]
  exact isUnit_iff_ne_zero.mpr (by decide)

lemma g2_scaled_irreducible : Irreducible (C (415 : ZMod 1249) * F2) := by
  exact (associated_unit_mul_left F2 (C (415 : ZMod 1249)) C415_unit).symm.irreducible S2550F2_irreducible

theorem S2531Mod1249ProductForm :
    (C (415 : ZMod 1249) * F2) * F10 = S2132Psi5Z.map (Int.castRingHom (ZMod 1249)) := by
  rw [← S2550Psi5Mod1249_eq, ← S2550Product]
  ring

end LeanFormal.IUT.XiFPaper.S2531Mod1249FactorDegreesActual

end