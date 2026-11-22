import tmp.sheaf.xif.paper.S2853ChartYNegationActual
import Mathlib.Tactic

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2853ChartYNegationActual
set_option maxHeartbeats 8000000
namespace LeanFormal.IUT.XiFPaper.S2855g0script
variable (K : Type) [Field K]

example : S2853G0Poly K (E37ChartYPolynomial K) = 0 := by
  have hpoly : algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)
      ((S2853ChartYS K)^3 - S2853ChartYS K * (S2853ChartYT K)^2 -
        S2853ChartYT K - (S2853ChartYT K)^2) =
      -((algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYS K)) *
          (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYT K))^2)
        + (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYS K))^3
        - algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYT K)
        - (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYT K))^2 := by
    simp only [map_sub, map_mul, map_pow]
    ring_nf
  have hmain : -((algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYS K)) *
          (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYT K))^2)
        + (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYS K))^3
        - algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYT K)
        - (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYT K))^2 = 0 := by
    rw [hpoly.symm, S2853_hrel]
  simp only [S2853G0Poly, S2853G0Vals, S2853ChartYNegS, S2853ChartYNegT,
    E37ChartYPolynomial, map_add, map_mul, map_pow, map_sub]
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
  have h0 : S2853G0Vals K (0 : Fin 2) = S2853ChartYNegS K := rfl
  have h1 : S2853G0Vals K (1 : Fin 2) = S2853ChartYNegT K := rfl
  rw [h0, h1]
  let u : S2853ChartYNegRing K := ↑(S2853ChartYNegUnit K)
  have hu : IsUnit u := ⟨S2853ChartYNegUnit K, rfl⟩
  apply (IsUnit.mul_left_inj (hu.pow 3)).mp
  rw [← hmain]
  simp only [S2853ChartYNegS, S2853ChartYNegT, u]
  simp only [Units.val_inv_eq_inv_val]
  ring_nf
  field_simp

end LeanFormal.IUT.XiFPaper.S2855g0script
end
