import tmp.sheaf.xif.paper.S2933PerTripleThetaCertificateActual
import tmp.sheaf.xif.paper.S2921HeightBridgeActual
import tmp.sheaf.xif.paper.S2937AbsNormJLeQPilotActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2933PerTripleThetaCertificateActual
open LeanFormal.IUT.XiFPaper.S2921HeightBridgeActual
open LeanFormal.IUT.XiFPaper.S2792NormalizedLineBundleBridge
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.XiFPaper.S2937AbsNormJLeQPilotActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2936ThetaUpperConstantActual

noncomputable def S2936C (n : Nat) (l : Nat) : Real :=
  4 / (2 * (n : Real) + 1) + 20 * (l : Real) / 3 - 1 / 6

noncomputable def S2936A (n : Nat) : Real :=
  ((2 * (n : Real) + 1) + 1) / 4

noncomputable def S2936B (n : Nat) : Real :=
  1 + 4 / (2 * (n : Real) + 1)

noncomputable def S2936AJ (n : Nat) : Real :=
  S2936A n * S2936B n * S2921D

noncomputable def S2936Eps (n : Nat) (l : Nat) : Real :=
  S2936A n * S2936C n l / 3 - 1

/-- Absorb S and T into Q: using `S ≤ Q` and `T = l*S`, the theta upper
expression is at most `A(n)*(B(n)*D + C(n,l)*Q)`. -/
theorem S2936_thetaUpper_absorb
    (n : Nat) (hn : 2 <= n)
    (hSQ : forall a b c : Nat, IsABCTriple a b c ->
      S2921S a b c <= S2921Q a b c)
    (a b c : Nat) (habc : IsABCTriple a b c) :
    S2933ThetaUpper n a b c <=
      S2936A n *
        (S2936B n * S2921D + S2936C n S2771FiveLabel.value * S2921Q a b c) := by
  have hS := hSQ a b c habc
  have hl : (0 : Real) <= (S2771FiveLabel.value : Real) := by exact_mod_cast Nat.zero_le _
  have hA : 0 <= S2936A n := by
    unfold S2936A; positivity
  have hcoef : 0 <= 4 / (2 * (n : Real) + 1) := by positivity
  have hS1 : S2936A n * (4 / (2 * (n : Real) + 1) * S2921S a b c) <=
      S2936A n * (4 / (2 * (n : Real) + 1) * S2921Q a b c) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hS hcoef) hA
  have hTS : S2921T a b c =
      (S2771FiveLabel.value : Real) * S2921S a b c := rfl
  have h20 : 20 / 3 * S2921T a b c <=
      20 / 3 * ((S2771FiveLabel.value : Real) * S2921Q a b c) := by
    rw [hTS]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hS hl) (by norm_num)
  have hT1 : S2936A n * (20 / 3 * S2921T a b c) <=
      S2936A n * (20 / 3 * ((S2771FiveLabel.value : Real) * S2921Q a b c)) :=
    mul_le_mul_of_nonneg_left h20 hA
  calc
    S2933ThetaUpper n a b c =
        S2936A n * (S2936B n * S2921D - S2921Q a b c / 6 +
          4 / (2 * (n : Real) + 1) * S2921S a b c + 20 / 3 * S2921T a b c) := rfl
    _ <= S2936A n * (S2936B n * S2921D - S2921Q a b c / 6 +
          4 / (2 * (n : Real) + 1) * S2921Q a b c +
          20 / 3 * ((S2771FiveLabel.value : Real) * S2921Q a b c)) := by
      nlinarith [hS1, hT1]
    _ = S2936A n *
        (S2936B n * S2921D + S2936C n S2771FiveLabel.value * S2921Q a b c) := by
      unfold S2936C; ring

/-- Convert `Q = 2 * S2792RegionVolume` to the standard region form with
the computed constants `C(n,l)` and `AJ(n)`. -/
theorem S2936_region_form
    (n : Nat) (a b c : Nat) :
    S2936A n * (S2936B n * S2921D +
        S2936C n S2771FiveLabel.value * S2921Q a b c) =
      6 * (1 + S2936Eps n S2771FiveLabel.value) *
          S2792RegionVolume a b c + S2936AJ n := by
  have hQ2 : S2921Q a b c = 2 * S2792RegionVolume a b c := by
    rw [S2921Q_eq_regionVolume]
    unfold S2792RegionVolume
    ring
  rw [hQ2]
  simp only [S2936A, S2936B, S2936C, S2936AJ, S2936Eps]
  ring_nf

/-- Constant computation: with `S2921S ≤ S2921Q`, the S/T terms of
`S2933ThetaUpper` absorb into `C(n,l)` and `AJ(n)`. -/
theorem S2936_thetaUpper_constant_bound
    (n : Nat) (hn : 2 <= n)
    (hSQ : forall a b c : Nat, IsABCTriple a b c ->
      S2921S a b c <= S2921Q a b c)
    (a b c : Nat) (habc : IsABCTriple a b c) :
    S2933ThetaUpper n a b c <=
      6 * (1 + S2936Eps n S2771FiveLabel.value) *
          S2792RegionVolume a b c + S2936AJ n := by
  refine le_trans (S2936_thetaUpper_absorb n hn hSQ a b c habc) ?_
  rw [S2936_region_form]

#check S2936C
#check S2936AJ
#check S2936Eps
#check S2936_thetaUpper_absorb
#check S2936_region_form
theorem S2936_thetaUpper_constant_bound_unconditional
    (n : Nat) (hn : 2 <= n)
    (a b c : Nat) (habc : IsABCTriple a b c) :
    S2933ThetaUpper n a b c <=
      6 * (1 + S2936Eps n S2771FiveLabel.value) *
          S2792RegionVolume a b c + S2936AJ n :=
  S2936_thetaUpper_constant_bound n hn
    (fun a b c habc => S2937_S2921S_le_S2921Q a b c habc) a b c habc

#check S2936_thetaUpper_constant_bound
#check S2936_thetaUpper_constant_bound_unconditional
#print axioms S2936_thetaUpper_constant_bound

end LeanFormal.IUT.XiFPaper.S2936ThetaUpperConstantActual
end
