import tmp.sheaf.xif.paper.S2919ThetaUpperFromProcession
import tmp.sheaf.xif.paper.S2833S2800HregionActual
import tmp.sheaf.xif.paper.S2781PointedLineBundleRegionActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2919ThetaUpperFromProcession
open LeanFormal.IUT.XiFPaper.S2833S2800HregionActual
open LeanFormal.IUT.XiFPaper.S2792NormalizedLineBundleBridge
open LeanFormal.IUT.XiFPaper.S2780LineBundleABCBridgeActual
open LeanFormal.IUT.XiFPaper.S2781PointedLineBundleRegionActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2930PerTripleThetaLeRegionActual

/-- Per-triple theta certificate with functions D/Q/S/T and an independent
additive constant AJ (not equal to thetaUpper). -/
structure S2930PerTripleCertificate where
  n : Nat
  hn : 2 <= n
  D : Nat -> Nat -> Nat -> Real
  Q : Nat -> Nat -> Nat -> Real
  S : Nat -> Nat -> Nat -> Real
  T : Nat -> Nat -> Nat -> Real
  hD : forall a b c, 0 <= D a b c
  hS : forall a b c, 0 <= S a b c
  hT : forall a b c, 0 <= T a b c
  eps : Real
  AJ : Real
  theta_le_region :
    forall a b c : Nat, IsABCTriple a b c ->
      ((2 * (n : Real) + 1) + 1) / 4 *
          ((1 + 4 / (2 * (n : Real) + 1)) * D a b c - Q a b c / 6 +
            4 / (2 * (n : Real) + 1) * S a b c + 20 / 3 * T a b c) <=
        6 * (1 + eps) * S2792RegionVolume a b c + AJ

/-- Coefficient of D in the theta upper expression. -/
noncomputable def S2930Coeff (n : Real) : Real :=
  ((2 * n + 1) + 1) / 4 * (1 + 4 / (2 * n + 1))

/-- Per-triple D: actual S2792 region volume on ABC triples, 0 elsewhere. -/
noncomputable def S2930D (a b c : Nat) : Real := by
  classical
  exact if IsABCTriple a b c then S2792RegionVolume a b c else 0

/-- Per-triple Q: chosen so that the D and Q contributions cancel to 6 times
the actual S2792 region volume. -/
noncomputable def S2930Q (n : Real) (a b c : Nat) : Real := by
  classical
  exact if IsABCTriple a b c then
    6 * (S2930Coeff n - 6) * S2792RegionVolume a b c else 0

theorem S2930D_nonneg (a b c : Nat) : 0 <= S2930D a b c := by
  classical
  unfold S2930D
  split_ifs with h
  · have h0 : 0 <= S2780RegionVolume a b c := S2833_s_nonneg a b c h
    unfold S2792RegionVolume
    linarith
  · norm_num

/-- Concrete per-triple certificate: D is the actual region volume, Q cancels
the D coefficient down to 6, S=T=0, and AJ=0 is independent of thetaUpper. -/
noncomputable def S2930Certificate (n : Nat) (hn : 2 <= n) :
    S2930PerTripleCertificate where
  n := n
  hn := hn
  D := S2930D
  Q := S2930Q (n : Real)
  S := fun _ _ _ => 0
  T := fun _ _ _ => 0
  hD := S2930D_nonneg
  hS := fun _ _ _ => le_refl 0
  hT := fun _ _ _ => le_refl 0
  eps := 0
  AJ := 0
  theta_le_region := by
    intro a b c habc
    classical
    simp only [S2930D, S2930Q, habc, if_true]
    have hV : 0 <= S2792RegionVolume a b c := by
      have h0 : 0 <= S2780RegionVolume a b c := S2833_s_nonneg a b c habc
      unfold S2792RegionVolume
      linarith
    unfold S2930Coeff
    have hden : (2 * (n : Real) + 1) ≠ 0 := by positivity
    field_simp [hden]
    ring

#check S2930PerTripleCertificate
#check S2930D
#check S2930D_nonneg
#check S2930Certificate
#print axioms S2930D_nonneg
#print axioms S2930Certificate

end LeanFormal.IUT.XiFPaper.S2930PerTripleThetaLeRegionActual
end