import tmp.sheaf.xif.paper.S2919ThetaUpperFromProcession
import tmp.sheaf.xif.paper.S2833S2800HregionActual
import tmp.sheaf.xif.paper.S2781PointedLineBundleRegionActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2919ThetaUpperFromProcession
open LeanFormal.IUT.XiFPaper.S2833S2800HregionActual
open LeanFormal.IUT.XiFPaper.S2792NormalizedLineBundleBridge
open LeanFormal.IUT.XiFPaper.S2781PointedLineBundleRegionActual
open Finset
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2921ThetaLeRegionActual

/-- Theta upper expression for the certificate, written explicitly so that it
can also be used as the additive constant AJ. -/
noncomputable def S2921ThetaUpper (n D Q S T : Real) : Real :=
  ((2 * n + 1) + 1) / 4 *
    ((1 + 4 / (2 * n + 1)) * D - Q / 6 +
      4 / (2 * n + 1) * S + 20 / 3 * T)

/-- General volume-nonneg form: with AJ equal to the theta upper expression,
theta_le_region follows from nonnegativity of the region term. -/
theorem S2921_theta_le_region_of_nonneg
    (n D Q S T eps : Real)
    (heps : 0 <= 1 + eps)
    (a b c : Nat) (habc : IsABCTriple a b c) :
    S2921ThetaUpper n D Q S T <=
      6 * (1 + eps) * S2792RegionVolume a b c +
        S2921ThetaUpper n D Q S T := by
  have hV : 0 <= S2792RegionVolume a b c := by
    have h := S2833_s_nonneg a b c habc
    unfold S2792NormalizedLineBundleBridge.S2792RegionVolume
    linarith
  have hterm : 0 <= 6 * (1 + eps) * S2792RegionVolume a b c :=
    mul_nonneg (mul_nonneg (by norm_num) heps) hV
  linarith

/-- Build a ThetaUpperCertificate with AJ := thetaUpper, so the region lemma is
proved from S2833 nonnegativity and the supplied height estimate. -/
noncomputable def S2921Certificate
    (n : Nat) (hn : 2 <= n)
    (D Q S T : Real) (hD : 0 <= D) (hS : 0 <= S) (hT : 0 <= T)
    (eps : Real) (heps : 0 <= 1 + eps)
    (height_le_procession :
      forall a b c : Nat, IsABCTriple a b c ->
        Height.logHeight₁ (abcJInvariant a b c) <=
          (1 / (n : Real)) *
            Finset.sum (Icc 1 n)
              (fun j => collectionBound (2 * (n : Real) + 1) D Q S T j)) :
    ThetaUpperCertificate where
  n := n
  hn := hn
  D := D
  Q := Q
  S := S
  T := T
  hD := hD
  hS := hS
  hT := hT
  eps := eps
  AJ := S2921ThetaUpper n D Q S T
  height_le_procession := height_le_procession
  theta_le_region := by
    intro a b c habc
    exact S2921_theta_le_region_of_nonneg n D Q S T eps heps a b c habc

theorem S2921_certificate_theta_le_region
    (C : ThetaUpperCertificate)
    (hAJ : C.thetaUpper <= C.AJ)
    (heps : 0 <= 1 + C.eps)
    (a b c : Nat) (habc : IsABCTriple a b c) :
    C.thetaUpper <=
      6 * (1 + C.eps) * S2792RegionVolume a b c + C.AJ := by
  have hV : 0 <= S2792RegionVolume a b c := by
    have h := S2833_s_nonneg a b c habc
    unfold S2792NormalizedLineBundleBridge.S2792RegionVolume
    linarith
  have hterm : 0 <= 6 * (1 + C.eps) * S2792RegionVolume a b c :=
    mul_nonneg (mul_nonneg (by norm_num) heps) hV
  linarith

#check S2921ThetaUpper
#check S2921_theta_le_region_of_nonneg
#check S2921Certificate
#check S2921_certificate_theta_le_region
#print axioms S2921_theta_le_region_of_nonneg
#print axioms S2921Certificate

end LeanFormal.IUT.XiFPaper.S2921ThetaLeRegionActual
end