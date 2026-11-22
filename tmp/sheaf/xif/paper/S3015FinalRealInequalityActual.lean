import tmp.sheaf.xif.paper.S2936ThetaUpperConstantActual
import tmp.sheaf.xif.paper.S2945CertificateActual
import LeanFormal.IUT.IUTIV.Estimates.StepVProcessionAverage

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2936ThetaUpperConstantActual
open LeanFormal.IUT.XiFPaper.S2933PerTripleThetaCertificateActual
open LeanFormal.IUT.XiFPaper.S2945CertificateActual
open LeanFormal.IUT.XiFPaper.S2752FinalHweightvolActual
open LeanFormal.IUT.XiFPaper.S2739FinsetSupportActual
open LeanFormal.IUT.XiFPaper.S2921HeightBridgeActual
open LeanFormal.IUT.XiFPaper.S2736QPilotLineBundleHweightvol
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.XiFPaper.S2792NormalizedLineBundleBridge
open Finset
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S3015FinalRealInequalityActual

/-- Paper constants from the StepV/S2921 absorption calculation. -/
noncomputable def S3015Eps (n : Nat) : Real := S2936Eps n S2771FiveLabel.value

noncomputable def S3015AJ (n : Nat) : Real := S2936AJ n

/-- The final real bound in paper form: `6*(1+eps(n))*region + AJ(n)`. -/
noncomputable def S3015FinalBound (n : Nat) (a b c : Nat) : Real :=
  6 * (1 + S3015Eps n) * S2792RegionVolume a b c + S3015AJ n

/-- Nonnegativity of the actual S2921 support volume. -/
theorem S3015_S2921S_nonneg (a b c : Nat) : 0 <= S2921S a b c :=
  S2945_S2921S_nonneg a b c

/-- Nonnegativity of the actual S2921 T candidate. -/
theorem S3015_S2921T_nonneg (a b c : Nat) : 0 <= S2921T a b c :=
  S2945_T_nonneg a b c

/-- **Final real inequality (paper constants).**  Input is exactly the StepV
height-to-procession bound; no ABC certificate and no `hadd` are introduced.
All constants are the actual S2921/StepV absorption constants. -/
theorem S3015_final_real_inequality
    (n : Nat) (hn : 2 <= n)
    (hheight : forall a b c : Nat, IsABCTriple a b c ->
      Height.logHeight₁ (abcJInvariant a b c) <=
        (1 / (n : Real)) *
          ∑ j ∈ Icc 1 n,
            LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionBound
              (2 * (n : Real) + 1) S2921D (S2921Q a b c)
              (S2921S a b c) (S2921T a b c) j)
    (a b c : Nat) (habc : IsABCTriple a b c) :
    Height.logHeight₁ (abcJInvariant a b c) <=
      S3015FinalBound n a b c :=
by
  have hD : 0 <= S2921D := S2921D_nonneg
  have hS : 0 <= S2921S a b c := S3015_S2921S_nonneg a b c
  have hT : 0 <= S2921T a b c := S3015_S2921T_nonneg a b c
  have h1 := hheight a b c habc
  have h2 := LeanFormal.IUT.IUTIV.StepVProcessionAverage.processionAverage_le
    n hn S2921D (S2921Q a b c) (S2921S a b c) (S2921T a b c) hD hS hT
  have h3 := S2936_thetaUpper_constant_bound_unconditional n hn a b c habc
  have h3' : S2933ThetaUpper n a b c <= S3015FinalBound n a b c := by
    unfold S3015FinalBound S3015Eps S3015AJ
    exact h3
  exact le_trans h1 (le_trans h2 h3')

#check S3015Eps
#check S3015AJ
#check S3015FinalBound
#check S3015_final_real_inequality
#print axioms S3015_final_real_inequality

end LeanFormal.IUT.XiFPaper.S3015FinalRealInequalityActual
end
