import tmp.sheaf.xif.paper.S2921HeightBridgeActual
import tmp.sheaf.xif.paper.S2751ExtendedAbsNormActual
import tmp.sheaf.xif.paper.S2735QPilotLineBundleActual
import tmp.sheaf.xif.paper.S2752FinalHweightvolActual
import tmp.sheaf.xif.paper.S2736QPilotLineBundleHweightvol
import tmp.sheaf.xif.paper.S2945CertificateActual

noncomputable section
open scoped nonZeroDivisors
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
open LeanFormal.IUT.XiFPaper.S2921HeightBridgeActual
open LeanFormal.IUT.XiFPaper.S2751ExtendedAbsNormActual
open LeanFormal.IUT.XiFPaper.S2735QPilotLineBundleActual
open LeanFormal.IUT.XiFPaper.S2752FinalHweightvolActual
open LeanFormal.IUT.XiFPaper.S2736QPilotLineBundleHweightvol
open LeanFormal.IUT.XiFPaper.S2945CertificateActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2967QDecomposition

/-- The q-pilot part of Q, as a Real constant. -/
noncomputable def S2967Qconst : Real :=
  Real.log ((5 * 5 * 2161 * 2161 : Nat) : Real)

theorem S2967Q_decomp (a b c : Nat) :
    S2921Q a b c =
      S2967Qconst +
        Real.log ((Ideal.absNorm (S2752J S2771FiveLabel a b c) : Nat) : Real) := by
  unfold S2921Q S2736QPilotLineBundleLogVolume S2967Qconst
  rw [show qPilotLineBundleExtended (l := S2771FiveLabel)
      (S2752J S2771FiveLabel a b c) =
      ((qPilotIdeal (l := S2771FiveLabel) *
        S2752J S2771FiveLabel a b c : Ideal
          (SourceOK (S2735Arithmetic S2771FiveLabel))) :
        FractionalIdeal (nonZeroDivisors (SourceOK (S2735Arithmetic S2771FiveLabel)))
          (S2735Arithmetic S2771FiveLabel).K) from rfl]
  rw [S2751_extended_absNorm]
  rw [show (qPilotIdeal (l := S2771FiveLabel) :
      FractionalIdeal (nonZeroDivisors (SourceOK (S2735Arithmetic S2771FiveLabel)))
        (S2735Arithmetic S2771FiveLabel).K) = qPilotLineBundle S2771FiveLabel from rfl]
  rw [qPilotFractional_absNorm]
  rw [FractionalIdeal.coeIdeal_absNorm]
  push_cast
  have hq : (116748025 : Real) ≠ 0 := by norm_num
  have hnum : (5 : Real) * 5 * 2161 * 2161 = 116748025 := by norm_num
  rw [hnum]
  have hJpos : 0 < Ideal.absNorm (S2752J S2771FiveLabel a b c) := by
    rw [Ideal.absNorm_pos_iff_mem_nonZeroDivisors]
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (S2945_supportIdeal_ne_bot a b c)
  have hJ : (((Ideal.absNorm (S2752J S2771FiveLabel a b c) : Nat) : Real)) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp hJpos
  exact Real.log_mul hq hJ

#check S2967Qconst
#check S2967Q_decomp

end LeanFormal.IUT.XiFPaper.S2967QDecomposition
end
