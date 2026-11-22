import tmp.sheaf.xif.paper.S2550TwoFactorCertificateActual

noncomputable section
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual

namespace LeanFormal.IUT.XiFPaper.S2569Batch10ActualAdapted

def R2 : (ZMod 1249)[X] := 871 + X * 629 + X ^ 2 * 1077 + X ^ 3 * 1032 + X ^ 4 * 142 + X ^ 5 * 643 + X ^ 6 * 946 + X ^ 7 * 1025 + X ^ 8 * 796 + X ^ 9 * 1154
def R5 : (ZMod 1249)[X] := 1194 + X * 810 + X ^ 2 * 856 + X ^ 3 * 203 + X ^ 4 * 881 + X ^ 5 * 314 + X ^ 6 * 738 + X ^ 7 * 1237 + X ^ 8 * 176 + X ^ 9 * 1189
def A2 : (ZMod 1249)[X] := 674 + X * 1117 + X ^ 2 * 222 + X ^ 3 * 503 + X ^ 4 * 799 + X ^ 5 * 642 + X ^ 6 * 379 + X ^ 7 * 271 + X ^ 8 * 440
def B2 : (ZMod 1249)[X] := 1130 + X * 94 + X ^ 2 * 731 + X ^ 3 * 910 + X ^ 4 * 431 + X ^ 5 * 498 + X ^ 6 * 677 + X ^ 7 * 780 + X ^ 8 * 275 + X ^ 9 * 662
def A5 : (ZMod 1249)[X] := 1015 + X * 207 + X ^ 2 * 907 + X ^ 3 * 672 + X ^ 4 * 428 + X ^ 5 * 518 + X ^ 6 * 1107 + X ^ 7 * 1199 + X ^ 8 * 1182
def B5 : (ZMod 1249)[X] := 916 + X * 757 + X ^ 2 * 62 + X ^ 3 * 823 + X ^ 4 * 924 + X ^ 5 * 760 + X ^ 6 * 650 + X ^ 7 * 1050 + X ^ 8 * 403 + X ^ 9 * 894

theorem bezout2 : A2 * S2550F10 + B2 * (R2 - X) = 1 := by
  unfold A2 B2 R2 S2550F10
  ring

theorem bezout5 : A5 * S2550F10 + B5 * (R5 - X) = 1 := by
  unfold A5 B5 R5 S2550F10
  ring

theorem R10_eq_X : (-1248 : (ZMod 1249)[X]) * X = X := by
  change C (-1248 : ZMod 1249) * X = X
  have h : (-1248 : ZMod 1249) = 1 := by decide
  rw [h, C_1, one_mul]

end LeanFormal.IUT.XiFPaper.S2569Batch10ActualAdapted

end
