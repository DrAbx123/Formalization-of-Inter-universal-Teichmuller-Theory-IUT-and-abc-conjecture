import Mathlib

noncomputable section
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2551Probe

abbrev G : (ZMod 13)[X] :=
  C 5 + C 0 * X + C 11 * X ^ 2 + C 5 * X ^ 3 + C 2 * X ^ 4 + C 5 * X ^ 5 +
    C 0 * X ^ 6 + C 2 * X ^ 7 + C 8 * X ^ 8 + C 5 * X ^ 9 + C 10 * X ^ 10 +
    C 3 * X ^ 11 + C 1 * X ^ 12

abbrev T1 : (ZMod 13)[X] :=
  C 2 + C 8 * X + C 7 * X ^ 2 + C 4 * X ^ 3 + C 1 * X ^ 4 + C 0 * X ^ 5 +
    C 8 * X ^ 6 + C 6 * X ^ 7 + C 9 * X ^ 8 + C 7 * X ^ 9 + C 12 * X ^ 10 + C 12 * X ^ 11

example : ((X : (ZMod 13)[X]) ^ 13) %ₘ G = T1 := by
  decide

end LeanFormal.IUT.XiFPaper.S2551Probe
end
