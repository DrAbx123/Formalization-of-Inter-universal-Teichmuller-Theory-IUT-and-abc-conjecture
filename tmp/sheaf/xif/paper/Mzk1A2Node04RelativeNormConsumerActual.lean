/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A2Node04RelativeNormInterfaceActual
import Mathlib.Tactic

/-! # A2 node04 §7.1: relative norm consumer -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1A2Node04RelativeNormConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1A2Node04RelativeNormInterfaceActual

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [NormedField K] [NormedField L]

def A2Node04RelativeNormInterface.relativeNorm'
    (D : A2Node04RelativeNormInterface K L) : L →* K :=
  D.relativeNorm

theorem A2Node04RelativeNormInterface.relativeNorm_norm_formula
    (D : A2Node04RelativeNormInterface K L) (x : L) :
    ‖A2Node04RelativeNormInterface.relativeNorm' D x‖ =
      ‖x‖ ^ Module.finrank K L :=
  D.norm_formula x

theorem A2Node04RelativeNormInterface.relativeNorm_q_contraction
    (D : A2Node04RelativeNormInterface K L) (q : K) (hq : ‖q‖ < 1) :
    ‖A2Node04RelativeNormInterface.relativeNorm' D (algebraMap K L q)‖ < 1 :=
  D.q_contraction q hq

end LeanFormal.IUT.XiFPaper.Mzk1A2Node04RelativeNormConsumerActual
