import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# A578 1D strictness tools (shehdd, for hull's product strictness)

Safe wrappers of Mathlib's one-dimensional strict/monotone log and exp facts,
used when proving product-wise strictness from one strictly increasing factor.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1OneDimStrictnessShaActual

theorem log_strict {a b : Real} (ha : 0 < a) (h : a < b) :
    Real.log a < Real.log b :=
  Real.log_lt_log ha h

theorem log_mono {a b : Real} (ha : 0 < a) (h : a ≤ b) :
    Real.log a ≤ Real.log b :=
  Real.log_le_log ha h

theorem log_strict_of_one_lt {a b : Real} (ha : 1 < a) (h : a < b) :
    Real.log a < Real.log b :=
  Real.log_lt_log (lt_trans zero_lt_one ha) h

theorem exp_strict {a b : Real} (h : a < b) : Real.exp a < Real.exp b :=
  Real.exp_lt_exp.mpr h

theorem exp_mono {a b : Real} (h : a ≤ b) : Real.exp a ≤ Real.exp b :=
  Real.exp_le_exp.mpr h

/-- If two positive factors satisfy `f a < g a` then the ratio is `> 1`, the
1D seed for product-wise strictness. -/
theorem one_lt_ratio {a f g : Real} (ha : 0 < a) (hfg : f < g) (hf : 0 < f) :
    1 < g / f := by
  rw [lt_div_iff₀ hf]
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1OneDimStrictnessShaActual
