import Mathlib.Tactic

/-! # GenEllThm38EffectiveBoundsActual — Thm 3.8 effective-bound statement shapes (class A/B)

STEP 0 prior-art: GenEll corpus Thm 3.8 (1145-1166), Lemma 3.7 (1052-1144),
Prop 3.4 (994-1010); Mathlib.NumberTheory.Height.Basic/Projectivization (logHeight API,
importable); ported FLT/TauCeti assets (RR/Serde/curve/divisor) pending compilation;
GenEll06Section3StatementsActual rows (statement ledger).

LABEL: class-A constant arithmetic + class-B condition shapes; no proof of the
analytic/Faltings-height inputs. -/

namespace LeanFormal.IUT.XiFPaper.GenEllThm38EffectiveBoundsActual

/-- 23040 = (3^2-1)(3^2-3)(5^2-1)(5^2-5) = |GL2(F_3) x GL2(F_5)|. -/
theorem genEll_23040_eq : (3 ^ 2 - 1) * (3 ^ 2 - 3) * (5 ^ 2 - 1) * (5 ^ 2 - 5) = 23040 := by
  norm_num

/-- The Thm 3.8 (a) lower bound shape for the prime l. -/
noncomputable def thm38BoundA (l d htFalt C eps : ℝ) : Prop :=
  l ≥ 23040 * 100 * d * (htFalt + C * d ^ eps)

/-- The Thm 3.8 (b) hypothesis shape (K_V membership and coprimality data as parameters). -/
noncomputable def thm38BoundB (memberKV primeToLocalHeights primeTo30 : Prop) : Prop :=
  memberKV ∧ primeToLocalHeights ∧ primeTo30

/-- The Cor 4.3/4.4 upper bound shapes with the paper's constants. -/
noncomputable def cor43BoundLo (l0 d htFalt xS C eps : ℝ) : Prop :=
  l0 ≤ 23040 * 900 * d * htFalt + 2 * xS + C * d ^ (1 + eps)

noncomputable def cor43BoundHi (l1 d htFalt logDiff xS C eps : ℝ) : Prop :=
  l1 ≤ 23040 * 900 * d * htFalt + 6 * d * logDiff + 2 * xS + C * d ^ (1 + eps)

noncomputable def cor44BoundLo (l0 d htFalt xS C : ℝ) : Prop :=
  l0 ≤ 23040 * 100 * d * htFalt + 2 * xS + C * d

noncomputable def cor44BoundHi (l1 d htFalt logDiff xS C : ℝ) : Prop :=
  l1 ≤ 23040 * 100 * d * htFalt + 6 * d * logDiff + 2 * xS + C * d

/-- The list of effective-bound condition shapes (data). -/
def genEllEffectiveBoundShapes : List (String × String) :=
  [ ("Thm 3.8 (a)", "l >= 23040 * 100d * (ht_Falt([E_L]) + C d^eps) and E_L has a prime of potentially multiplicative reduction"),
    ("Thm 3.8 (b)", "[E_L] in K_V, l prime to local heights of potentially multiplicative reduction and to 2*3*5"),
    ("Cor 4.3 (c)", "l_o <= 23040*900d*ht_Falt + 2x_S + C d^(1+eps); l_b <= 23040*900d*ht_Falt + 6d*log-diff + 2x_S + C d^(1+eps)"),
    ("Cor 4.4 (c)", "l_o <= 23040*100d*ht_Falt + 2x_S + C d; l_b <= 23040*100d*ht_Falt + 6d*log-diff + 2x_S + C d"),
    ("physical-layer assets", "Mathlib.NumberTheory.Height.logHeight/mulHeight + Northcott; ported FLT/TauCeti RR/Serde/curve layers (pending compile)"),
    ("remaining paper input", "Faltings height ht_Falt and Prop 3.4 comparison chain deg_inf ~ ht_inf ~ 12(1+eps)ht_Falt ~ (1+eps)ht_inf [Silv2]; Serre large-image [Serre]") ]

theorem genEllEffectiveBoundShapes_length : genEllEffectiveBoundShapes.length = 6 := rfl

#check genEll_23040_eq
#check genEllEffectiveBoundShapes_length

end LeanFormal.IUT.XiFPaper.GenEllThm38EffectiveBoundsActual