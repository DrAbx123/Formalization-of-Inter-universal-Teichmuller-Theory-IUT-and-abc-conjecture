/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ResiduePowerInstanceActual
import tmp.sheaf.xif.paper.Mzk1ArchTorsionDictionaryActual
import Mathlib.Tactic

/-! # B10 (abc scope): q normalization and global Sum/index dictionary -/

/- Two consistent normalizations of the q-side magnitude:
* LANA/our A := absLogQ = logQ/(2l), with logQ = sum_v (f_v/[F:Q])*ord_v(q_v)*log p_v
  (lana `Cor312/LeftHandSide.lean:81-88`);
* UNNORMALIZED A' := logQ.  The SSIneq LHS is
  `(sFactor(nC)-1)*A = c_lana*A'` with `c_lana = (sFactor(nC)-1)/(2l)` (proved below).
So a candidate counterexample that plugs A = log q directly is off by the factor `2l`.

Global Sum/index dictionary (green):
* `logShellIntegerIndex_eq_card_div_torsion` (IndexArithmetic:100):
  index = card(units/congruence)/card(torsion units);
* `logShellResidueCard_eq_prime_pow` (SharpBounds:1014): residueCard = p^f, f >= 1;
* under the residue-power cardinal hypothesis, `log index = a*f*log p`
  (`Mzk1ResiduePowerInstanceActual.log_index_eq_mul_mul_log`);
* arch/torsion dictionary (hull `Mzk1ArchTorsionDictionaryActual`):
  archConstant = log(sqrt 2 * pi) = log2/2 + log pi, torsionTerm = r/n,
  diffTerm = -order*logp - r/n + arch, with torsion <= 1 giving
  diffTerm >= -order*logp - 1 + arch.

Sign-aligned deficit (A800): deficit = (ssCoeff - cLana)*A + order*logp + arch - torsion
(arch/torsion cancel against the dictionary definitions).

STRENGTH: this dictionary is for OUR/paper-normalized model; it is not lana SSIneq and
not ABC.  No equivalence with Szpiro-6 is asserted. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1QNormalizationDictionaryActual

open LeanFormal.IUT.XiFPaper.Mzk1ArchTorsionDictionaryActual

def absLogQFromLogQ (logQ l : ℝ) : ℝ := logQ / (2 * l)

def cLana (sFactor l : ℝ) : ℝ := (sFactor - 1) / (2 * l)

/-- **Normalization equivalence**: `(sFactor-1)*absLogQ = c_lana*logQ`. -/
theorem normalization_equiv (sFactor logQ l : ℝ) (hl : l ≠ 0) :
    (sFactor - 1) * absLogQFromLogQ logQ l = cLana sFactor l * logQ := by
  unfold absLogQFromLogQ cLana
  have h2l : (2 : ℝ) * l ≠ 0 := mul_ne_zero (by norm_num) hl
  field_simp [h2l]

/-- The two deficit conventions coincide under the normalization equivalence. -/
theorem deficit_normalization_equiv (sFactor A' sumLogMu sumTheta l : ℝ) (hl : l ≠ 0) :
    sFactor * absLogQFromLogQ A' l - (sumLogMu + sumTheta) =
      sFactor * (A' / (2 * l)) - (sumLogMu + sumTheta) := by
  rfl

/-- torsion term is nonnegative for `0 <= r`, `0 < n`. -/
theorem torsion_nonneg {r n : ℝ} (hr : 0 ≤ r) (hn : 0 < n) : 0 ≤ torsionTerm r n := by
  unfold torsionTerm
  positivity

/-- Dictionary rows: (item, assertion, tag). -/
def qNormalizationRows : List (String × String × String) :=
  [ ("q magnitude A", "A = absLogQ = logQ/(2l)", "DEF (lana LeftHandSide:88)") ,
    ("unnormalized A'", "ssCoeff*A = c_lana*A', c_lana=(sFactor-1)/(2l)", "PROVED normalization_equiv") ,
    ("global index", "index = card(units/congruence)/card(torsion)", "GREEN IndexArithmetic:100") ,
    ("residue card", "residueCard = p^f, f>=1", "GREEN SharpBounds:1014") ,
    ("log index", "log index = a*f*log p under residue-power hypothesis", "PROVED log_index_eq_mul_mul_log") ,
    ("arch", "archConstant = log2/2 + log pi", "PROVED arch_decomposition") ,
    ("torsion", "torsionTerm = r/n, >=0 for r>=0<n", "PROVED torsion_nonneg") ,
    ("def", "deficit = (ssCoeff-cLana)A + order*logp + arch - torsion", "PROVED A800 deficit_sign_aligned") ,
    ("stage4 q=22 check", "A = logQ/(2l) not logQ; q=22 bad support {2,11}", "CORRECTION noted") ]

theorem qNormalizationRows_length : qNormalizationRows.length = 9 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1QNormalizationDictionaryActual
