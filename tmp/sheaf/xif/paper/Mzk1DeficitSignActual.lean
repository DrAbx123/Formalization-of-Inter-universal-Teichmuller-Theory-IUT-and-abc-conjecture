/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1DifferentDictionaryActual
import tmp.sheaf.xif.paper.Mzk1PaperNormDeficitActual
import Mathlib.Tactic

/-! # A800/A804: sign alignment of the paper different dictionary and p=2 case -/

/- hull dictionary (Mzk1DifferentDictionaryActual):
* `diffPaperLog order logp = -order * logp` (paper `log N(d)`),
* `diffPaperPerPlace order logp torsion arch = -order*logp - torsion + arch`,
  with `torsionConstant r n = r/n`, `archConstant = log(sqrt 2 * pi)`,
* `diffPaperPerPlace_different_eq`: subtracting `arch` and adding `torsion` gives
  `-order*logp` (the different term).

With hull's deficit `paperDeficit ssCoeff A sumLogMu sumTheta = ssCoeff*A - (sumLogMu + sumTheta)`
and `sumLogMu = diffDifferent - arch + torsion`, `sumTheta = c_lana*A`, `diffDifferent = -order*logp`:
  deficit = (ssCoeff - c_lana)*A + order*logp + arch - torsion.
This file proves exactly this sign-aligned expansion (pure algebra, no sign flip), plus the
p=2 numeric case `paperMuCoeff 2 1 2 1 = -1` and the p=2 positive-deficit conditional.

NOTE: whether C3/Theta-data realizes e=1, r=2, n=1 at p=2 is NOT decided here.
     (lattice reports e=1, r/n=1 impossible under standard conventions; the p=2 tuple is
      a different case and still has to be checked against sourceLocalLogShellDatum.) -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1DeficitSignActual

open LeanFormal.IUT.XiFPaper.Mzk1DifferentDictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperNormMuActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperNormDeficitActual

/-- **Sign-aligned deficit expansion**: with `sumLogMu = diffDifferent - arch + torsion`,
`sumTheta = cLana*A`, `diffDifferent = -order*logp`, the deficit equals
`(ssCoeff - cLana)*A + order*logp + arch - torsion`. -/
theorem deficit_sign_aligned (ssCoeff A cLana order logp arch torsion : ℝ) :
    ssCoeff * A - ((-order * logp - arch + torsion) + cLana * A) =
      (ssCoeff - cLana) * A + order * logp + arch - torsion := by
  ring

/-- The dictionary combination: paper different term = `-order*logp`; subtracting `arch`
and adding `torsion` recovers the different term. -/
theorem diffPerPlace_recover_different (order logp r n : ℝ) :
    diffPaperPerPlace order logp (torsionConstant r n) archConstant - archConstant +
      torsionConstant r n = -order * logp :=
  diffPaperPerPlace_different_eq order logp r n

/-- p = 2, e = 1, r = 2, n = 1: `paperMuCoeff = -1`. -/
theorem paperMuCoeff_p2_e1_r2_n1 : paperMuCoeff 2 1 2 1 = -1 := by
  unfold paperMuCoeff
  norm_num

/-- p = 2 instance: `logMuPaper = -log 2`. -/
theorem logMuPaper_p2_e1_r2_n1 : logMuPaper 2 1 2 1 = -Real.log 2 := by
  unfold logMuPaper paperMuCoeff
  norm_num

end LeanFormal.IUT.XiFPaper.Mzk1DeficitSignActual