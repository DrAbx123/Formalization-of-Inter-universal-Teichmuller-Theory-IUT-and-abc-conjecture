import Mathlib.RingTheory.Perfection
import Mathlib.RingTheory.Perfectoid.Untilt
import Mathlib.RingTheory.Perfectoid.FontaineTheta
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # S735: perfectoid / Fargues-Fontaine / adic Lean inventory (research only)

This file records what Mathlib actually provides for the Task G question:

  can perfectoid spaces / the Fargues-Fontaine curve / tilting / nonarch adic
  geometry supply a paper-faithful carrier for q[2u] and the Theta-pilot
  hull log?

It contains no new mathematical assertion: only `#check`s.  Companion memo:
`S735_TASK_G_PERFECTOID_FF_MEMO.md`.

Mathlib inventory (checked 2026-10-30, mathlib in D:\\lean\\.lake\\packages\\mathlib):
* `Mathlib/RingTheory/Perfection.lean`: `PreTilt` (a type of p-adic pre-tilt
  elements), not a perfectoid field.
* `Mathlib/RingTheory/Perfectoid/Untilt.lean`: `PreTilt.untilt` (the untilt
  *map* from a pre-tilt of a p-adically complete ring), explicitly *not* the
  untilt functor (file docstring).
* `Mathlib/RingTheory/Perfectoid/FontaineTheta.lean`: `fontaineTheta`,
  `fontaineThetaModPPow`, surjectivity from Frobenius-surjectivity.
* Absent (grep 0 in Mathlib): `PerfectoidRing`, `PerfectoidField`, a tilt
  functor/equivalence, `AdicSpace`/`Spa`, `FarguesFontaine`, Berkovich
  spaces.  Adic spaces exist only as an open draft PR, not in this checkout.
-/

namespace LeanFormal.IUT.XiFPaper.S735PerfectoidFFToolInventory

-- Mathlib's only perfectoid-related API.
#check PreTilt
#check PreTilt.untilt
#check PreTilt.mk_untilt_eq_coeff_zero
#check PreTilt.untilt_iterate_frobeniusEquiv_symm_pow
#check WittVector.fontaineTheta
#check WittVector.fontaineThetaModPPow
#check surjective_fontaineTheta

-- Haar / finrank machinery used by the paper hull log (already used in repo).
#check MeasureTheory.Measure.addHaar
#check Module.finrank
#check FiniteDimensional.proper

end LeanFormal.IUT.XiFPaper.S735PerfectoidFFToolInventory
