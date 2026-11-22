/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import tmp.sheaf.xif.paper.S2568S2subsetAoc2Actual
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# A3: from maximal localizations to `IsIntegrallyClosed Aoc2`

Context (actual files):

* `S2565`: `S2555_isIntegralClosure : IsIntegralClosure S R L`, with `R = ℤ[1/Cden]`,
  `S = R[C]`, `L = F'`;
* `S2566`: `Aoc2 = Algebra.adjoin R (HZc2.rootSet L)`, and every element of `Aoc2` is
  `algebraMap S L s` for some `s : S` (`adjoin2_subset_isIntegralClosure`);
* `S2567`: `S2567_isFractionRing : IsFractionRing Aoc2 L`;
* `S2568`: `[IsFractionRing Aoc2 L] → IsIntegrallyClosed Aoc2 → ∀ s : S, algebraMap S L s ∈ Aoc2`.

This file supplies the missing local-to-global link

  `(∀ p : Ideal Aoc2, p.IsMaximal → IsIntegrallyClosed (Localization.AtPrime p)) →
     IsIntegrallyClosed Aoc2`

using Mathlib's `IsIntegrallyClosed.of_localization_maximal`
(`Mathlib.RingTheory.LocalProperties.IntegrallyClosed`), whose exact shape is

```
theorem IsIntegrallyClosed.of_localization_maximal [IsDomain R]
    (h : ∀ p : Ideal R, p ≠ ⊥ → [p.IsMaximal] →
      IsIntegrallyClosed (Localization.AtPrime p)) : IsIntegrallyClosed R
```

API obligations discharged here:

* `IsDomain Aoc2`: Mathlib instance `Subalgebra.isDomain` (since `L` is a field);
* `[p.IsPrime]` needed by `Localization.AtPrime p`: the instance
  `Ideal.IsMaximal.isPrime'` from the `[p.IsMaximal]` binder;
* the `p ≠ ⊥` argument of the Mathlib criterion is simply discarded, so the hypothesis
  only has to quantify over maximal ideals.

No `sorry`, no new axiom, no `native_decide`.
-/

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

namespace LeanFormal.IUT.XiFPaper.A3LocalGlobalAgent

open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2566AdjoinIntegralCActual
open LeanFormal.IUT.XiFPaper.S2568S2subsetAoc2Actual

/-- **A3, main form.** If every localization of `Aoc2` at a maximal ideal is integrally
closed, then `Aoc2` is integrally closed. -/
theorem aoc2_isIntegrallyClosed_of_localization_maximal
    (hlocal : ∀ (p : Ideal Aoc2) [p.IsMaximal],
      IsIntegrallyClosed (Localization.AtPrime p)) :
    IsIntegrallyClosed Aoc2 :=
  IsIntegrallyClosed.of_localization_maximal (R := Aoc2) (fun p _ hmax => by
    haveI : p.IsMaximal := hmax
    exact hlocal p)

/-- The same criterion with an explicit maximality hypothesis instead of an instance
binder.  The `letI` in the hypothesis discharges the `[p.IsPrime]` requirement of
`Localization.AtPrime p` from the explicit `hp : p.IsMaximal`. -/
theorem aoc2_isIntegrallyClosed_of_localization_maximal'
    (hlocal : ∀ (p : Ideal Aoc2) (hp : p.IsMaximal),
      letI : p.IsMaximal := hp
      IsIntegrallyClosed (Localization.AtPrime p)) :
    IsIntegrallyClosed Aoc2 :=
  aoc2_isIntegrallyClosed_of_localization_maximal (fun p hmax => by
    haveI : p.IsMaximal := hmax
    exact hlocal p hmax)

/-- Local DVR input, the shape used in
`WeierstrassCoordinateRingIntegrallyClosed.sourceIntegrallyClosed_of_localizationDVR`.
`IsDiscreteValuationRing → IsIntegrallyClosed` is a Mathlib instance. -/
theorem aoc2_isIntegrallyClosed_of_localization_dvr
    (hlocal : ∀ (p : Ideal Aoc2) [p.IsMaximal],
      IsDiscreteValuationRing (Localization.AtPrime p)) :
    IsIntegrallyClosed Aoc2 :=
  aoc2_isIntegrallyClosed_of_localization_maximal (fun p hmax => by
    haveI : p.IsMaximal := hmax
    haveI := hlocal p
    infer_instance)

/-- **Consumer.** `S2568` with the global hypothesis `IsIntegrallyClosed Aoc2` replaced
by the local hypothesis at maximal ideals.  Requires `IsFractionRing Aoc2 L` (S2567). -/
theorem S2_le_Aoc2_of_localization_maximal [IsFractionRing Aoc2 L]
    (hlocal : ∀ (p : Ideal Aoc2) [p.IsMaximal],
      IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ s : S, algebraMap S L s ∈ Aoc2 :=
  S2_le_Aoc2_of_integrallyClosed (aoc2_isIntegrallyClosed_of_localization_maximal hlocal)

#check @IsIntegrallyClosed.of_localization_maximal
#print axioms aoc2_isIntegrallyClosed_of_localization_maximal
#print axioms aoc2_isIntegrallyClosed_of_localization_maximal'
#print axioms aoc2_isIntegrallyClosed_of_localization_dvr
#print axioms S2_le_Aoc2_of_localization_maximal

end LeanFormal.IUT.XiFPaper.A3LocalGlobalAgent
end