/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1StripDegreeExponentChainActual
import tmp.sheaf.xif.paper.Mzk1StripDegreeChainActual

/-! # Chain: nonpositivity of negated exponent-vector degrees -/

namespace LeanFormal.IUT.XiFPaper.PrimeStripDegreeActual

open LeanFormal.IUT.XiFPaper.PrimeStripExponentActual

variable {ι : Type*}

theorem stripDegree_evNeg_nonpos (s : Finset ι) {a : ExpVec ι}
    (h : ∀ i ∈ s, 0 ≤ a i) : stripDegree s (evNeg a) ≤ 0 := by
  rw [stripDegree_evNeg]
  exact neg_nonpos.mpr (stripDegree_nonneg s h)

theorem stripDegree_evZero_eq_zero (s : Finset ι) :
    stripDegree s (evZero : ExpVec ι) = 0 := stripDegree_evZero s

theorem stripDegree_evAdd_evNeg_zero (s : Finset ι) (a : ExpVec ι) :
    stripDegree s (evAdd a (evNeg a)) = 0 := stripDegree_evAdd_evNeg s a

end LeanFormal.IUT.XiFPaper.PrimeStripDegreeActual
