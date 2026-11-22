/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PrimeStripExponentActual
import tmp.sheaf.xif.paper.Mzk1PrimeStripDegreeActual

/-! # Chain bridge: degree sums of exponent-vector operations -/

namespace LeanFormal.IUT.XiFPaper.PrimeStripDegreeActual

open LeanFormal.IUT.XiFPaper.PrimeStripExponentActual

variable {ι : Type*}

theorem stripDegree_evAdd (s : Finset ι) (a b : ExpVec ι) :
    stripDegree s (evAdd a b) = stripDegree s a + stripDegree s b := by
  unfold stripDegree evAdd
  exact Finset.sum_add_distrib

theorem stripDegree_evZero (s : Finset ι) :
    stripDegree s (evZero : ExpVec ι) = 0 := by
  unfold stripDegree evZero
  simp

theorem stripDegree_evNeg (s : Finset ι) (a : ExpVec ι) :
    stripDegree s (evNeg a) = -stripDegree s a := by
  unfold stripDegree evNeg
  simp

theorem stripDegree_evAdd_evNeg (s : Finset ι) (a : ExpVec ι) :
    stripDegree s (evAdd a (evNeg a)) = 0 := by
  rw [stripDegree_evAdd, stripDegree_evNeg]
  exact add_neg_cancel (stripDegree s a)

end LeanFormal.IUT.XiFPaper.PrimeStripDegreeActual
