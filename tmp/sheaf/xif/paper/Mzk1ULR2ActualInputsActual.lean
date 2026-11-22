/- Route 4.4 actual inputs: hVh, hlogdK, hsQ as named data/interface theorems. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULR2ActualInputsActual

/-- hlogdK data: K/Ftpd tower split into good/tame/wild local different contributions. -/
structure HlogdKData where
  logDifferentK : Real
  S_ar : Real
  logl : Real
  goodSum : Real
  tameSum : Real
  wildSum : Real
  hdecomp : logDifferentK <= goodSum + tameSum + wildSum + 21
  hgood : goodSum <= 0
  htame : tameSum <= S_ar + 2 * logl
  hwild : wildSum <= 0
  hS_ar_nonneg : 0 <= S_ar

/-- hlogdK bound: global different <= S_ar + 2 log l + 21. -/
theorem hlogdK_bound (D : HlogdKData) :
    D.logDifferentK <= D.S_ar + 2 * D.logl + 21 := by
  linarith [D.hdecomp, D.hgood, D.htame, D.hwild]

/-- hsQ data: actual finite bad-prime support split into q, different and special. -/
structure HsQData where
  logSQ : Real
  dmod : Real
  S_ar : Real
  logl : Real
  qdSum : Real
  specialSum : Real
  hsplit : logSQ <= qdSum + specialSum
  hqd : qdSum <= 2 * dmod * S_ar
  hspecial : specialSum <= 5 + logl
  hdmod_nonneg : 0 <= dmod

/-- hsQ bound: log sQ <= 2 dmod S_ar + 5 + log l. -/
theorem hsQ_bound (D : HsQData) :
    D.logSQ <= 2 * D.dmod * D.S_ar + 5 + D.logl := by
  linarith [D.hsplit, D.hqd, D.hspecial]

/-- hVh data: real procession row readouts. -/
structure HVhData (ι : Type*) [Fintype ι] where
  V : ι → Real
  w : ι → Real
  avg : Real
  hw_nonneg : ∀ i, 0 <= w i
  havg : avg <= (∑ i, w i * V i) / (∑ i, w i)
  hsum_pos : 0 < ∑ i, w i

/-- hVh: H = avg is bounded by the weighted row average of real row readouts V. -/
theorem hVh_le_weighted (ι : Type*) [Fintype ι] (D : HVhData ι) :
    D.avg <= (∑ i, D.w i * D.V i) / (∑ i, D.w i) :=
  D.havg

#print axioms hlogdK_bound
#print axioms hsQ_bound
#print axioms hVh_le_weighted

end LeanFormal.IUT.XiFPaper.Mzk1ULR2ActualInputsActual
