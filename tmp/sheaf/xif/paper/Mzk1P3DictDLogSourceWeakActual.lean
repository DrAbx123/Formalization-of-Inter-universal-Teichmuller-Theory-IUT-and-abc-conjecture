import tmp.sheaf.xif.paper.Mzk1P3DictDCurveDataSourceActual
import tmp.sheaf.xif.paper.Mzk1P3DictDLogDiscActual
import Mathlib.Tactic

/-! # GAP: weaker D source: log(disc)=e log p instead of disc=p^e -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictDLogSourceWeakActual

open LeanFormal.IUT.XiFPaper.Mzk1P3DictDLogDiscActual
open LeanFormal.IUT.XiFPaper.Mzk1P3DictDCurveDataSourceActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual

/-- Weaker named source: actual log of CurveData.disc equals e*log p. -/
structure PrimeConductorDiscLogSource {ι : Type*}
    (M : CurveData ι) (E : ι) (p : Nat) where
  hp : Nat.Prime p
  e : Nat
  log_disc_eq : Real.log (M.disc E : Real) = (e : Real) * Real.log (p : Real)

/-- Build the paper carrier from the weaker source. -/
def PrimeConductorDiscLogSource.toCurve
    {ι : Type*} {M : CurveData ι} {E : ι} {p : Nat}
    (S : PrimeConductorDiscLogSource M E p) : PrimeConductorCurve where
  p := p
  hp := S.hp
  e := S.e

/-- The weaker source gives the paper log disc equal to the actual log disc. -/
theorem toCurve_logDisc_eq_log_disc
    {ι : Type*} {M : CurveData ι} {E : ι} {p : Nat}
    (S : PrimeConductorDiscLogSource M E p) :
    primeConductorLogDisc (S.toCurve) = Real.log (M.disc E : Real) := by
  unfold primeConductorLogDisc
  change (S.e : Real) * Real.log (p : Real) = Real.log (M.disc E : Real)
  rw [← S.log_disc_eq]

#check PrimeConductorDiscLogSource
#check PrimeConductorDiscLogSource.toCurve
#check toCurve_logDisc_eq_log_disc
end LeanFormal.IUT.XiFPaper.Mzk1P3DictDLogSourceWeakActual
end
