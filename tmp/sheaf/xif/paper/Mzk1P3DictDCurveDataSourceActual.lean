import Mathlib.Data.Nat.Factorization.Basic
import tmp.sheaf.xif.paper.Mzk1P3DictDLogDiscActual
import Mathlib.Tactic

/-! # GAP/CONDITIONAL: D-side actual Delta_min from Iut.CurveData.disc -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictDCurveDataSourceActual

/-! Local mirror of Iut.Abc.Counting.CurveData (Iut/Abc/Counting/Basic.lean:106-116);
the Iut module is not built in this lake workspace, so the structure is copied verbatim. -/

/-- Mirror of Iut.Abc.Counting.CurveData: absolute minimal discriminant and conductor. -/
structure CurveData (ι : Type*) where
  disc : ι -> Nat
  disc_ne_zero : forall E, disc E ≠ 0
  cond : ι -> Nat
  Semistable : ι -> Prop
open LeanFormal.IUT.XiFPaper.Mzk1P3DictDLogDiscActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual

/-- Actual prime-conductor discriminant data: an actual CurveData E, a prime p,
exponent e=v_p(disc), and the prime-conductor support equation disc=p^e. -/
structure PrimeConductorDiscDataSource {ι : Type*} (M : CurveData ι) (E : ι) (p : Nat) where
  hp : Nat.Prime p
  e : Nat
  e_eq : e = (M.disc E).factorization p
  disc_eq_pow : M.disc E = p ^ e

/-- Build the paper carrier from actual CurveData. -/
def PrimeConductorDiscDataSource.toCurve
    {ι : Type*} {M : CurveData ι} {E : ι} {p : Nat}
    (S : PrimeConductorDiscDataSource M E p) : PrimeConductorCurve where
  p := p
  hp := S.hp
  e := S.e

/-- The paper log disc equals the actual log of CurveData.disc. -/
theorem toCurve_logDisc_eq_log_disc
    {ι : Type*} {M : CurveData ι} {E : ι} {p : Nat}
    (S : PrimeConductorDiscDataSource M E p) :
    primeConductorLogDisc (S.toCurve) = Real.log (M.disc E : Real) := by
  unfold primeConductorLogDisc
  have hcast : (M.disc E : Real) = (p : Real) ^ S.e := by
    rw [S.disc_eq_pow]
    push_cast
    ring
  rw [hcast, Real.log_pow]
  rfl

/-- Symmetric form: actual log disc equals the paper log disc. -/
theorem log_disc_eq_toCurve_logDisc
    {ι : Type*} {M : CurveData ι} {E : ι} {p : Nat}
    (S : PrimeConductorDiscDataSource M E p) :
    Real.log (M.disc E : Real) = primeConductorLogDisc (S.toCurve) :=
  (toCurve_logDisc_eq_log_disc S).symm

#check PrimeConductorDiscDataSource
#check PrimeConductorDiscDataSource.toCurve
#check toCurve_logDisc_eq_log_disc
#check log_disc_eq_toCurve_logDisc
end LeanFormal.IUT.XiFPaper.Mzk1P3DictDCurveDataSourceActual
end
