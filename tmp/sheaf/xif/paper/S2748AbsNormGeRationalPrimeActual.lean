import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFullPrimePacket
import tmp.sheaf.xif.paper.S2748RationalAbsNormActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2748RationalAbsNormActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2748AbsNormGeRationalPrimeActual

variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]

/-- The absolute norm of the maximal ideal of a finite place above the rational
prime p is at least p (real proof: Mathlib absNorm = p ^ inertiaDeg' with positive
inertia degree; the LiesOver relation comes from the actual completion comap bridge). -/
theorem S2748_absNorm_ge_rationalPrime
    (P : FinitePlaceAtPrime K p) :
    p <= Ideal.absNorm P.val.maximalIdeal.asIdeal := by
  let Q := P.val.maximalIdeal.asIdeal
  let q := (rationalFinitePlace p).maximalIdeal.asIdeal
  have hcomap : comap (k := ℚ) P.val = rationalFinitePlace p :=
    comap_eq_rationalFinitePlace P
  have hlies : Q.LiesOver q :=
    S2748_liesOver_of_comap P.val (rationalFinitePlace p) hcomap
  letI : Q.LiesOver q := hlies
  have hmain := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver
    (P := Q) (p := q) (rationalFinitePlace p).maximalIdeal.isPrime
    (rationalFinitePlace p).maximalIdeal.ne_bot
  rw [S2748_absNorm_rationalFinitePlace p] at hmain
  let f := q.inertiaDeg' Q
  have hf : 0 < f := Ideal.inertiaDeg'_pos (p := q) (P := Q)
  have hle : p ^ 1 ≤ p ^ f :=
    Nat.pow_le_pow_right (Fact.out : Nat.Prime p).pos hf
  rw [hmain]
  exact le_trans (by simp) hle

end LeanFormal.IUT.XiFPaper.S2748AbsNormGeRationalPrimeActual
end
