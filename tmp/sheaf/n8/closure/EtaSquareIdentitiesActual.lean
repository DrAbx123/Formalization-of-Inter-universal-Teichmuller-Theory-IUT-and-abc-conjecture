import tmp.sheaf.n8.closure.EtaRouteInterface

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

/-!
# Actual ETA square identities

Uses the actual ETA route carriers Rval = preLogShell, Rss = logShell and the
actual scaling maps EtaQ/EtaAnab.  The scalar observation is the actual real-log
norm on nonzero carrier elements.  The two square identities are proved for
nonzero elements; the zero element (which lies in preLogShell) is the exact
obstruction to a global log-norm scalar map, since log norm is not
multiplicative at zero.
-/

noncomputable section

open MeasureTheory BigOperators
open IsDedekindDomain NumberField
open scoped NumberField
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C2Native
open LeanFormal.IUT.NumberFieldFinitePlace
open Multiplicative
open LeanFormal.IUT.N8Closure.EtaRouteInterface

namespace LeanFormal.IUT.N8Closure.EtaSquareIdentitiesActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance nativeShellNormedField : NormedField (NativeShell X).K :=
  inferInstanceAs (NormedField (NumberFieldFinitePlace.CommonPrimeCompletion
    (K := X.S.arithmetic.Fmod) (badPlaceAtPrime X)))

/-- Actual pStar scalar: real log norm of the actual ETA pStar. -/
noncomputable def pStarScalar : Multiplicative ℝ :=
  Multiplicative.ofAdd (Real.log ‖((NativeShell X).pStar : (NativeShell X).K)‖)

/-- Actual real-log-norm scalar on Rval = preLogShell. -/
noncomputable def rvalScalar (a : Rval X) : Multiplicative ℝ :=
  Multiplicative.ofAdd (Real.log ‖a.1‖)

/-- Actual real-log-norm scalar on Rss = logShell. -/
noncomputable def rssScalar (b : Rss X) : Multiplicative ℝ :=
  Multiplicative.ofAdd (Real.log ‖b.1‖)

theorem etaQ_scalar_square_of_ne_zero (a : Rval X) (ha : a.1 ≠ 0) :
    rssScalar X (EtaQ X a) = (pStarScalar X)⁻¹ * rvalScalar X a := by
  unfold rssScalar rvalScalar pStarScalar EtaQ
  apply Multiplicative.ext
  simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd]
  rw [norm_mul, norm_inv]
  have hp : ((NativeShell X).pStar : (NativeShell X).K) ≠ 0 :=
    SourceLogShellDatum.pStar_ne_zero_cast (NativeShell X)
  have hpn : ‖((NativeShell X).pStar : (NativeShell X).K)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hp
  have han : ‖a.1‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  rw [Real.log_mul (inv_ne_zero hpn) han, Real.log_inv]

theorem etaAnab_scalar_square_of_ne_zero (b : Rss X) (hb : b.1 ≠ 0) :
    rvalScalar X (EtaAnab X b) = pStarScalar X * rssScalar X b := by
  unfold rvalScalar rssScalar pStarScalar EtaAnab
  apply Multiplicative.ext
  simp only [toAdd_mul, toAdd_ofAdd]
  rw [norm_mul]
  have hp : ((NativeShell X).pStar : (NativeShell X).K) ≠ 0 :=
    SourceLogShellDatum.pStar_ne_zero_cast (NativeShell X)
  have hpn : ‖((NativeShell X).pStar : (NativeShell X).K)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hp
  have hbn : ‖b.1‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  rw [Real.log_mul hpn hbn]

/-- Exact obstruction at zero: zero lies in preLogShell, and a global
log-norm scalar identity would force log pStar = 0 there. -/
theorem zero_mem_preLogShell : (0 : (NativeShell X).K) ∈ Rval X :=
  SourceLogShellDatum.zero_mem_preLogShell (NativeShell X)

/-- Exact gap: no global real-log-norm scalar map satisfies the square
identities on the zero element of preLogShell. -/
def MissingGlobalScalarSquare : Prop :=
  ¬ (∀ a : Rval X,
      rssScalar X (EtaQ X a) = (pStarScalar X)⁻¹ * rvalScalar X a)

end LeanFormal.IUT.N8Closure.EtaSquareIdentitiesActual

end