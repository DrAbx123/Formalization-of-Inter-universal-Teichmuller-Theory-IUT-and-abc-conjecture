/- U-C S1: paper weights (lambda_v / local total), no over-Q completion degree.

lambda_v := [(F_mod)_v : Q_p] via relativeCompletionDegree (k := Q) (K := Fmod)
(FinitePlaceCompletionNormTransport.relativeCompletionDegree).  localTotal is the
BAD-fiber sum of lambda (pFiber); missingLambda (full-fiber sum minus bad-fiber
sum) is the explicit J2 index term and needs the full place-fiber index set
(pending: fullPrimeArithmeticTensorDimension with the fiber index instance).
Provenance: IUT IV L1715-1716 (lambda_e = [(F_mod)_v : Q_vQ], weighted average
denominator), L1736-1741, L1860-1874 (outer sum over v_Q carries weight 1).
-/
import tmp.sheaf.xif.paper.Mzk1ULPaperLettersActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticPacketVolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFullPrimePacket
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULPaperWeightActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- lambda_b := [(F_mod)_v : Q_p] for the bad F_mod place v = b.1. -/
noncomputable def baseLambda (b : Bad (nativePlaceSelection T)) : ℝ :=
  (LeanFormal.IUT.NumberFieldFinitePlace.relativeCompletionDegree (k := ℚ)
    (K := T.arithmetic.Fmod) (nativeBadFmodPlace T b) : ℝ)

/-- PROVED: lambda_b > 0 (e and f are nonzero). -/
theorem zero_lt_baseLambda (b : Bad (nativePlaceSelection T)) : 0 < baseLambda T b := by
  unfold baseLambda
  have he : LeanFormal.IUT.NumberFieldFinitePlace.relativeRamificationIndex (k := ℚ)
      (K := T.arithmetic.Fmod) (nativeBadFmodPlace T b) ≠ 0 :=
    LeanFormal.IUT.NumberFieldFinitePlace.relativeRamificationIndex_ne_zero _
  have hf : LeanFormal.IUT.NumberFieldFinitePlace.relativeResidueDegree (k := ℚ)
      (K := T.arithmetic.Fmod) (nativeBadFmodPlace T b) ≠ 0 :=
    LeanFormal.IUT.NumberFieldFinitePlace.relativeResidueDegree_ne_zero _
  have hne : LeanFormal.IUT.NumberFieldFinitePlace.relativeCompletionDegree (k := ℚ)
      (K := T.arithmetic.Fmod) (nativeBadFmodPlace T b) ≠ 0 := by
    unfold LeanFormal.IUT.NumberFieldFinitePlace.relativeCompletionDegree
    exact mul_ne_zero he hf
  have hpos : 0 < LeanFormal.IUT.NumberFieldFinitePlace.relativeCompletionDegree (k := ℚ)
      (K := T.arithmetic.Fmod) (nativeBadFmodPlace T b) :=
    Nat.pos_of_ne_zero hne
  exact_mod_cast hpos

/-- the fiber of bad places over the rational prime p. -/
noncomputable def pFiber (p : ℕ) : Finset (Bad (nativePlaceSelection T)) :=
  Finset.univ.filter (fun b => qVFamTensorP T b = p)

/-- BAD-fiber sum of lambda. -/
noncomputable def localTotal (b : Bad (nativePlaceSelection T)) : ℝ :=
  ∑ b' ∈ pFiber T (qVFamTensorP T b), baseLambda T b'

/-- PROVED: the bad-fiber lambda sum is positive. -/
theorem zero_lt_localTotal (b : Bad (nativePlaceSelection T)) : 0 < localTotal T b := by
  unfold localTotal
  have hb : b ∈ pFiber T (qVFamTensorP T b) := by
    unfold pFiber
    simp
  have hle : baseLambda T b ≤ ∑ b' ∈ pFiber T (qVFamTensorP T b), baseLambda T b' :=
    Finset.single_le_sum (f := fun b' => baseLambda T b')
      (fun b' _ => (zero_lt_baseLambda T b').le) hb
  linarith [zero_lt_baseLambda T b]

/-- paper weight: lambda_b / bad-fiber local total. -/
noncomputable def paperWeight (b : Bad (nativePlaceSelection T)) : ℝ :=
  baseLambda T b / localTotal T b

/-- PROVED: the paper weight is positive. -/
theorem zero_lt_paperWeight (b : Bad (nativePlaceSelection T)) : 0 < paperWeight T b := by
  unfold paperWeight
  exact div_pos (zero_lt_baseLambda T b) (zero_lt_localTotal T b)

/-- PROVED: the paper weights sum to 1 on each bad fiber. -/
theorem paperWeight_sum_fiber (b0 : Bad (nativePlaceSelection T)) :
    (∑ b ∈ pFiber T (qVFamTensorP T b0), paperWeight T b) = 1 := by
  unfold paperWeight localTotal
  have hconst : ∀ b ∈ pFiber T (qVFamTensorP T b0),
      (∑ b' ∈ pFiber T (qVFamTensorP T b), baseLambda T b')
        = (∑ b' ∈ pFiber T (qVFamTensorP T b0), baseLambda T b') := by
    intro b hb
    have hpeq : qVFamTensorP T b = qVFamTensorP T b0 := by
      unfold pFiber at hb
      simpa using (Finset.mem_filter.mp hb).2
    rw [hpeq]
  calc (∑ b ∈ pFiber T (qVFamTensorP T b0),
        baseLambda T b / (∑ b' ∈ pFiber T (qVFamTensorP T b), baseLambda T b'))
      = (∑ b ∈ pFiber T (qVFamTensorP T b0),
          baseLambda T b / (∑ b' ∈ pFiber T (qVFamTensorP T b0), baseLambda T b')) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [hconst b hb]
    _ = (∑ b ∈ pFiber T (qVFamTensorP T b0), baseLambda T b)
          / (∑ b' ∈ pFiber T (qVFamTensorP T b0), baseLambda T b') := by
        rw [Finset.sum_div]
    _ = 1 := by
        have hpos : 0 < ∑ b' ∈ pFiber T (qVFamTensorP T b0), baseLambda T b' := by
          have := zero_lt_localTotal T b0
          simpa [localTotal] using this
        field_simp


/-- full-fiber lambda total: the local degree [F_mod x Q_p : Q_p] of the base
field at the rational prime p (sum over ALL places over p). -/
noncomputable def fullLambda (b : Bad (nativePlaceSelection T)) : ℝ :=
  (LeanFormal.IUT.NumberFieldFinitePlace.fullPrimeArithmeticTensorDimension
    (K := T.arithmetic.Fmod) (p := qVFamTensorP T b)
    (LeanFormal.IUT.NumberFieldFinitePlace.FinitePlaceAtPrime T.arithmetic.Fmod
      (qVFamTensorP T b)) : ℝ)

/-- EXPLICIT J2 index term: full-fiber lambda total minus the bad-fiber total. -/
noncomputable def missingLambda (b : Bad (nativePlaceSelection T)) : ℝ :=
  fullLambda T b - localTotal T b

/-- PROVED (definitional): bad-fiber total + missing term = full-fiber total. -/
theorem localTotal_add_missingLambda (b : Bad (nativePlaceSelection T)) :
    localTotal T b + missingLambda T b = fullLambda T b := by
  unfold missingLambda
  ring

end LeanFormal.IUT.XiFPaper.Mzk1ULPaperWeightActual
end