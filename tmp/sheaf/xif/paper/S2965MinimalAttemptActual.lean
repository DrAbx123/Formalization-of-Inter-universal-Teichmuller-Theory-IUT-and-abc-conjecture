import tmp.sheaf.xif.paper.S2965DirectHeightProcession
import tmp.sheaf.xif.paper.S2966AbsNormJEqRadActual
import tmp.sheaf.xif.paper.S2967QDecomposition
import tmp.sheaf.xif.paper.S2935HeightLeProcessionActual
import tmp.sheaf.xif.paper.S2847A6ArithmeticActual
import LeanFormal.IUT.ABCBridge.Arithmetic.LogarithmicBoundEquivalence

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2965DirectHeightProcession
open LeanFormal.IUT.XiFPaper.S2921HeightBridgeActual
open LeanFormal.IUT.XiFPaper.S2966AbsNormJEqRadActual
open LeanFormal.IUT.XiFPaper.S2967QDecomposition
open LeanFormal.IUT.XiFPaper.S2935HeightLeProcessionActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.XiFPaper.S2752FinalHweightvolActual
open Finset
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2965MinimalAttemptActual

/-!
## Direct proof attempt for `S2965MinimalLinear`

The target `S2965MinimalLinear n` is the linear (non-summed) form of the
elementary ABC bound with the actual `S2921` candidates `D, Q, S, T`.

This file proves, with no new assumptions and no `sorry`:

1. the candidate `D` is exactly `0` for the A6 arithmetic data
   (`Fmod = F = F6`, so `finrank = 1`);
2. `Q = log(5*5*2161*2161) + S` exactly, and `T = 5 * S` exactly;
3. hence the whole right-hand side is the affine function
   `kappa n * S - ((n+1)/12) * log(5*5*2161*2161)` of the single quantity
   `S = S2921S a b c`, with `kappa n = (119 n + 371)/12 > 0`;
4. therefore the target is *exactly equivalent* to a one-variable lower bound
   on `S2921S` (`S2965SLogLower`), a strictly smaller unproven statement:
   no height, no line bundle, no collection sum;
5. the only lower bound available is `S >= log rad(a b c)`, which reduces the
   target to the explicit radical inequality `S2965RadicalLower`;
6. that radical inequality is *exactly* an ABC logarithmic bound of exponent
   `kappa n / 6 >= 490/72 > 6.8` (`S2965_radicalLower_iff_ABCLogBound`), and
   the target itself implies the ABC logarithmic bound of exponent
   `kappa n / 3` (factor two weaker);
7. the available `S2921_hweightvol_candidate` has the wrong direction for this
   target: it bounds the target expression from above, not from below;
8. the target does imply the existing `S2935HeightLeProcession` target
   (consumer); its conclusion is the stronger one (the elementary bound
   `6 log c + log 256` rather than the J-height), and the J-height upper bound
   `logHeight <= 6 log c + log 256` goes the wrong way, so the height target
   cannot yield it;
9. a non-vacuity check: the target inequality holds at the ABC triple
   `(1, 1, 2)` for every `n`;
10. the family is monotone in `n`: `S2965MinimalLinear 1` implies
   `S2965MinimalLinear n` for every `n >= 1`, so the whole family reduces to
   the single case `n = 1`.

The exact first error is recorded at the end: a missing *uniform* ABC quality
bound `rad(a b c) >= c^delta`; the two-sided bound
`log rad <= S <= 2 log rad` is in the tree, but no lower bound of `log c` in
terms of `log rad` is.
-/

/-! ## 1. The candidate `D` is zero -/

/-- The A6 arithmetic data has `Fmod = F`, so the field degree is `1` and the
candidate `S2921D = log 1 = 0`. -/
theorem S2965_finrank_eq_one : Module.finrank S2847A6.Fmod S2847A6.F = 1 := by
  show Module.finrank S2847F6 S2847F6 = 1
  exact CommSemiring.finrank_self S2847F6

theorem S2965_D_eq_zero : S2921D = 0 := by
  unfold S2921D
  rw [S2965_finrank_eq_one]
  norm_num

/-! ## 2. Exact affine structure of `Q` and `T` -/

/-- `S2921Q` is the q-pilot constant plus `S2921S` (S2967 exact
decomposition). -/
theorem S2965_Q_eq_const_add_S (a b c : Nat) :
    S2921Q a b c = S2967Qconst + S2921S a b c := by
  rw [S2967Q_decomp]
  rfl

/-- `S2921T` is `l^*_mod = 5` times `S2921S`. -/
theorem S2965_T_eq_five_mul_S (a b c : Nat) :
    S2921T a b c = 5 * S2921S a b c := by
  unfold S2921T
  have hval : ((S2771FiveLabel.value : Nat) : ℝ) = 5 := by
    show ((5 : Nat) : ℝ) = 5
    norm_num
  rw [hval]

/-- The coefficient of `S2921S` in the linear form once `D = 0`, `Q = c0 + S`
and `T = 5 S` are substituted. -/
noncomputable def S2965Kappa (n : Nat) : ℝ :=
  1 + ((2 * (n : ℝ) + 1) + 5) * 5 - (((2 * (n : ℝ) + 1) + 1) / 24)

theorem S2965_kappa_eq (n : Nat) :
    S2965Kappa n = ((119 : ℝ) * (n : ℝ) + 371) / 12 := by
  unfold S2965Kappa
  ring

theorem S2965_kappa_pos (n : Nat) : 0 < S2965Kappa n := by
  rw [S2965_kappa_eq]
  positivity

theorem S2965_kappa_one : S2965Kappa 1 = 490 / 12 := by
  rw [S2965_kappa_eq]
  norm_num

/-- **The linear form is affine in `S`.**  Under the exact identities above,
the right-hand side of `S2965MinimalLinear` is
`kappa n * S - ((n+1)/12) * log(5*5*2161*2161)`. -/
theorem S2965_linear_eq (n a b c : Nat) :
    ((2 * (n : ℝ) + 1) + 5) / 4 * S2921D -
        ((2 * (n : ℝ) + 1) + 1) / 24 * S2921Q a b c +
        S2921S a b c + ((2 * (n : ℝ) + 1) + 5) * S2921T a b c =
      S2965Kappa n * S2921S a b c -
        (((2 * (n : ℝ) + 1) + 1) / 24) * S2967Qconst := by
  rw [S2965_D_eq_zero, S2965_Q_eq_const_add_S a b c, S2965_T_eq_five_mul_S a b c]
  unfold S2965Kappa
  ring

/-! ## 3. Exact reduction to one lower bound on `S2921S` -/

/-- The strictly smaller target: a pointwise lower bound for `S2921S`. -/
def S2965SLogLower (n : Nat) : Prop :=
  ∀ a b c : Nat, IsABCTriple a b c →
    6 * Real.log (c : ℝ) + Real.log 256 +
        (((2 * (n : ℝ) + 1) + 1) / 24) * S2967Qconst ≤
      S2965Kappa n * S2921S a b c

/-- **The target is equivalent to the one-variable lower bound.** -/
theorem S2965_minimal_iff_SLogLower (n : Nat) :
    S2965MinimalLinear n ↔ S2965SLogLower n := by
  constructor
  · intro h a b c habc
    have h1 := h a b c habc
    rw [S2965_linear_eq n a b c] at h1
    linarith
  · intro h a b c habc
    have h1 := h a b c habc
    rw [S2965_linear_eq n a b c]
    linarith

/-! ## 4. The available lower bound on `S2921S` -/

/-- `S2921S` dominates the arithmetic weight `log rad(a b c)` (S2966:
`rad <= absNorm J`). -/
theorem S2965_weight_le_S (a b c : Nat) (habc : IsABCTriple a b c) :
    arithmeticWeight (abcRationalPoint a c) ≤ S2921S a b c := by
  rw [arithmeticWeight_abcRationalPoint habc, S2966_S2921S_eq_log_absNorm]
  apply Real.log_le_log
  · exact_mod_cast natRadical_pos (a * b * c)
  · exact_mod_cast S2966_rad_le_absNorm a b c habc

/-- The radical form of the missing inequality. -/
def S2965RadicalLower (n : Nat) : Prop :=
  ∀ a b c : Nat, IsABCTriple a b c →
    6 * Real.log (c : ℝ) + Real.log 256 +
        (((2 * (n : ℝ) + 1) + 1) / 24) * S2967Qconst ≤
      S2965Kappa n * arithmeticWeight (abcRationalPoint a c)

/-- **Reduction to the radical inequality**: `S2965RadicalLower` is enough. -/
theorem S2965MinimalLinear_of_radical (n : Nat) (h : S2965RadicalLower n) :
    S2965MinimalLinear n := by
  rw [S2965_minimal_iff_SLogLower]
  intro a b c habc
  have h1 := h a b c habc
  have h2 := S2965_weight_le_S a b c habc
  have hk : 0 ≤ S2965Kappa n := le_of_lt (S2965_kappa_pos n)
  have h3 := mul_le_mul_of_nonneg_left h2 hk
  linarith

/-- The radical inequality written with `natRadical`. -/
theorem S2965_radicalLower_iff_natRadical (n : Nat) :
    S2965RadicalLower n ↔
      ∀ a b c : Nat, IsABCTriple a b c →
        6 * Real.log (c : ℝ) + Real.log 256 +
            (((2 * (n : ℝ) + 1) + 1) / 24) * S2967Qconst ≤
          S2965Kappa n * Real.log ((natRadical (a * b * c) : Nat) : ℝ) := by
  constructor
  · intro h a b c habc
    have h1 := h a b c habc
    rwa [arithmeticWeight_abcRationalPoint habc] at h1
  · intro h a b c habc
    have h1 := h a b c habc
    rwa [arithmeticWeight_abcRationalPoint habc]

/-- **The radical inequality is exactly an ABC logarithmic bound** with
exponent `kappa n / 6` and constant `-(log 256 + ((n+1)/12) c0)/6`. -/
theorem S2965_radicalLower_iff_ABCLogBound (n : Nat) :
    S2965RadicalLower n ↔
      ABCLogBound (S2965Kappa n / 6 - 1)
        (-(Real.log 256 + (((2 * (n : ℝ) + 1) + 1) / 24) * S2967Qconst) / 6) := by
  constructor
  · intro h a b c habc
    have h1 := (S2965_radicalLower_iff_natRadical n).mp h a b c habc
    have he : (1 + (S2965Kappa n / 6 - 1)) = S2965Kappa n / 6 := by ring
    rw [he]
    linarith
  · intro h a b c habc
    have h1 := h a b c habc
    have he : (1 + (S2965Kappa n / 6 - 1)) = S2965Kappa n / 6 := by ring
    rw [he] at h1
    rw [arithmeticWeight_abcRationalPoint habc]
    linarith

/-- The q-pilot constant `log(5*5*2161*2161)` is at most `30 log 2`. -/
theorem S2965_Qconst_le (n : Nat) : S2967Qconst ≤ 30 * Real.log 2 := by
  unfold S2967Qconst
  calc Real.log ((5 * 5 * 2161 * 2161 : Nat) : ℝ)
      ≤ Real.log ((2 : ℝ) ^ 30) := by
        apply Real.log_le_log
        · norm_num
        · norm_num
    _ = 30 * Real.log 2 := by
        rw [Real.log_pow]
        norm_num

/-! ## 4b. Monotonicity in `n`: it suffices to prove the target at `n = 1` -/

/-- The arithmetic weight is at least `log 2`: an ABC triple has
`a * b * c >= 2`, hence `rad(a b c) >= 2`. -/
theorem S2965_weight_ge_log_two (a b c : Nat) (habc : IsABCTriple a b c) :
    Real.log 2 ≤ arithmeticWeight (abcRationalPoint a c) := by
  rw [arithmeticWeight_abcRationalPoint habc]
  have hne : natRadical (a * b * c) ≠ 1 := by
    intro h1
    have hle : a * b * c ≤ 1 := (natRadical_eq_one_iff (n := a * b * c)).mp h1
    obtain ⟨ha, hb, hsum, _⟩ := habc
    have hc : 2 ≤ c := by omega
    have hab : 1 ≤ a * b := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have h2 : 2 ≤ a * b * c := by
      calc (2 : Nat) = 1 * 2 := by norm_num
        _ ≤ (a * b) * c := Nat.mul_le_mul hab hc
        _ = a * b * c := by ring
    omega
  have hpos : 0 < natRadical (a * b * c) := natRadical_pos _
  have h2 : 2 ≤ natRadical (a * b * c) := by omega
  exact Real.log_le_log (by norm_num) (by exact_mod_cast h2)

/-- Pointwise monotonicity of the linear form: with `S >= log 2` the linear
form at `n = 1` is at most the linear form at `n`.  Indeed the difference is
`((n-1)/12) * (119 S - c0)` and `c0 <= 30 log 2 <= 119 S`. -/
theorem S2965_linearForm_one_le (n : Nat) (hn : 1 ≤ n) {S : ℝ}
    (hS : Real.log 2 ≤ S) :
    S2965Kappa 1 * S - (((2 * (1 : ℝ) + 1) + 1) / 24) * S2967Qconst ≤
      S2965Kappa n * S - (((2 * (n : ℝ) + 1) + 1) / 24) * S2967Qconst := by
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hc0 : S2967Qconst ≤ 30 * Real.log 2 := S2965_Qconst_le n
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hS119 : S2967Qconst ≤ 119 * S := by nlinarith
  have hk : S2965Kappa n = S2965Kappa 1 + 119 * ((n : ℝ) - 1) / 12 := by
    rw [S2965_kappa_eq n, S2965_kappa_eq 1]
    push_cast
    ring
  have hc1 : ((2 * (n : ℝ) + 1) + 1) / 24 =
      ((2 * (1 : ℝ) + 1) + 1) / 24 + ((n : ℝ) - 1) / 12 := by
    ring
  have hd : 0 ≤ ((n : ℝ) - 1) / 12 * (119 * S - S2967Qconst) := by
    apply mul_nonneg
    · apply div_nonneg _ (by norm_num)
      linarith
    · linarith
  nlinarith [hk, hc1, hd]

theorem S2965SLogLower_one_implies (n : Nat) (hn : 1 ≤ n) (h : S2965SLogLower 1) :
    S2965SLogLower n := by
  intro a b c habc
  have h1 := h a b c habc
  have hw := S2965_weight_ge_log_two a b c habc
  have hS := S2965_weight_le_S a b c habc
  have hmono := S2965_linearForm_one_le n hn (le_trans hw hS)
  linarith

/-- **It suffices to prove the target at `n = 1`.** -/
theorem S2965MinimalLinear_of_one (n : Nat) (hn : 1 ≤ n) (h : S2965MinimalLinear 1) :
    S2965MinimalLinear n := by
  rw [S2965_minimal_iff_SLogLower]
  exact S2965SLogLower_one_implies n hn ((S2965_minimal_iff_SLogLower 1).mp h)

/-! ## 5. The target implies a (factor-two weaker) ABC logarithmic bound -/

/-- `S2921S` is at most twice the arithmetic weight (S2966:
`absNorm J <= rad^2`). -/
theorem S2965_S_le_two_weight (a b c : Nat) (habc : IsABCTriple a b c) :
    S2921S a b c ≤ 2 * arithmeticWeight (abcRationalPoint a c) := by
  rw [arithmeticWeight_abcRationalPoint habc, S2966_S2921S_eq_log_absNorm]
  have hradpos : (0 : ℝ) < (natRadical (a * b * c) : ℝ) := by
    exact_mod_cast natRadical_pos (a * b * c)
  have hradle : natRadical (a * b * c) ≤ Ideal.absNorm (S2752J S2771FiveLabel a b c) :=
    S2966_rad_le_absNorm a b c habc
  have hradleR : (natRadical (a * b * c) : ℝ) ≤
      ((Ideal.absNorm (S2752J S2771FiveLabel a b c) : Nat) : ℝ) := by
    exact_mod_cast hradle
  have hJpos : (0 : ℝ) < ((Ideal.absNorm (S2752J S2771FiveLabel a b c) : Nat) : ℝ) :=
    lt_of_lt_of_le hradpos hradleR
  have hle : ((Ideal.absNorm (S2752J S2771FiveLabel a b c) : Nat) : ℝ) ≤
      ((natRadical (a * b * c) : ℝ)) ^ 2 := by
    have h := S2966_absNorm_le_radSq a b c habc
    have hcast : (((natRadical (a * b * c)) ^ 2 : Nat) : ℝ) =
        ((natRadical (a * b * c) : ℝ)) ^ 2 := by push_cast; ring
    rw [← hcast]
    exact_mod_cast h
  calc Real.log ((Ideal.absNorm (S2752J S2771FiveLabel a b c) : Nat) : ℝ)
      ≤ Real.log (((natRadical (a * b * c) : ℝ)) ^ 2) := Real.log_le_log hJpos hle
    _ = 2 * Real.log ((natRadical (a * b * c) : ℝ)) := by
        rw [Real.log_pow]
        norm_num

/-- **Converse direction**: the target implies an ABC logarithmic bound with
exponent `kappa n / 3` (this is the two-sided bound
`log rad <= S <= 2 log rad` at work). -/
theorem S2965_ABCLogBound_of_minimal (n : Nat) (h : S2965MinimalLinear n) :
    ABCLogBound (S2965Kappa n / 3 - 1)
      (-(Real.log 256 + (((2 * (n : ℝ) + 1) + 1) / 24) * S2967Qconst) / 6) := by
  intro a b c habc
  have h1 := (S2965_minimal_iff_SLogLower n).mp h a b c habc
  have h2 := S2965_S_le_two_weight a b c habc
  have hk : 0 ≤ S2965Kappa n := le_of_lt (S2965_kappa_pos n)
  have h3 : S2965Kappa n * S2921S a b c ≤
      S2965Kappa n * (2 * arithmeticWeight (abcRationalPoint a c)) :=
    mul_le_mul_of_nonneg_left h2 hk
  have h4 : 6 * Real.log (c : ℝ) + Real.log 256 +
      (((2 * (n : ℝ) + 1) + 1) / 24) * S2967Qconst ≤
      S2965Kappa n * (2 * arithmeticWeight (abcRationalPoint a c)) := le_trans h1 h3
  rw [arithmeticWeight_abcRationalPoint habc] at h4
  have he : (1 + (S2965Kappa n / 3 - 1)) = S2965Kappa n / 3 := by ring
  rw [he]
  linarith

/-! ## 6. Direction of the available `hweightvol` comparison -/

/-- The available `arithmeticWeight <= Q` (S2921) can only bound the target
expression from *above*: since the coefficient of `Q` is negative, replacing
`Q` by the weight *decreases* the right-hand side.  Hence it cannot supply the
lower bound that the target needs. -/
theorem S2965_linear_le_weight_form (n a b c : Nat) (habc : IsABCTriple a b c) :
    ((2 * (n : ℝ) + 1) + 5) / 4 * S2921D -
        ((2 * (n : ℝ) + 1) + 1) / 24 * S2921Q a b c +
        S2921S a b c + ((2 * (n : ℝ) + 1) + 5) * S2921T a b c
      ≤ ((2 * (n : ℝ) + 1) + 5) / 4 * S2921D -
        ((2 * (n : ℝ) + 1) + 1) / 24 * arithmeticWeight (abcRationalPoint a c) +
        S2921S a b c + ((2 * (n : ℝ) + 1) + 5) * S2921T a b c := by
  have h := S2921_hweightvol_candidate a b c habc
  have hc : (0 : ℝ) ≤ (((2 * (n : ℝ) + 1) + 1) / 24) := by positivity
  have hm := mul_le_mul_of_nonneg_left h hc
  linarith

/-! ## 7. Consumer: the target implies the height-to-procession target -/

/-- `S2965MinimalLinear` implies `S2935HeightLeProcession`: the J-height is at
most `6 log c + log 256` (`S2935_Jheight_upper`), and the target bounds the
latter.  Note that this is the only direction available: the target has the
stronger conclusion (the elementary bound rather than the J-height), because
`logHeight <= 6 log c + log 256` cannot be reversed (the lower bound is
`6 log c + log(27/64)`), so the height-to-procession target cannot yield it. -/
theorem S2965MinimalLinear_implies_heightLeProcession (n : Nat) (hn : 1 ≤ n)
    (h : S2965MinimalLinear n) : S2935HeightLeProcession n := by
  intro a b c habc
  have h1 := S2965_target_of_minimal n hn h a b c habc
  have h2 := S2935_Jheight_upper a b c habc
  exact le_trans h2 h1

/-! ## 8. Non-vacuity: the target inequality holds at `(1, 1, 2)` -/

theorem S2965_isABCTriple_one_one_two : IsABCTriple 1 1 2 :=
  ⟨Nat.one_pos, Nat.one_pos, by norm_num, by norm_num⟩

theorem S2965_natRadical_one_one_two : natRadical (1 * 1 * 2) = 2 := by
  have h2 : (1 : Nat) * 1 * 2 = 2 := by norm_num
  rw [h2]
  have hdvd : natRadical 2 ∣ 2 := natRadical_dvd_self
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exfalso
    have : 2 ≤ 1 := (natRadical_eq_one_iff (n := 2)).mp h
    omega
  · exact h

theorem S2965_S_one_one_two_ge : Real.log 2 ≤ S2921S 1 1 2 := by
  have h := S2965_weight_le_S 1 1 2 S2965_isABCTriple_one_one_two
  rwa [arithmeticWeight_abcRationalPoint S2965_isABCTriple_one_one_two,
    S2965_natRadical_one_one_two] at h

theorem S2965_log256_eq : Real.log (256 : ℝ) = 8 * Real.log 2 := by
  have h : (256 : ℝ) = (2 : ℝ) ^ 8 := by norm_num
  rw [h, Real.log_pow]
  norm_num

/-- Numeric end-game: at `log 2` the whole constant part fits. -/
theorem S2965_const_bound (n : Nat) :
    6 * Real.log 2 + Real.log 256 +
        (((2 * (n : ℝ) + 1) + 1) / 24) * S2967Qconst ≤
      S2965Kappa n * Real.log 2 := by
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hQ : S2967Qconst ≤ 30 * Real.log 2 := S2965_Qconst_le n
  have hc1 : (0 : ℝ) ≤ (((2 * (n : ℝ) + 1) + 1) / 24) := by positivity
  have hQ2 : (((2 * (n : ℝ) + 1) + 1) / 24) * S2967Qconst ≤
      (((2 * (n : ℝ) + 1) + 1) / 24) * (30 * Real.log 2) :=
    mul_le_mul_of_nonneg_left hQ hc1
  have hlog256 : Real.log (256 : ℝ) = 8 * Real.log 2 := S2965_log256_eq
  have hlin : 14 + 30 * (((2 * (n : ℝ) + 1) + 1) / 24) ≤ S2965Kappa n := by
    rw [S2965_kappa_eq]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hmul : (14 + 30 * (((2 * (n : ℝ) + 1) + 1) / 24)) * Real.log 2 ≤
      S2965Kappa n * Real.log 2 :=
    mul_le_mul_of_nonneg_right hlin (le_of_lt hlog2pos)
  have hcombine : 6 * Real.log 2 + Real.log 256 +
      (((2 * (n : ℝ) + 1) + 1) / 24) * S2967Qconst ≤
      (14 + 30 * (((2 * (n : ℝ) + 1) + 1) / 24)) * Real.log 2 := by
    rw [hlog256]
    nlinarith [hQ2]
  linarith

/-- The target inequality holds at the ABC triple `(1, 1, 2)`, for every `n`.
This shows the reduced statement is not vacuous. -/
theorem S2965_target_at_one_one_two (n : Nat) :
    6 * Real.log (2 : ℝ) + Real.log 256 ≤
      ((2 * (n : ℝ) + 1) + 5) / 4 * S2921D -
        ((2 * (n : ℝ) + 1) + 1) / 24 * S2921Q 1 1 2 +
        S2921S 1 1 2 + ((2 * (n : ℝ) + 1) + 5) * S2921T 1 1 2 := by
  rw [S2965_linear_eq n 1 1 2]
  have hS := S2965_S_one_one_two_ge
  have hc : S2965Kappa n * Real.log 2 ≤ S2965Kappa n * S2921S 1 1 2 :=
    mul_le_mul_of_nonneg_left hS (le_of_lt (S2965_kappa_pos n))
  linarith [S2965_const_bound n, hc]

/-- Non-vacuity in existential form. -/
theorem S2965_exists_satisfying_triple (n : Nat) :
    ∃ a b c : Nat, IsABCTriple a b c ∧
      6 * Real.log (c : ℝ) + Real.log 256 ≤
        ((2 * (n : ℝ) + 1) + 5) / 4 * S2921D -
          ((2 * (n : ℝ) + 1) + 1) / 24 * S2921Q a b c +
          S2921S a b c + ((2 * (n : ℝ) + 1) + 5) * S2921T a b c :=
  ⟨1, 1, 2, S2965_isABCTriple_one_one_two, S2965_target_at_one_one_two n⟩

/-!
## 9. Exact first error (no fake, no new assumption)

Available, unconditionally:

* `S2921D = 0` (Section 1);
* `S2921Q a b c = c0 + S2921S a b c` and `S2921T a b c = 5 * S2921S a b c`
  with `c0 = S2967Qconst = log(5*5*2161*2161)` (Section 2);
* `log rad(a b c) <= S2921S a b c <= 2 * log rad(a b c)` (Section 4/5).

Consequently `S2965MinimalLinear n` is equivalent to

  `kappa n * S2921S a b c >= 6 log c + log 256 + ((n+1)/12) * c0`,

with `kappa n = (119 n + 371)/12` (so `kappa n >= 490/12 > 40.8` for `n >= 1`).
The only available lower bound is `S2921S >= log rad(a b c)`, which yields the
sufficient radical inequality `S2965RadicalLower n`, i.e. exactly an ABC
logarithmic bound with exponent

  `1 + epsilon = kappa n / 6 >= 490/72 > 6.8`  (at `n = 1`, `6.8055...`),

against the specific constant `-(log 256 + ((n+1)/12) c0)/6
= -(5.545 + 3.096)/6 = -1.440` at `n = 1` (`c0 = log 116748025 = 18.576`).
Equivalently, it is the uniform quality bound

  `quality := log c / log rad(a b c) <= ~6.8`  (`n = 1`; `~1.65 n` in general).

The target implies the same shape with exponent `kappa n / 3` (Section 5), so up
to the factor `2` between the two available bounds on `S2921S` the target *is*
a uniform bound on the ABC quality.

Moreover the family is monotone in `n` (Section 4b):
`S2965MinimalLinear 1` implies `S2965MinimalLinear n` for every `n >= 1`.
The reason is that the coefficient of `S` and the negative constant part both
grow linearly in `n` with the same slope: `kappa n - kappa 1
= 119 (n-1)/12` and `(2n+2)/24 - 4/24 = (n-1)/12`, so the difference of the two
linear forms is `((n-1)/12) * (119 S - c0) >= 0` because
`119 S >= 119 log 2 >= 30 log 2 >= c0`.  Hence it is enough to decide the single
case `n = 1`.

**Missing input.** No uniform lower bound of `log c` in terms of `log rad` is
available anywhere in the tree: `LeanFormal.IUT.ABCConjecture` is a `def`
without proof, and the radical arithmetic (`natRadical_pos`, `natRadical_dvd_self`,
`natRadical_mul_of_coprime`, ...) gives only `log rad >= 0` (`>= log 2` for a
triple).  A uniform quality bound is strictly weaker than the ABC conjecture but
is not known unconditionally (the record quality is `~1.63`); it is *not*
derivable from `rad | a b c` or from the height comparisons in
`ABCInvariantHeight`, whose inequalities are
`6 log c + log(27/64) <= logHeight <= 6 log c + log 256` and have the opposite
direction (they bound the height *by* `log c`, not `log c` by `log rad`).

**Direction mismatch (recorded, not used).** `S2921_hweightvol_candidate`
(`arithmeticWeight <= Q`) multiplies a negative coefficient, so it gives an
upper bound on the target right-hand side (`S2965_linear_le_weight_form`),
hence cannot establish the required lower bound.

Therefore this attempt closes the *reduction* but not the target: replacing the
target by `S2965SLogLower n` (or by `S2965RadicalLower n` / the ABC
logarithmic bound above) is exact, and the residual gap is the single missing
arithmetic inequality
`kappa n * log rad(a b c) >= 6 log c + log 256 + ((n+1)/12) c0`.
-/

#check S2965_finrank_eq_one
#check S2965_D_eq_zero
#check S2965_kappa_one
#check S2965_Q_eq_const_add_S
#check S2965_T_eq_five_mul_S
#check S2965_kappa_pos
#check S2965_linear_eq
#check S2965SLogLower
#check S2965_minimal_iff_SLogLower
#check S2965_weight_le_S
#check S2965RadicalLower
#check S2965MinimalLinear_of_radical
#check S2965_radicalLower_iff_natRadical
#check S2965_radicalLower_iff_ABCLogBound
#check S2965_S_le_two_weight
#check S2965_ABCLogBound_of_minimal
#check S2965_linear_le_weight_form
#check S2965MinimalLinear_implies_heightLeProcession
#check S2965_target_at_one_one_two
#check S2965_exists_satisfying_triple
#check S2965_weight_ge_log_two
#check S2965_linearForm_one_le
#check S2965MinimalLinear_of_one
#print axioms S2965_D_eq_zero
#print axioms S2965_linear_eq
#print axioms S2965_minimal_iff_SLogLower
#print axioms S2965MinimalLinear_of_radical
#print axioms S2965_radicalLower_iff_ABCLogBound
#print axioms S2965_ABCLogBound_of_minimal
#print axioms S2965MinimalLinear_implies_heightLeProcession
#print axioms S2965_target_at_one_one_two
#print axioms S2965_S_le_two_weight
#print axioms S2965_exists_satisfying_triple
#print axioms S2965_linearForm_one_le
#print axioms S2965MinimalLinear_of_one

end LeanFormal.IUT.XiFPaper.S2965MinimalAttemptActual
end
