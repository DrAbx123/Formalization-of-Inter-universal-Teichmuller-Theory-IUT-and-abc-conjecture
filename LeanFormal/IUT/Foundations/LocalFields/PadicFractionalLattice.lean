import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellLattice
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Fractional norm lattices in a finite p-adic local field

For a real exponent `a`, the closed norm ball of radius `p^{-a}` is a
`Zp`-submodule of the local field. These are the norm-ball models of the
fractional lattices `p^a R` used in IUT IV Proposition 1.2. The integer
shift is realized by an explicit power of `p`; no fractional-ideal API is
introduced here.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.FinitePadicIntegralLattice LeanFormal.IUT.LocalFieldIntegralUnits
open scoped LeanFormal.IUT.FinitePadicIntegralLattice

noncomputable section

section RealPrimePowers

variable {p : ℕ} [Fact p.Prime]

/-- The reciprocal prime power cancels a positive integer shift. -/
theorem real_rpow_neg_int_mul_rpow_neg (a : ℝ) (k : ℤ) :
    (p : ℝ) ^ (-(k : ℝ)) * (p : ℝ) ^ (-a) =
      (p : ℝ) ^ (-(a + (k : ℝ))) := by
  have hp : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  rw [← Real.rpow_add hp]
  congr 1
  ring

/-- The prime power cancels a negative integer shift. -/
theorem real_rpow_int_mul_rpow_neg_add (a : ℝ) (k : ℤ) :
    (p : ℝ) ^ (k : ℝ) * (p : ℝ) ^ (-(a + (k : ℝ))) =
      (p : ℝ) ^ (-a) := by
  have hp : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  rw [← Real.rpow_add hp]
  congr 1
  ring

/-- The reciprocal prime powers multiply by adding the exponents. -/
theorem real_rpow_neg_mul_neg (a b : ℝ) :
    (p : ℝ) ^ (-a) * (p : ℝ) ^ (-b) =
      (p : ℝ) ^ (-(a + b)) := by
  have hp : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  rw [← Real.rpow_add hp]
  congr 1
  ring

end RealPrimePowers

section LocalField

variable {K : Type*} [NormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] K]

/-- The norm-ball lattice `{x | ‖x‖ ≤ p^{-a}}` with its actual `Zp` action. -/
def padicFractionalLattice (a : ℝ) : Submodule ℤ_[p] K where
  carrier := {x : K | ‖x‖ ≤ (p : ℝ) ^ (-a)}
  zero_mem' := by
    change ‖(0 : K)‖ ≤ (p : ℝ) ^ (-a)
    rw [norm_zero]
    exact Real.rpow_nonneg (by positivity) _
  add_mem' := by
    intro x y hx hy
    exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  smul_mem' := by
    intro z x hx
    change ‖(z : ℚ_[p]) • x‖ ≤ (p : ℝ) ^ (-a)
    rw [norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg x) z.property).trans hx

theorem mem_padicFractionalLattice_iff (a : ℝ) (x : K) :
    x ∈ padicFractionalLattice (p := p) (K := K) a ↔
      ‖x‖ ≤ (p : ℝ) ^ (-a) := Iff.rfl

/-- The zero fractional lattice is the actual valuation-integer lattice. -/
theorem padicFractionalLattice_zero :
    padicFractionalLattice (p := p) (K := K) 0 =
      valuationIntegerLattice (p := p) (K := K) := by
  ext x
  change (‖x‖ ≤ (p : ℝ) ^ (-(0 : ℝ))) ↔ x ∈ Integers K
  rw [mem_integers_iff]
  simp

/-- A larger exponent gives a smaller norm-ball lattice. -/
theorem padicFractionalLattice_antitone {a b : ℝ} (hab : a ≤ b) :
    padicFractionalLattice (p := p) (K := K) b ≤
      padicFractionalLattice (p := p) (K := K) a := by
  intro x hx
  rw [mem_padicFractionalLattice_iff] at hx ⊢
  exact hx.trans (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt.le) (neg_le_neg hab))

section SubmoduleProduct

local instance padicFractionalZpAlgebra : Algebra ℤ_[p] K :=
  Algebra.restrictScalars ℤ_[p] ℚ_[p] K

/-- The product of an element of `F a` and an element of `F b` lies in
`F (a + b)`. This is the local pure-factor form of fractional-lattice
multiplication. -/
theorem padicFractionalLattice_mul_mem {a b : ℝ} {x y : K}
    (hx : x ∈ padicFractionalLattice (p := p) (K := K) a)
    (hy : y ∈ padicFractionalLattice (p := p) (K := K) b) :
    x * y ∈ padicFractionalLattice (p := p) (K := K) (a + b) := by
  rw [mem_padicFractionalLattice_iff] at hx hy ⊢
  have hp : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  rw [norm_mul]
  calc
    ‖x‖ * ‖y‖ ≤ (p : ℝ) ^ (-a) * (p : ℝ) ^ (-b) :=
      mul_le_mul hx hy (norm_nonneg y) (Real.rpow_nonneg hp.le _)
    _ = (p : ℝ) ^ (-(a + b)) := by
      rw [← Real.rpow_add hp]
      congr 1
      ring

/-- Multiplication of fractional norm-ball lattices is contained in the
norm-ball lattice with the summed exponent. -/
theorem padicFractionalLattice_mul_le (a b : ℝ) :
    padicFractionalLattice (p := p) (K := K) a *
        padicFractionalLattice (p := p) (K := K) b ≤
      padicFractionalLattice (p := p) (K := K) (a + b) := by
  rw [Submodule.mul_le]
  intro x hx y hy
  exact padicFractionalLattice_mul_mem hx hy

/-- An exact fractional generator: an element whose norm is precisely the
radius of `F a`. For an exponent in the local value group this is the
uniformizer power that realizes the corresponding principal fractional
ideal inside the value-group grading. -/
def HasExactFractionalGenerator (a : ℝ) : Prop :=
  ∃ c : K, ‖c‖ = (p : ℝ) ^ (-a)

omit [IsUltrametricDist K] [NormedAlgebra ℚ_[p] K] in
/-- An exact fractional generator has nonzero norm, hence is nonzero. -/
theorem padicFractionalLattice_exactGenerator_ne_zero {a : ℝ} {c : K}
    (hc : ‖c‖ = (p : ℝ) ^ (-a)) : c ≠ 0 := by
  have hp : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hpos : 0 < (p : ℝ) ^ (-a) := Real.rpow_pos_of_pos hp _
  intro hzero
  have hz : (0 : ℝ) = (p : ℝ) ^ (-a) := by simpa [hzero] using hc
  exact hpos.ne' hz.symm

omit [IsUltrametricDist K] [NormedAlgebra ℚ_[p] K] in
/-- Exact fractional generators are closed under multiplication, with the
exponents adding. -/
theorem HasExactFractionalGenerator.add {a b : ℝ}
    (ha : HasExactFractionalGenerator (p := p) (K := K) a)
    (hb : HasExactFractionalGenerator (p := p) (K := K) b) :
    HasExactFractionalGenerator (p := p) (K := K) (a + b) := by
  rcases ha with ⟨c, hc⟩
  rcases hb with ⟨d, hd⟩
  exact ⟨c * d, by rw [norm_mul, hc, hd, real_rpow_neg_mul_neg]⟩

omit [IsUltrametricDist K] [Fact p.Prime] [NormedAlgebra ℚ_[p] K] in
/-- Exact fractional generators are closed under inversion. -/
theorem HasExactFractionalGenerator.neg {a : ℝ}
    (ha : HasExactFractionalGenerator (p := p) (K := K) a) :
    HasExactFractionalGenerator (p := p) (K := K) (-a) := by
  rcases ha with ⟨c, hc⟩
  refine ⟨c⁻¹, ?_⟩
  rw [norm_inv, hc]
  have hp : (0 : ℝ) ≤ (p : ℝ) := by positivity
  exact (Real.rpow_neg hp (-a)).symm

omit [IsUltrametricDist K] [NormedAlgebra ℚ_[p] K] in
/-- Exact fractional generators are closed under subtraction. -/
theorem HasExactFractionalGenerator.sub {a b : ℝ}
    (ha : HasExactFractionalGenerator (p := p) (K := K) a)
    (hb : HasExactFractionalGenerator (p := p) (K := K) b) :
    HasExactFractionalGenerator (p := p) (K := K) (a - b) := by
  rw [sub_eq_add_neg]
  exact ha.add hb.neg

/-- Given exact generators of `F a` and `F b`, every element of `F (a+b)` is
a single product of an element of `F a` and an element of `F b`. This is the
local principal-fractional-ideal factorization. -/
theorem padicFractionalLattice_exists_mul_of_norm_eq {a b : ℝ} {c d : K}
    (hc : ‖c‖ = (p : ℝ) ^ (-a))
    (hd : ‖d‖ = (p : ℝ) ^ (-b)) {x : K}
    (hx : x ∈ padicFractionalLattice (p := p) (K := K) (a + b)) :
    ∃ u ∈ padicFractionalLattice (p := p) (K := K) a,
      ∃ v ∈ padicFractionalLattice (p := p) (K := K) b, u * v = x := by
  rw [mem_padicFractionalLattice_iff] at hx
  have hp : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hpa : 0 < (p : ℝ) ^ (-a) := Real.rpow_pos_of_pos hp _
  have hpb : 0 < (p : ℝ) ^ (-b) := Real.rpow_pos_of_pos hp _
  have hc_ne : c ≠ 0 := by
    intro hzero
    have hz : (0 : ℝ) = (p : ℝ) ^ (-a) := by simpa [hzero] using hc
    exact hpa.ne' hz.symm
  have hd_ne : d ≠ 0 := by
    intro hzero
    have hz : (0 : ℝ) = (p : ℝ) ^ (-b) := by simpa [hzero] using hd
    exact hpb.ne' hz.symm
  let y : K := (c * d)⁻¹ * x
  have hy_norm : ‖y‖ ≤ 1 := by
    dsimp only [y]
    rw [norm_mul, norm_inv, norm_mul, hc, hd, real_rpow_neg_mul_neg]
    have hpos : 0 < (p : ℝ) ^ (-(a + b)) := Real.rpow_pos_of_pos hp _
    calc
      ((p : ℝ) ^ (-(a + b)))⁻¹ * ‖x‖ ≤
          ((p : ℝ) ^ (-(a + b)))⁻¹ * (p : ℝ) ^ (-(a + b)) :=
        mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hpos.le)
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  have hy_integer : y ∈ valuationIntegerLattice (p := p) (K := K) := by
    change y ∈ Integers K
    exact (mem_integers_iff y).mpr hy_norm
  have hc_mem : c ∈ padicFractionalLattice (p := p) (K := K) a := by
    rw [mem_padicFractionalLattice_iff]
    exact hc.le
  have hv : d * y ∈ padicFractionalLattice (p := p) (K := K) b := by
    rw [mem_padicFractionalLattice_iff]
    rw [norm_mul, hd]
    calc
      (p : ℝ) ^ (-b) * ‖y‖ ≤ (p : ℝ) ^ (-b) * 1 :=
        mul_le_mul_of_nonneg_left hy_norm (Real.rpow_nonneg hp.le _)
      _ = (p : ℝ) ^ (-b) := mul_one _
  refine ⟨c, hc_mem, d * y, hv, ?_⟩
  have hcd_ne : c * d ≠ 0 := mul_ne_zero hc_ne hd_ne
  calc
    c * (d * y) = (c * d) * ((c * d)⁻¹ * x) := by
      dsimp only [y]
      ring
    _ = x := by rw [← mul_assoc, mul_inv_cancel₀ hcd_ne, one_mul]

/-- Exact fractional generators give the local principal fractional-ideal
multiplication equality `F a * F b = F (a+b)`. -/
theorem padicFractionalLattice_mul_eq_of_norm_eq {a b : ℝ} {c d : K}
    (hc : ‖c‖ = (p : ℝ) ^ (-a))
    (hd : ‖d‖ = (p : ℝ) ^ (-b)) :
    padicFractionalLattice (p := p) (K := K) a *
        padicFractionalLattice (p := p) (K := K) b =
      padicFractionalLattice (p := p) (K := K) (a + b) := by
  apply le_antisymm (padicFractionalLattice_mul_le a b)
  intro x hx
  rcases padicFractionalLattice_exists_mul_of_norm_eq hc hd hx with
    ⟨u, hu, v, hv, huv⟩
  rw [← huv]
  exact Submodule.mul_mem_mul hu hv

/-- An exact generator realizes `F a` as the valuation-integer lattice times
the principal `Zp`-line through that generator. This is the correct
`Zp`-form of a principal fractional ideal in a possibly higher-degree local
field; it does not assert that the whole lattice is cyclic over `Zp`. -/
theorem padicFractionalLattice_eq_valuationIntegerLattice_mul_span_of_norm_eq
    {a : ℝ} {c : K} (hc : ‖c‖ = (p : ℝ) ^ (-a)) :
    padicFractionalLattice (p := p) (K := K) a =
      valuationIntegerLattice (p := p) (K := K) *
        Submodule.span ℤ_[p] ({c} : Set K) := by
  have hp : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hpa : 0 < (p : ℝ) ^ (-a) := Real.rpow_pos_of_pos hp _
  have hc_ne : c ≠ 0 := by
    intro hzero
    have hz : (0 : ℝ) = (p : ℝ) ^ (-a) := by simpa [hzero] using hc
    exact hpa.ne' hz.symm
  apply le_antisymm
  · intro x hx
    rw [mem_padicFractionalLattice_iff] at hx
    have hy_norm : ‖c⁻¹ * x‖ ≤ 1 := by
      rw [norm_mul, norm_inv, hc]
      calc
        ((p : ℝ) ^ (-a))⁻¹ * ‖x‖ ≤ ((p : ℝ) ^ (-a))⁻¹ * (p : ℝ) ^ (-a) :=
          mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hpa.le)
        _ = 1 := inv_mul_cancel₀ hpa.ne'
    have hy_integer : c⁻¹ * x ∈ valuationIntegerLattice (p := p) (K := K) := by
      change c⁻¹ * x ∈ Integers K
      exact (mem_integers_iff (c⁻¹ * x)).mpr hy_norm
    have hspan : c ∈ Submodule.span ℤ_[p] ({c} : Set K) :=
      Submodule.subset_span (Set.mem_singleton c)
    have hmem : (c⁻¹ * x) * c ∈
        valuationIntegerLattice (p := p) (K := K) *
          Submodule.span ℤ_[p] ({c} : Set K) :=
      Submodule.mul_mem_mul hy_integer hspan
    have hxc : (c⁻¹ * x) * c = x := by
      rw [mul_comm (c⁻¹ * x) c, ← mul_assoc, mul_inv_cancel₀ hc_ne, one_mul]
    rwa [hxc] at hmem
  · rw [Submodule.mul_le]
    intro r hr s hs
    have hr_norm : ‖r‖ ≤ 1 := by
      change r ∈ Integers K at hr
      exact (mem_integers_iff r).mp hr
    have hspan_le : Submodule.span ℤ_[p] ({c} : Set K) ≤
        padicFractionalLattice (p := p) (K := K) a := by
      apply Submodule.span_le.mpr
      rw [Set.singleton_subset_iff]
      change c ∈ padicFractionalLattice (p := p) (K := K) a
      rw [mem_padicFractionalLattice_iff]
      exact hc.le
    have hs_norm : ‖s‖ ≤ (p : ℝ) ^ (-a) := by
      exact hspan_le hs
    rw [mem_padicFractionalLattice_iff, norm_mul]
    calc
      ‖r‖ * ‖s‖ ≤ 1 * (p : ℝ) ^ (-a) :=
        mul_le_mul hr_norm hs_norm (norm_nonneg _) zero_le_one
      _ = (p : ℝ) ^ (-a) := one_mul _

omit [IsUltrametricDist K] in
/-- The principal `Zp`-line acts on a submodule by left multiplication by
its generator. -/
theorem submodule_span_singleton_mul_eq_map_mulLeft (c : K)
    (N : Submodule ℤ_[p] K) :
    Submodule.span ℤ_[p] ({c} : Set K) * N =
      N.map (LinearMap.mulLeft ℤ_[p] c) := by
  ext x
  rw [Submodule.mem_span_singleton_mul, Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, hzx⟩
    exact ⟨z, hz, hzx⟩
  · rintro ⟨z, hz, hzx⟩
    exact ⟨z, hz, hzx⟩

/-- Exact scalar scaling by an exact fractional generator, provided the
normalization submodule is stable under the valuation-integer lattice. -/
theorem padicFractionalLattice_mul_eq_map_mulLeft_of_norm_eq {a : ℝ} {c : K}
    (hc : ‖c‖ = (p : ℝ) ^ (-a))
    (N : Submodule ℤ_[p] K)
    (hN : valuationIntegerLattice (p := p) (K := K) * N = N) :
    padicFractionalLattice (p := p) (K := K) a * N =
      N.map (LinearMap.mulLeft ℤ_[p] c) := by
  rw [padicFractionalLattice_eq_valuationIntegerLattice_mul_span_of_norm_eq hc]
  calc
    (valuationIntegerLattice (p := p) (K := K) *
        Submodule.span ℤ_[p] ({c} : Set K)) * N =
        Submodule.span ℤ_[p] ({c} : Set K) * N := by
      calc
        (valuationIntegerLattice (p := p) (K := K) *
            Submodule.span ℤ_[p] ({c} : Set K)) * N =
            valuationIntegerLattice (p := p) (K := K) *
              (Submodule.span ℤ_[p] ({c} : Set K) * N) :=
          mul_assoc _ _ _
        _ = valuationIntegerLattice (p := p) (K := K) *
              (N * Submodule.span ℤ_[p] ({c} : Set K)) := by
          rw [Submodule.mul_comm (Submodule.span ℤ_[p] ({c} : Set K)) N]
        _ = (valuationIntegerLattice (p := p) (K := K) * N) *
              Submodule.span ℤ_[p] ({c} : Set K) :=
          (mul_assoc _ _ _).symm
        _ = N * Submodule.span ℤ_[p] ({c} : Set K) := by rw [hN]
        _ = Submodule.span ℤ_[p] ({c} : Set K) * N :=
          Submodule.mul_comm N (Submodule.span ℤ_[p] ({c} : Set K))
    _ = N.map (LinearMap.mulLeft ℤ_[p] c) :=
      submodule_span_singleton_mul_eq_map_mulLeft c N

omit [IsUltrametricDist K] in
/-- Multiplying the principal line of `c` into an already `c`-scaled
submodule is the same as scaling the product by `c`. -/
theorem submodule_mul_map_mulLeft (P N : Submodule ℤ_[p] K) (c : K) :
    P * (N.map (LinearMap.mulLeft ℤ_[p] c)) =
      (P * N).map (LinearMap.mulLeft ℤ_[p] c) := by
  apply le_antisymm
  · rw [Submodule.mul_eq_span_mul_set P (N.map (LinearMap.mulLeft ℤ_[p] c))]
    apply Submodule.span_le.mpr
    rintro z ⟨r, hr, q, hq, rfl⟩
    rcases Submodule.mem_map.mp hq with ⟨n, hn, rfl⟩
    exact Submodule.mem_map.mpr
      ⟨r * n, Submodule.mul_mem_mul hr hn,
        by simp only [LinearMap.mulLeft_apply]; ring⟩
  · rw [Submodule.mul_eq_span_mul_set P N, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro z ⟨w, hw, rfl⟩
    rcases hw with ⟨r, hr, n, hn, rfl⟩
    have hmem : r * (c * n) ∈ P * (N.map (LinearMap.mulLeft ℤ_[p] c)) :=
      Submodule.mul_mem_mul hr (Submodule.mem_map.mpr ⟨n, hn, rfl⟩)
    change (c : K) * (r * n) ∈ P * (N.map (LinearMap.mulLeft ℤ_[p] c))
    simpa only [mul_left_comm] using hmem

/-- Unconditional exact scalar scaling: the fractional lattice scales
`R * N` by the exact generator, without assuming `R`-stability of `N`. -/
theorem padicFractionalLattice_mul_eq_map_mulLeft_of_norm_eq_unstable
    {a : ℝ} {c : K} (hc : ‖c‖ = (p : ℝ) ^ (-a))
    (N : Submodule ℤ_[p] K) :
    padicFractionalLattice (p := p) (K := K) a * N =
      ((valuationIntegerLattice (p := p) (K := K)) * N).map
        (LinearMap.mulLeft ℤ_[p] c) := by
  rw [padicFractionalLattice_eq_valuationIntegerLattice_mul_span_of_norm_eq hc]
  calc
    (valuationIntegerLattice (p := p) (K := K) *
        Submodule.span ℤ_[p] ({c} : Set K)) * N =
        valuationIntegerLattice (p := p) (K := K) *
          (Submodule.span ℤ_[p] ({c} : Set K) * N) :=
      mul_assoc _ _ _
    _ = valuationIntegerLattice (p := p) (K := K) *
          (N.map (LinearMap.mulLeft ℤ_[p] c)) := by
      rw [submodule_span_singleton_mul_eq_map_mulLeft]
    _ = (valuationIntegerLattice (p := p) (K := K) * N).map
          (LinearMap.mulLeft ℤ_[p] c) :=
      submodule_mul_map_mulLeft _ _ _

/-- A nonnegative fractional exponent gives a lattice contained in the
valuation-integer lattice. -/
theorem padicFractionalLattice_le_valuationIntegerLattice_of_nonneg {a : ℝ}
    (ha : 0 ≤ a) :
    padicFractionalLattice (p := p) (K := K) a ≤
      valuationIntegerLattice (p := p) (K := K) := by
  intro x hx
  rw [mem_padicFractionalLattice_iff] at hx
  change x ∈ Integers K
  rw [mem_integers_iff]
  exact hx.trans (Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt.le) (neg_nonpos.mpr ha))

/-- Multiplying a fractional lattice by the valuation-integer lattice does
not enlarge it. This holds for every real exponent, not only nonnegative
ones. -/
theorem padicFractionalLattice_mul_valuationIntegerLattice_le (a : ℝ) :
    padicFractionalLattice (p := p) (K := K) a *
        valuationIntegerLattice (p := p) (K := K) ≤
      padicFractionalLattice (p := p) (K := K) a := by
  simpa [padicFractionalLattice_zero] using
    padicFractionalLattice_mul_le (p := p) (K := K) a 0

/-- For a nonnegative exponent, multiplying `F a` by the valuation-integer
lattice remains inside the valuation-integer lattice. -/
theorem padicFractionalLattice_mul_valuationIntegerLattice_le_valuationInteger_of_nonneg
    {a : ℝ} (ha : 0 ≤ a) :
    padicFractionalLattice (p := p) (K := K) a *
        valuationIntegerLattice (p := p) (K := K) ≤
      valuationIntegerLattice (p := p) (K := K) :=
  (padicFractionalLattice_mul_valuationIntegerLattice_le
    (p := p) (K := K) a).trans
      (padicFractionalLattice_le_valuationIntegerLattice_of_nonneg ha)

/-- A `Zp`-submodule stable under multiplication by the valuation integers
is stable under multiplication by every nonnegative fractional lattice. -/
theorem padicFractionalLattice_mul_le_of_mul_valuationInteger_le
    {U : Submodule ℤ_[p] K}
    (hU : valuationIntegerLattice (p := p) (K := K) * U ≤ U)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    padicFractionalLattice (p := p) (K := K) θ * U ≤ U :=
  (mul_le_mul' (padicFractionalLattice_le_valuationIntegerLattice_of_nonneg hθ)
    le_rfl).trans hU

end SubmoduleProduct

omit [IsUltrametricDist K] in
/-- The normalized norm sends the rational prime to its inverse. -/
theorem norm_prime_eq_inv :
    ‖(p : K)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] K) p, norm_algebraMap', Padic.norm_p]

omit [IsUltrametricDist K] in
/-- The norm of every integral power of the prime. -/
theorem norm_prime_zpow (k : ℤ) :
    ‖(p : K) ^ k‖ = (p : ℝ) ^ (-(k : ℝ)) := by
  rw [norm_zpow, norm_prime_eq_inv, inv_zpow', ← Real.rpow_intCast]
  congr 1
  norm_cast

/-- Multiplication by an integral power of the prime, as a `Zp`-linear
endomorphism of the local field. -/
def padicPrimeZpowLinearMap (k : ℤ) : K →ₗ[ℤ_[p]] K :=
  (LinearMap.mulLeft ℚ_[p] ((p : K) ^ k)).restrictScalars ℤ_[p]

omit [IsUltrametricDist K] in
@[simp] theorem padicPrimeZpowLinearMap_apply (k : ℤ) (x : K) :
    padicPrimeZpowLinearMap (p := p) (K := K) k x = (p : K) ^ k * x := by
  simp [padicPrimeZpowLinearMap]

omit [IsUltrametricDist K] in
/-- Every integer exponent admits an exact fractional generator, namely the
corresponding integral power of the prime. -/
theorem padicFractionalLattice_hasExactFractionalGenerator_intCast (k : ℤ) :
    HasExactFractionalGenerator (p := p) (K := K) (k : ℝ) :=
  ⟨(p : K) ^ k, norm_prime_zpow (p := p) (K := K) k⟩

section Compact

variable [ProperSpace K]

/-- A nonnegative fractional exponent gives a compact norm-ball lattice. -/
theorem isCompact_padicFractionalLattice_of_nonneg (a : ℝ) (_ha : 0 ≤ a) :
    IsCompact (padicFractionalLattice (p := p) (K := K) a : Set K) := by
  have hset : (padicFractionalLattice (p := p) (K := K) a : Set K) =
      Metric.closedBall (0 : K) ((p : ℝ) ^ (-a)) := by
    ext x
    change x ∈ padicFractionalLattice (p := p) (K := K) a ↔
      x ∈ Metric.closedBall (0 : K) ((p : ℝ) ^ (-a))
    rw [mem_padicFractionalLattice_iff, Metric.mem_closedBall, dist_zero_right]
  rw [hset]
  exact isCompact_closedBall 0 _

section Finite

variable [FiniteDimensional ℚ_[p] K]

theorem finite_padicFractionalLattice_of_nonneg (a : ℝ) (ha : 0 ≤ a) :
    Module.Finite ℤ_[p] (padicFractionalLattice (p := p) (K := K) a) :=
  finite_of_isCompact (p := p) _
    (isCompact_padicFractionalLattice_of_nonneg (p := p) (K := K) a ha)

theorem free_padicFractionalLattice_of_nonneg (a : ℝ) (ha : 0 ≤ a) :
    Module.Free ℤ_[p] (padicFractionalLattice (p := p) (K := K) a) :=
  free_of_isCompact (p := p) _
    (isCompact_padicFractionalLattice_of_nonneg (p := p) (K := K) a ha)

end Finite

end Compact

section IntegerShift

variable [CharZero K]

/-- Integer exponent shift of a fractional lattice, realized by `p^k`. -/
theorem mem_padicFractionalLattice_add_int_iff (a : ℝ) (k : ℤ) (x : K) :
    x ∈ padicFractionalLattice (p := p) (K := K) (a + (k : ℝ)) ↔
      ∃ y ∈ padicFractionalLattice (p := p) (K := K) a,
        (p : K) ^ k * y = x := by
  have hpK : (p : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero
  have hp_pos : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  constructor
  · intro hx
    refine ⟨(p : K) ^ (-k) * x, ?_, ?_⟩
    · rw [mem_padicFractionalLattice_iff] at hx ⊢
      rw [norm_mul, norm_prime_zpow]
      have hneg : -(((-k : ℤ) : ℝ)) = (k : ℝ) := by
        rw [Int.cast_neg]
        exact neg_neg _
      rw [hneg]
      calc
        (p : ℝ) ^ (k : ℝ) * ‖x‖ ≤
            (p : ℝ) ^ (k : ℝ) * (p : ℝ) ^ (-(a + (k : ℝ))) :=
          mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hp_pos.le _)
        _ = (p : ℝ) ^ (-a) := real_rpow_int_mul_rpow_neg_add a k
    · rw [← mul_assoc, ← zpow_add₀ hpK]
      simp
  · rintro ⟨y, hy, rfl⟩
    rw [mem_padicFractionalLattice_iff] at hy ⊢
    rw [norm_mul, norm_prime_zpow]
    calc
      (p : ℝ) ^ (-(k : ℝ)) * ‖y‖ ≤
          (p : ℝ) ^ (-(k : ℝ)) * (p : ℝ) ^ (-a) :=
        mul_le_mul_of_nonneg_left hy (Real.rpow_nonneg hp_pos.le _)
      _ = (p : ℝ) ^ (-(a + (k : ℝ))) := real_rpow_neg_int_mul_rpow_neg a k

/-- For an integer exponent the fractional lattice is the image of the
valuation-integer lattice under multiplication by `p^k`. -/
theorem padicFractionalLattice_intCast_eq_map (k : ℤ) :
    padicFractionalLattice (p := p) (K := K) (k : ℝ) =
      (valuationIntegerLattice (p := p) (K := K)).map
        (padicPrimeZpowLinearMap (p := p) (K := K) k) := by
  ext x
  rw [Submodule.mem_map]
  have hshift := mem_padicFractionalLattice_add_int_iff (p := p) (K := K) 0 k x
  rw [zero_add, padicFractionalLattice_zero] at hshift
  constructor
  · intro hx
    rcases hshift.mp hx with ⟨y, hy, hyx⟩
    exact ⟨y, hy, by simpa using hyx⟩
  · rintro ⟨y, hy, hyx⟩
    exact hshift.mpr ⟨y, hy, by simpa using hyx⟩

end IntegerShift

end LocalField

end

end LeanFormal.IUT.LocalFieldLogarithm


#print axioms LeanFormal.IUT.LocalFieldLogarithm.real_rpow_neg_int_mul_rpow_neg
#print axioms LeanFormal.IUT.LocalFieldLogarithm.real_rpow_int_mul_rpow_neg_add
#print axioms LeanFormal.IUT.LocalFieldLogarithm.padicFractionalLattice
#print axioms LeanFormal.IUT.LocalFieldLogarithm.mem_padicFractionalLattice_iff
#print axioms LeanFormal.IUT.LocalFieldLogarithm.padicFractionalLattice_zero
#print axioms LeanFormal.IUT.LocalFieldLogarithm.padicFractionalLattice_antitone
#print axioms LeanFormal.IUT.LocalFieldLogarithm.norm_prime_eq_inv
#print axioms LeanFormal.IUT.LocalFieldLogarithm.norm_prime_zpow
#print axioms LeanFormal.IUT.LocalFieldLogarithm.isCompact_padicFractionalLattice_of_nonneg
#print axioms LeanFormal.IUT.LocalFieldLogarithm.finite_padicFractionalLattice_of_nonneg
#print axioms LeanFormal.IUT.LocalFieldLogarithm.free_padicFractionalLattice_of_nonneg
#print axioms LeanFormal.IUT.LocalFieldLogarithm.mem_padicFractionalLattice_add_int_iff
