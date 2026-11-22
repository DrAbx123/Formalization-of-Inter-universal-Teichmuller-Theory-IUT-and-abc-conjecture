import LeanFormal.IUT.Foundations.LocalFields.PadicFractionalLattice
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIntegralLogTensorLattice
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIntegerTensorComparison

/-!
# Fractional tensor lattices at a tuple of finite places

The local fractional norm-ball lattices are assembled by the actual `Zp`
span of their pure tensors. The zero exponent recovers the existing
valuation-integer tensor lattice.

An integer shift `a i + k` multiplies every local factor by the same power
of the common prime. It is therefore the lattice `F (a + k * 1)`, not a
base-field scalar multiple `p^k * F a`. In particular, the common-prime
pure tensor `arithmeticTupleCommonPrimePower k` has total exponent
`k * card ι`, and the constant-exponent lattice has total exponent
`card ι * lambda`; neither is the paper's single-total-exponent `p^lambda`.

The element chain of Proposition 1.2(ii) uses actual pure elements
`alpha = tensor_i alpha_i`, not a lattice-level `p^lambda`. The lemmas below
therefore identify the fractional tensor with `R_I` times the principal line
of such a pure element (`...eq_valuationInteger_mul_span_of_norm_eq`) and
compute the action of that element on a normalization submodule
(`...mul_eq_map_mulLeft_of_exact_generators`). No lattice-level sum-exponent
equality `F a = p^{sum a}` and no `N`-level bridge
`F a * N = E (sum a) * N` is asserted; the latter is not valid in general
(guidance 12.14). A general tuple of local exponents is also not determined
by its sum: already for two `Qp` factors, `F (1, 1)` is `pR tensor pR`,
whereas the single-coordinate lattice with total exponent `2` is
`p^2 R tensor R`.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldPadicTensor LeanFormal.IUT.LocalFieldLogarithm
  LeanFormal.IUT.LocalFieldIntegralUnits
open scoped LeanFormal.IUT.FinitePadicIntegralLattice Pointwise

noncomputable section

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type*} [Fintype ι] {V : ι → Type*}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)

/-- The fractional tensor lattice with local exponents `a i`. -/
abbrev arithmeticTupleFractionalLattice (a : ι → ℝ) : Submodule ℤ_[p]
    (ArithmeticTensorTupleBlock places tuple) :=
  submoduleTensorSpan (p := p)
    (fun i => CommonPrimeCompletion (places i (tuple i)))
    (fun i => padicFractionalLattice (p := p)
      (K := CommonPrimeCompletion (places i (tuple i))) (a i))

/-- The zero fractional tensor lattice is the valuation-integer tensor. -/
theorem arithmeticTupleFractionalLattice_zero :
    arithmeticTupleFractionalLattice places tuple (fun _ => 0) =
      arithmeticTupleValuationIntegerLattice places tuple := by
  simp only [arithmeticTupleFractionalLattice, arithmeticTupleValuationIntegerLattice,
    tensorIntegerLattice]
  congr 1
  funext i
  exact padicFractionalLattice_zero

section SingleCoordinate

variable [DecidableEq ι]

/-- The exponent vector supported at one tensor coordinate. -/
def arithmeticTupleSingleFractionalExponent (iSelected : ι) (a : ℝ) : ι → ℝ :=
  fun i => if i = iSelected then a else 0

omit [Fintype ι] in
@[simp] theorem arithmeticTupleSingleFractionalExponent_same
    (iSelected : ι) (a : ℝ) :
    arithmeticTupleSingleFractionalExponent iSelected a iSelected = a := by
  simp [arithmeticTupleSingleFractionalExponent]

omit [Fintype ι] in
@[simp] theorem arithmeticTupleSingleFractionalExponent_ne
    {i iSelected : ι} (hi : i ≠ iSelected) (a : ℝ) :
    arithmeticTupleSingleFractionalExponent iSelected a i = 0 := by
  simp [arithmeticTupleSingleFractionalExponent, hi]

/-- The fractional tensor lattice with a fractional exponent at one tensor
coordinate and zero exponent at all the others. This is the one-factor
principal model; it is not by itself a lattice-level `p^lambda` for Step (v),
because a general tuple lattice is not determined by its total exponent. -/
abbrev arithmeticTupleSingleFractionalLattice (iSelected : ι) (a : ℝ) :
    Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple) :=
  arithmeticTupleFractionalLattice places tuple
    (arithmeticTupleSingleFractionalExponent iSelected a)

/-- The pure tensor with one chosen local element at `iSelected` and `1` in every
other factor. -/
abbrev arithmeticTupleSingleFractionalGenerator (iSelected : ι)
    (c : CommonPrimeCompletion (places iSelected (tuple iSelected))) :
    ArithmeticTensorTupleBlock places tuple :=
  finitePadicTensorTprod (p := p)
    (fun i => CommonPrimeCompletion (places i (tuple i)))
    (Pi.mulSingle iSelected c)

end SingleCoordinate

/-- The pure product of a family of chosen local exact generators. Its local
fractional exponents add, so its total exponent is the sum of the local
exponents. It is a pure tensor in the tensor algebra, not a `Qp`-scalar. -/
abbrev arithmeticTupleFractionalPureGenerator
    (c : (i : ι) → CommonPrimeCompletion (places i (tuple i))) :
    ArithmeticTensorTupleBlock places tuple :=
  finitePadicTensorTprod (p := p)
    (fun i => CommonPrimeCompletion (places i (tuple i))) c

/-- A larger tuple of exponents gives a smaller fractional tensor lattice. -/
theorem arithmeticTupleFractionalLattice_mono {a b : ι → ℝ}
    (hab : ∀ i, a i ≤ b i) :
    arithmeticTupleFractionalLattice places tuple b ≤
      arithmeticTupleFractionalLattice places tuple a := by
  unfold arithmeticTupleFractionalLattice submoduleTensorSpan tensorIntegralRegion
  apply Submodule.span_mono
  rintro z ⟨x, hx, rfl⟩
  exact ⟨x, fun i _ => padicFractionalLattice_antitone (hab i) (hx i (Set.mem_univ i)), rfl⟩

/-- A pure tensor with every local coordinate in the fractional lattice. -/
theorem arithmeticTupleFractionalLattice_pure_tensor_mem
    (a : ι → ℝ) (x : (i : ι) → CommonPrimeCompletion (places i (tuple i)))
    (hx : ∀ i, x i ∈ padicFractionalLattice (p := p)
      (K := CommonPrimeCompletion (places i (tuple i))) (a i)) :
    finitePadicTensorTprod (p := p) (fun i => CommonPrimeCompletion (places i (tuple i))) x ∈
      arithmeticTupleFractionalLattice places tuple a := by
  unfold arithmeticTupleFractionalLattice submoduleTensorSpan tensorIntegralRegion
  exact Submodule.subset_span ⟨x, fun i _ => hx i, rfl⟩

/-- The fractional tensor is contained in the integral log-shell tensor when
every local fractional lattice is contained in the local log-shell. -/
theorem arithmeticTupleFractionalLattice_le_integralLogLattice
    (a : ι → ℝ)
    (h : ∀ i, padicFractionalLattice (p := p)
      (K := CommonPrimeCompletion (places i (tuple i))) (a i) ≤
      integralLogShellLattice (K := CommonPrimeCompletion (places i (tuple i))) (p := p)) :
    arithmeticTupleFractionalLattice places tuple a ≤
      arithmeticTupleIntegralLogLattice places tuple := by
  unfold arithmeticTupleFractionalLattice submoduleTensorSpan arithmeticTupleIntegralLogLattice
    tensorLogShellLattice tensorIntegralRegion tensorLogShellRegion
  apply Submodule.span_mono
  rintro z ⟨x, hx, rfl⟩
  exact ⟨x, fun i _ => h i (hx i (Set.mem_univ i)), rfl⟩

section SubmoduleProduct

local instance arithmeticTupleFractionalZpAlgebra :
    Algebra ℤ_[p] (ArithmeticTensorTupleBlock places tuple) :=
  Algebra.restrictScalars ℤ_[p] ℚ_[p] (ArithmeticTensorTupleBlock places tuple)

omit [Fintype ι] in
set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- Multiplication of pure tensors is the pure tensor of the coordinatewise
products. This is the tensor-level pure-factor lemma used below. -/
theorem finitePadicTensorTprod_mul_tprod
    (x y : (i : ι) → CommonPrimeCompletion (places i (tuple i))) :
    finitePadicTensorTprod (p := p)
        (fun i => CommonPrimeCompletion (places i (tuple i))) x *
      finitePadicTensorTprod (p := p)
        (fun i => CommonPrimeCompletion (places i (tuple i))) y =
    finitePadicTensorTprod (p := p)
      (fun i => CommonPrimeCompletion (places i (tuple i)))
      (fun i => x i * y i) := by
  exact PiTensorProduct.tprod_mul_tprod x y

/-- A pure tensor whose coordinates lie in the local fractional lattices
belongs to the fractional tensor lattice. -/
theorem arithmeticTupleFractionalLattice_pure_tensor_mul_mem
    (a b : ι → ℝ)
    (x y : (i : ι) → CommonPrimeCompletion (places i (tuple i)))
    (hx : ∀ i, x i ∈ padicFractionalLattice (p := p)
      (K := CommonPrimeCompletion (places i (tuple i))) (a i))
    (hy : ∀ i, y i ∈ padicFractionalLattice (p := p)
      (K := CommonPrimeCompletion (places i (tuple i))) (b i)) :
    finitePadicTensorTprod (p := p)
        (fun i => CommonPrimeCompletion (places i (tuple i))) x *
      finitePadicTensorTprod (p := p)
        (fun i => CommonPrimeCompletion (places i (tuple i))) y ∈
      arithmeticTupleFractionalLattice places tuple (fun i => a i + b i) := by
  rw [finitePadicTensorTprod_mul_tprod]
  exact arithmeticTupleFractionalLattice_pure_tensor_mem places tuple
    (fun i => a i + b i) (fun i => x i * y i)
    (fun i => padicFractionalLattice_mul_mem (hx i) (hy i))

/-- The tensor fractional lattices multiply into the fractional lattice with
the summed exponent. Only the `≤` direction is asserted: arbitrary real
exponents are rounded by the norm balls, so equality is not available at
this level without an exact-generator hypothesis. -/
theorem arithmeticTupleFractionalLattice_mul_le (a b : ι → ℝ) :
    arithmeticTupleFractionalLattice places tuple a *
        arithmeticTupleFractionalLattice places tuple b ≤
      arithmeticTupleFractionalLattice places tuple (fun i => a i + b i) := by
  unfold arithmeticTupleFractionalLattice submoduleTensorSpan
  rw [Submodule.span_mul_span]
  apply Submodule.span_mono
  rintro z ⟨x, hx, y, hy, rfl⟩
  rcases hx with ⟨xcoord, hxcoord, rfl⟩
  rcases hy with ⟨ycoord, hycoord, rfl⟩
  exact ⟨fun i => xcoord i * ycoord i,
    fun i _ => padicFractionalLattice_mul_mem (hxcoord i (Set.mem_univ i))
      (hycoord i (Set.mem_univ i)),
    (finitePadicTensorTprod_mul_tprod (places := places) (tuple := tuple)
      xcoord ycoord).symm⟩

/-- A tuple of exponents has exact fractional generators when each local
norm-ball lattice has an element of exactly its defining radius. -/
def arithmeticTupleHasExactFractionalGenerators (a : ι → ℝ) : Prop :=
  ∀ i, HasExactFractionalGenerator (p := p)
    (K := CommonPrimeCompletion (places i (tuple i))) (a i)


/-- A pure tensor whose coordinates all lie in the valuation-integer
lattices belongs to the valuation-integer tensor. -/
theorem arithmeticTupleValuationIntegerLattice_pure_tensor_mem
    (x : (i : ι) → CommonPrimeCompletion (places i (tuple i)))
    (hx : ∀ i, x i ∈ valuationIntegerLattice (p := p)
      (K := CommonPrimeCompletion (places i (tuple i)))) :
    finitePadicTensorTprod (p := p)
        (fun i => CommonPrimeCompletion (places i (tuple i))) x ∈
      arithmeticTupleValuationIntegerLattice places tuple := by
  unfold arithmeticTupleValuationIntegerLattice tensorIntegerLattice submoduleTensorSpan
    tensorIntegralRegion
  exact Submodule.subset_span ⟨x, fun i _ => hx i, rfl⟩

/-- Multiplication by the valuation-integer tensor does not enlarge a
fractional tensor. -/
theorem arithmeticTupleValuationIntegerLattice_mul_fractionalLattice_le
    (a : ι → ℝ) :
    arithmeticTupleValuationIntegerLattice places tuple *
        arithmeticTupleFractionalLattice places tuple a ≤
      arithmeticTupleFractionalLattice places tuple a := by
  simpa [arithmeticTupleFractionalLattice_zero, zero_add] using
    arithmeticTupleFractionalLattice_mul_le places tuple (fun _ => 0) a

/-- Exact fractional generators exhibit the tensor fractional lattice as the
valuation-integer tensor times the principal line of the pure exact
generator. This is the tensor-level principal fractional-ideal form. -/
theorem arithmeticTupleFractionalLattice_eq_valuationInteger_mul_span_of_norm_eq
    (a : ι → ℝ)
    (c : (i : ι) → CommonPrimeCompletion (places i (tuple i)))
    (hc : ∀ i, ‖c i‖ = (p : ℝ) ^ (-(a i))) :
    arithmeticTupleFractionalLattice places tuple a =
      arithmeticTupleValuationIntegerLattice places tuple *
        Submodule.span ℤ_[p]
          ({finitePadicTensorTprod (p := p)
            (fun i => CommonPrimeCompletion (places i (tuple i))) c} :
              Set (ArithmeticTensorTupleBlock places tuple)) := by
  let C : ArithmeticTensorTupleBlock places tuple :=
    finitePadicTensorTprod (p := p)
      (fun i => CommonPrimeCompletion (places i (tuple i))) c
  have hC_mem : C ∈ arithmeticTupleFractionalLattice places tuple a := by
    exact arithmeticTupleFractionalLattice_pure_tensor_mem places tuple a c
      (fun i => (hc i).le)
  apply le_antisymm
  · unfold arithmeticTupleFractionalLattice submoduleTensorSpan tensorIntegralRegion
    apply Submodule.span_le.mpr
    rintro z ⟨x, hx, rfl⟩
    let r : (i : ι) → CommonPrimeCompletion (places i (tuple i)) :=
      fun i => x i * (c i)⁻¹
    have hr : ∀ i, r i ∈ valuationIntegerLattice (p := p)
        (K := CommonPrimeCompletion (places i (tuple i))) := by
      intro i
      change r i ∈ Integers (CommonPrimeCompletion (places i (tuple i)))
      rw [mem_integers_iff]
      have hp : (0 : ℝ) < (p : ℝ) := by
        exact_mod_cast (Fact.out : Nat.Prime p).pos
      have hcpos : 0 < (p : ℝ) ^ (-(a i)) := Real.rpow_pos_of_pos hp _
      have hxnorm : ‖x i‖ ≤ (p : ℝ) ^ (-(a i)) := hx i (Set.mem_univ i)
      dsimp only [r]
      rw [norm_mul, norm_inv, hc]
      calc
        ‖x i‖ * ((p : ℝ) ^ (-(a i)))⁻¹ ≤
            (p : ℝ) ^ (-(a i)) * ((p : ℝ) ^ (-(a i)))⁻¹ :=
          mul_le_mul_of_nonneg_right hxnorm (inv_nonneg.mpr hcpos.le)
        _ = 1 := mul_inv_cancel₀ hcpos.ne'
    have hr_mem : finitePadicTensorTprod (p := p)
        (fun i => CommonPrimeCompletion (places i (tuple i))) r ∈
        arithmeticTupleValuationIntegerLattice places tuple :=
      arithmeticTupleValuationIntegerLattice_pure_tensor_mem places tuple r hr
    have hC_span : C ∈ Submodule.span ℤ_[p]
        ({C} : Set (ArithmeticTensorTupleBlock places tuple)) :=
      Submodule.subset_span (Set.mem_singleton C)
    have hx_eq : finitePadicTensorTprod (p := p)
          (fun i => CommonPrimeCompletion (places i (tuple i))) x =
        finitePadicTensorTprod (p := p)
            (fun i => CommonPrimeCompletion (places i (tuple i))) r * C := by
      dsimp only [C]
      rw [finitePadicTensorTprod_mul_tprod]
      congr 1
      funext i
      dsimp only [r]
      rw [mul_assoc, inv_mul_cancel₀
        (padicFractionalLattice_exactGenerator_ne_zero (hc i)), mul_one]
    rw [hx_eq]
    exact Submodule.mul_mem_mul hr_mem hC_span
  · rw [Submodule.mul_le]
    intro r hr s hs
    induction hs using Submodule.span_induction with
    | mem s hs =>
        have hs_eq : s = C := by simpa using hs
        subst s
        exact (arithmeticTupleValuationIntegerLattice_mul_fractionalLattice_le
          places tuple a) (Submodule.mul_mem_mul hr hC_mem)
    | zero =>
        simp
    | add s t hs ht ihs iht =>
        rw [mul_add]
        exact (arithmeticTupleFractionalLattice places tuple a).add_mem ihs iht
    | smul z s hs ih =>
        rw [Algebra.mul_smul_comm]
        exact (arithmeticTupleFractionalLattice places tuple a).smul_mem z ih

/-- The principal `Zp`-line in the tensor algebra acts on a submodule by
left multiplication. -/
theorem arithmeticTupleSubmodule_span_singleton_mul_eq_map_mulLeft
    (c : ArithmeticTensorTupleBlock places tuple)
    (N : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)) :
    Submodule.span ℤ_[p] ({c} :
        Set (ArithmeticTensorTupleBlock places tuple)) * N =
      N.map (LinearMap.mulLeft ℤ_[p] c) := by
  ext x
  rw [Submodule.mem_span_singleton_mul, Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, hzx⟩
    exact ⟨z, hz, hzx⟩
  · rintro ⟨z, hz, hzx⟩
    exact ⟨z, hz, hzx⟩

/-- Exact scalar scaling once `F a` has been identified with the
valuation-integer tensor times a principal line and the normalization
submodule is stable under the valuation-integer tensor. -/
theorem arithmeticTupleFractionalLattice_mul_eq_map_mulLeft_of_eq_valuationInteger_mul_span
    (a : ι → ℝ) (c : ArithmeticTensorTupleBlock places tuple)
    (N : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple))
    (hc : arithmeticTupleFractionalLattice places tuple a =
      arithmeticTupleValuationIntegerLattice places tuple *
        Submodule.span ℤ_[p]
          ({c} : Set (ArithmeticTensorTupleBlock places tuple)))
    (hN : arithmeticTupleValuationIntegerLattice places tuple * N = N) :
    arithmeticTupleFractionalLattice places tuple a * N =
      N.map (LinearMap.mulLeft ℤ_[p] c) := by
  rw [hc]
  calc
    (arithmeticTupleValuationIntegerLattice places tuple *
        Submodule.span ℤ_[p]
          ({c} : Set (ArithmeticTensorTupleBlock places tuple))) * N =
        Submodule.span ℤ_[p]
          ({c} : Set (ArithmeticTensorTupleBlock places tuple)) * N := by
      calc
        (arithmeticTupleValuationIntegerLattice places tuple *
            Submodule.span ℤ_[p]
              ({c} : Set (ArithmeticTensorTupleBlock places tuple))) * N =
            arithmeticTupleValuationIntegerLattice places tuple *
              (Submodule.span ℤ_[p]
                ({c} : Set (ArithmeticTensorTupleBlock places tuple)) * N) :=
          mul_assoc _ _ _
        _ = arithmeticTupleValuationIntegerLattice places tuple *
              (N * Submodule.span ℤ_[p]
                ({c} : Set (ArithmeticTensorTupleBlock places tuple))) := by
          rw [Submodule.mul_comm (Submodule.span ℤ_[p]
            ({c} : Set (ArithmeticTensorTupleBlock places tuple))) N]
        _ = (arithmeticTupleValuationIntegerLattice places tuple * N) *
              Submodule.span ℤ_[p]
                ({c} : Set (ArithmeticTensorTupleBlock places tuple)) :=
          (mul_assoc _ _ _).symm
        _ = N * Submodule.span ℤ_[p]
              ({c} : Set (ArithmeticTensorTupleBlock places tuple)) := by rw [hN]
        _ = Submodule.span ℤ_[p]
              ({c} : Set (ArithmeticTensorTupleBlock places tuple)) * N :=
          Submodule.mul_comm N (Submodule.span ℤ_[p]
            ({c} : Set (ArithmeticTensorTupleBlock places tuple)))
    _ = N.map (LinearMap.mulLeft ℤ_[p] c) :=
      arithmeticTupleSubmodule_span_singleton_mul_eq_map_mulLeft
        (places := places) (tuple := tuple) c N

section SingleCoordinateScaling

variable [DecidableEq ι]

/-- Exact scaling of an arbitrary normalization submodule by a
single-coordinate fractional lattice. The multiplier is the pure tensor with
the chosen local generator at `iSelected` and `1` elsewhere; this is the actual
`p^a` object in the one-factor fractional model. -/
theorem arithmeticTupleSingleFractionalLattice_mul_eq_map_mulLeft_of_norm_eq
    (iSelected : ι) {a : ℝ}
    {c : CommonPrimeCompletion (places iSelected (tuple iSelected))}
    (hc : ‖c‖ = (p : ℝ) ^ (-a))
    (N : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple))
    (hN : arithmeticTupleValuationIntegerLattice places tuple * N = N) :
    arithmeticTupleSingleFractionalLattice places tuple iSelected a * N =
      N.map (LinearMap.mulLeft ℤ_[p]
        (arithmeticTupleSingleFractionalGenerator places tuple iSelected c)) := by
  have hgen : ∀ i, ‖(Pi.mulSingle iSelected c :
      (j : ι) → CommonPrimeCompletion (places j (tuple j))) i‖ =
      (p : ℝ) ^ (-(arithmeticTupleSingleFractionalExponent iSelected a i)) := by
    intro i
    by_cases hi : i = iSelected
    · subst i
      simp [Pi.mulSingle_eq_same, arithmeticTupleSingleFractionalExponent, hc]
    · rw [Pi.mulSingle_eq_of_ne hi]
      rw [arithmeticTupleSingleFractionalExponent_ne hi, norm_one]
      simp
  have hspan := arithmeticTupleFractionalLattice_eq_valuationInteger_mul_span_of_norm_eq
    (places := places) (tuple := tuple)
    (a := arithmeticTupleSingleFractionalExponent iSelected a)
    (c := Pi.mulSingle iSelected c) hgen
  have hmain :=
    arithmeticTupleFractionalLattice_mul_eq_map_mulLeft_of_eq_valuationInteger_mul_span
      (places := places) (tuple := tuple)
      (a := arithmeticTupleSingleFractionalExponent iSelected a)
      (c := finitePadicTensorTprod (p := p)
        (fun j => CommonPrimeCompletion (places j (tuple j)))
        (Pi.mulSingle iSelected c)) N hspan hN
  change arithmeticTupleFractionalLattice places tuple
      (arithmeticTupleSingleFractionalExponent iSelected a) * N =
    N.map (LinearMap.mulLeft ℤ_[p]
      (arithmeticTupleFractionalPureGenerator places tuple (Pi.mulSingle iSelected c)))
  exact hmain

end SingleCoordinateScaling

/-- Exact-generator scaling of an arbitrary normalization submodule. The
multiplier is the pure tensor of the chosen local exact generators. Its
local exponents are the tuple `a`, and its total exponent is their sum. This
is the correct exact `p^a` object: it is a pure tensor, not a `Qp`-scalar. -/
theorem arithmeticTupleFractionalLattice_mul_eq_map_mulLeft_of_exact_generators
    {a : ι → ℝ}
    (ha : arithmeticTupleHasExactFractionalGenerators places tuple a)
    (N : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple))
    (hN : arithmeticTupleValuationIntegerLattice places tuple * N = N) :
    ∃ c : (i : ι) → CommonPrimeCompletion (places i (tuple i)),
      (∀ i, ‖c i‖ = (p : ℝ) ^ (-(a i))) ∧
      arithmeticTupleFractionalLattice places tuple a * N =
        N.map (LinearMap.mulLeft ℤ_[p]
          (arithmeticTupleFractionalPureGenerator places tuple c)) := by
  unfold arithmeticTupleHasExactFractionalGenerators at ha
  choose c hc using ha
  refine ⟨c, hc, ?_⟩
  exact arithmeticTupleFractionalLattice_mul_eq_map_mulLeft_of_eq_valuationInteger_mul_span
    (places := places) (tuple := tuple) a
    (finitePadicTensorTprod (p := p)
      (fun i => CommonPrimeCompletion (places i (tuple i))) c) N
    (arithmeticTupleFractionalLattice_eq_valuationInteger_mul_span_of_norm_eq
      (places := places) (tuple := tuple) a c hc) hN

/-- A nonnegative tuple of exponents gives a fractional tensor contained in
the valuation-integer tensor. -/
theorem arithmeticTupleFractionalLattice_le_valuationInteger
    {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    arithmeticTupleFractionalLattice places tuple a ≤
      arithmeticTupleValuationIntegerLattice places tuple := by
  unfold arithmeticTupleFractionalLattice arithmeticTupleValuationIntegerLattice
    tensorIntegerLattice submoduleTensorSpan tensorIntegralRegion
  apply Submodule.span_mono
  rintro z ⟨x, hx, rfl⟩
  exact ⟨x, fun i _ => padicFractionalLattice_le_valuationIntegerLattice_of_nonneg
    (ha i) (hx i (Set.mem_univ i)), rfl⟩

/-- Multiplying a fractional tensor by the valuation-integer tensor does not
enlarge it. This holds for every real exponent tuple. -/
theorem arithmeticTupleFractionalLattice_mul_valuationInteger_le (a : ι → ℝ) :
    arithmeticTupleFractionalLattice places tuple a *
        arithmeticTupleValuationIntegerLattice places tuple ≤
      arithmeticTupleFractionalLattice places tuple a := by
  simpa [arithmeticTupleFractionalLattice_zero] using
    arithmeticTupleFractionalLattice_mul_le places tuple a (fun _ => 0)

/-- For a nonnegative exponent tuple, multiplying by the valuation-integer
tensor remains in the valuation-integer tensor. -/
theorem arithmeticTupleFractionalLattice_mul_valuationInteger_le_valuationInteger
    {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    arithmeticTupleFractionalLattice places tuple a *
        arithmeticTupleValuationIntegerLattice places tuple ≤
      arithmeticTupleValuationIntegerLattice places tuple :=
  (arithmeticTupleFractionalLattice_mul_valuationInteger_le places tuple a).trans
    (arithmeticTupleFractionalLattice_le_valuationInteger places tuple ha)

/-- The standard submodule product `F a * N` is the `Zp`-span of the
setwise products of its elements: the normalization interface for the
paper's `p^λ · N` at the level of a submodule `N`. The exponent vector is
kept componentwise; it is not collapsed to a constant or to its total sum,
and no single-coordinate equality is asserted. -/
theorem arithmeticTupleFractionalLattice_mul_normalization
    (a : ι → ℝ) (N : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)) :
    arithmeticTupleFractionalLattice places tuple a * N =
      Submodule.span ℤ_[p]
        ((arithmeticTupleFractionalLattice places tuple a :
            Set (ArithmeticTensorTupleBlock places tuple)) *
          (N : Set (ArithmeticTensorTupleBlock places tuple))) :=
  Submodule.mul_eq_span_mul_set
    (arithmeticTupleFractionalLattice places tuple a) N

/-- Multiplication by a fixed fractional tensor is monotone in the
normalization submodule. -/
theorem arithmeticTupleFractionalLattice_mul_mono (a : ι → ℝ)
    {N₁ N₂ : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)}
    (hN : N₁ ≤ N₂) :
    arithmeticTupleFractionalLattice places tuple a * N₁ ≤
      arithmeticTupleFractionalLattice places tuple a * N₂ :=
  mul_le_mul' le_rfl hN

/-- One-sided associativity of fractional tensor multiplication: the
important direction for passing from `F b * N` to `F (a+b) * N`. -/
theorem arithmeticTupleFractionalLattice_mul_mul_le (a b : ι → ℝ)
    (N : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)) :
    arithmeticTupleFractionalLattice places tuple a *
        (arithmeticTupleFractionalLattice places tuple b * N) ≤
      arithmeticTupleFractionalLattice places tuple (fun i => a i + b i) * N := by
  calc
    arithmeticTupleFractionalLattice places tuple a *
        (arithmeticTupleFractionalLattice places tuple b * N) =
        (arithmeticTupleFractionalLattice places tuple a *
          arithmeticTupleFractionalLattice places tuple b) * N :=
      (mul_assoc _ _ _).symm
    _ ≤ arithmeticTupleFractionalLattice places tuple (fun i => a i + b i) * N :=
      mul_le_mul' (arithmeticTupleFractionalLattice_mul_le places tuple a b) le_rfl

/-- A submodule contained in the valuation-integer tensor is contained in
the integral log-shell tensor. This packages the `R ≤ log` step together
with an arbitrary normalization submodule. -/
theorem arithmeticTupleFractionalLattice_mul_le_integralLogLattice_of_le_valuationInteger
    {a : ι → ℝ} {N : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)}
    (hN : arithmeticTupleFractionalLattice places tuple a * N ≤
      arithmeticTupleValuationIntegerLattice places tuple) :
    arithmeticTupleFractionalLattice places tuple a * N ≤
      arithmeticTupleIntegralLogLattice places tuple :=
  hN.trans (arithmeticTupleValuationIntegerLattice_le_integralLogLattice places tuple)

/-- If `F d * N` is integral and `a` is a nonnegative exponent tuple, then
`F (d+a) * N` is integral. This is the direct monotone combination needed
in Step (v); no equality of fractional products is required. -/
theorem arithmeticTupleFractionalLattice_mul_le_valuationInteger_of_nonneg_add
    {d a : ι → ℝ} (ha : ∀ i, 0 ≤ a i)
    {N : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)}
    (hN : arithmeticTupleFractionalLattice places tuple d * N ≤
      arithmeticTupleValuationIntegerLattice places tuple) :
    arithmeticTupleFractionalLattice places tuple (fun i => d i + a i) * N ≤
      arithmeticTupleValuationIntegerLattice places tuple := by
  have hmono : arithmeticTupleFractionalLattice places tuple (fun i => d i + a i) ≤
      arithmeticTupleFractionalLattice places tuple d :=
    arithmeticTupleFractionalLattice_mono places tuple
      (fun i => le_add_of_nonneg_right (ha i))
  exact (mul_le_mul' hmono le_rfl).trans hN

end SubmoduleProduct

/-- The pure tensor whose every factor is the same integral power of `p`.
This is the common-prime tensor `tensor_i p^k`, of total exponent
`k * card ι`; it realizes the common shift `F (a + k * 1)`. It is not the
base-field scalar `p^k`. It is also not on the Step (v) path: that step uses
actual pure elements `tensor_i alpha_i`, not this tensor. -/
def arithmeticTupleCommonPrimePower (k : ℤ) : ArithmeticTensorTupleBlock places tuple :=
  finitePadicTensorTprod (p := p) (fun i => CommonPrimeCompletion (places i (tuple i)))
    (fun i => (p : CommonPrimeCompletion (places i (tuple i))) ^ k)

omit [Fintype ι] in
@[simp] theorem arithmeticTupleCommonPrimePower_zero :
    arithmeticTupleCommonPrimePower places tuple 0 = 1 := by
  unfold arithmeticTupleCommonPrimePower
  simp only [zpow_zero, finitePadicTensorTprod]
  exact PiTensorProduct.one_def.symm

omit [Fintype ι] in
theorem arithmeticTupleCommonPrimePower_mul_tprod (k : ℤ)
    (x : (i : ι) → CommonPrimeCompletion (places i (tuple i))) :
    arithmeticTupleCommonPrimePower places tuple k *
        finitePadicTensorTprod (p := p)
          (fun i => CommonPrimeCompletion (places i (tuple i))) x =
      finitePadicTensorTprod (p := p)
        (fun i => CommonPrimeCompletion (places i (tuple i)))
        (fun i => (p : CommonPrimeCompletion (places i (tuple i))) ^ k * x i) := by
  unfold arithmeticTupleCommonPrimePower finitePadicTensorTprod
  change (PiTensorProduct.tprod ℚ_[p]
      (fun i => (p : CommonPrimeCompletion (places i (tuple i))) ^ k)) *
      (PiTensorProduct.tprod ℚ_[p] x) =
    PiTensorProduct.tprod ℚ_[p]
      (fun i => (p : CommonPrimeCompletion (places i (tuple i))) ^ k * x i)
  exact PiTensorProduct.tprod_mul_tprod _ _

/-- Multiplication by the global common-prime power inside the tensor algebra. -/
def arithmeticTupleCommonPrimePowerMul (k : ℤ) :
    ArithmeticTensorTupleBlock places tuple →ₗ[ℤ_[p]]
      ArithmeticTensorTupleBlock places tuple :=
  (LinearMap.mulLeft ℚ_[p] (arithmeticTupleCommonPrimePower places tuple k)).restrictScalars ℤ_[p]

@[simp] theorem arithmeticTupleCommonPrimePowerMul_apply (k : ℤ)
    (x : ArithmeticTensorTupleBlock places tuple) :
    arithmeticTupleCommonPrimePowerMul places tuple k x =
      arithmeticTupleCommonPrimePower places tuple k * x := rfl

omit [Fintype ι] in
/-- The global prime power maps the pure-tensor region of `a` onto that of
`a + k`. -/
theorem arithmeticTupleCommonPrimePower_image_region (a : ι → ℝ) (k : ℤ) :
    (fun z : ArithmeticTensorTupleBlock places tuple =>
        arithmeticTupleCommonPrimePower places tuple k * z) ''
        tensorIntegralRegion (p := p)
          (fun i => CommonPrimeCompletion (places i (tuple i)))
          (fun i => (padicFractionalLattice (p := p)
            (K := CommonPrimeCompletion (places i (tuple i))) (a i) : Set _)) =
      tensorIntegralRegion (p := p)
        (fun i => CommonPrimeCompletion (places i (tuple i)))
        (fun i => (padicFractionalLattice (p := p)
          (K := CommonPrimeCompletion (places i (tuple i))) (a i + (k : ℝ)) : Set _)) := by
  unfold tensorIntegralRegion
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases hw with ⟨x, hx, rfl⟩
    refine ⟨fun i => (p : CommonPrimeCompletion (places i (tuple i))) ^ k * x i,
      fun i _ => ?_, ?_⟩
    · exact (mem_padicFractionalLattice_add_int_iff (p := p)
        (K := CommonPrimeCompletion (places i (tuple i))) (a i) k
        ((p : CommonPrimeCompletion (places i (tuple i))) ^ k * x i)).mpr
        ⟨x i, hx i (Set.mem_univ i), rfl⟩
    · change finitePadicTensorTprod (p := p)
          (fun i => CommonPrimeCompletion (places i (tuple i)))
          (fun i => (p : CommonPrimeCompletion (places i (tuple i))) ^ k * x i) =
        arithmeticTupleCommonPrimePower places tuple k *
          finitePadicTensorTprod (p := p)
            (fun i => CommonPrimeCompletion (places i (tuple i))) x
      rw [arithmeticTupleCommonPrimePower_mul_tprod]
  · rintro ⟨y, hy, rfl⟩
    choose x hxmem hxeq using fun i =>
      (mem_padicFractionalLattice_add_int_iff (p := p)
        (K := CommonPrimeCompletion (places i (tuple i))) (a i) k (y i)).mp
        (hy i (Set.mem_univ i))
    refine ⟨finitePadicTensorTprod (p := p)
        (fun i => CommonPrimeCompletion (places i (tuple i))) x,
      ⟨x, fun i _ => hxmem i, rfl⟩, ?_⟩
    change arithmeticTupleCommonPrimePower places tuple k *
        finitePadicTensorTprod (p := p)
          (fun i => CommonPrimeCompletion (places i (tuple i))) x =
        finitePadicTensorTprod (p := p)
          (fun i => CommonPrimeCompletion (places i (tuple i))) y
    rw [arithmeticTupleCommonPrimePower_mul_tprod]
    congr 1
    funext i
    exact hxeq i

/-- Common integer shift of every local exponent, realized by multiplication
with the pure tensor whose every factor is `p^k`. This is the common-exponent
tensor `F (a + k * 1)`, not a base-field scalar multiplication by `p^k`. -/
theorem arithmeticTupleFractionalLattice_shift_eq_map (a : ι → ℝ) (k : ℤ) :
    arithmeticTupleFractionalLattice places tuple (fun i => a i + (k : ℝ)) =
      (arithmeticTupleFractionalLattice places tuple a).map
        (arithmeticTupleCommonPrimePowerMul places tuple k) := by
  unfold arithmeticTupleFractionalLattice submoduleTensorSpan
  rw [Submodule.map_span]
  congr 1
  exact (arithmeticTupleCommonPrimePower_image_region places tuple a k).symm

/-- Membership form of the global integer shift. -/
theorem mem_arithmeticTupleFractionalLattice_shift_iff
    (a : ι → ℝ) (k : ℤ) (x : ArithmeticTensorTupleBlock places tuple) :
    x ∈ arithmeticTupleFractionalLattice places tuple (fun i => a i + (k : ℝ)) ↔
      ∃ y ∈ arithmeticTupleFractionalLattice places tuple a,
        arithmeticTupleCommonPrimePower places tuple k * y = x := by
  rw [arithmeticTupleFractionalLattice_shift_eq_map]
  constructor
  · intro hx
    rcases (Submodule.mem_map.mp hx) with ⟨y, hy, hyx⟩
    exact ⟨y, hy, hyx⟩
  · rintro ⟨y, hy, hyx⟩
    exact Submodule.mem_map.mpr ⟨y, hy, hyx⟩

end

end LeanFormal.IUT.NumberFieldFinitePlace



open LeanFormal.IUT.NumberFieldFinitePlace

#print axioms arithmeticTupleFractionalLattice
#print axioms arithmeticTupleFractionalLattice_zero
#print axioms arithmeticTupleSingleFractionalExponent
#print axioms arithmeticTupleSingleFractionalExponent_same
#print axioms arithmeticTupleSingleFractionalExponent_ne
#print axioms arithmeticTupleSingleFractionalLattice
#print axioms arithmeticTupleSingleFractionalGenerator
#print axioms arithmeticTupleFractionalPureGenerator
#print axioms arithmeticTupleFractionalLattice_mono
#print axioms arithmeticTupleFractionalLattice_pure_tensor_mem
#print axioms arithmeticTupleFractionalLattice_le_integralLogLattice
#print axioms finitePadicTensorTprod_mul_tprod
#print axioms arithmeticTupleFractionalLattice_pure_tensor_mul_mem
#print axioms arithmeticTupleFractionalLattice_mul_le
#print axioms arithmeticTupleHasExactFractionalGenerators
#print axioms arithmeticTupleValuationIntegerLattice_pure_tensor_mem
#print axioms arithmeticTupleValuationIntegerLattice_mul_fractionalLattice_le
#print axioms arithmeticTupleFractionalLattice_eq_valuationInteger_mul_span_of_norm_eq
#print axioms arithmeticTupleSubmodule_span_singleton_mul_eq_map_mulLeft
#print axioms arithmeticTupleFractionalLattice_mul_eq_map_mulLeft_of_eq_valuationInteger_mul_span
#print axioms arithmeticTupleSingleFractionalLattice_mul_eq_map_mulLeft_of_norm_eq
#print axioms arithmeticTupleFractionalLattice_mul_eq_map_mulLeft_of_exact_generators
#print axioms arithmeticTupleFractionalLattice_le_valuationInteger
#print axioms arithmeticTupleFractionalLattice_mul_valuationInteger_le
#print axioms arithmeticTupleFractionalLattice_mul_valuationInteger_le_valuationInteger
#print axioms arithmeticTupleFractionalLattice_mul_normalization
#print axioms arithmeticTupleFractionalLattice_mul_mono
#print axioms arithmeticTupleFractionalLattice_mul_mul_le
#print axioms arithmeticTupleFractionalLattice_mul_le_integralLogLattice_of_le_valuationInteger
#print axioms arithmeticTupleFractionalLattice_mul_le_valuationInteger_of_nonneg_add
#print axioms arithmeticTupleCommonPrimePower
#print axioms arithmeticTupleCommonPrimePower_zero
#print axioms arithmeticTupleCommonPrimePower_mul_tprod
#print axioms arithmeticTupleCommonPrimePowerMul
#print axioms arithmeticTupleCommonPrimePowerMul_apply
#print axioms arithmeticTupleCommonPrimePower_image_region
#print axioms arithmeticTupleFractionalLattice_shift_eq_map
#print axioms mem_arithmeticTupleFractionalLattice_shift_iff
