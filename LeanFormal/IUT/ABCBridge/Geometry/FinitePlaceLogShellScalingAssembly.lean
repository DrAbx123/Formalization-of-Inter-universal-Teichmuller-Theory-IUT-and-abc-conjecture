import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIntegerTensorComparison
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIntegralLogTensorLattice

/-!
# Prime-power scaling assemblies for the integral log-shell comparison

This file records the *integer-exponent special case* of the linear-algebraic
Step (v) input of the IUT IV Theorem 1.10 comparison.  A `Zp`-submodule `N` is
sandwiched between the actual valuation integer tensor `R = O_tensor` and the
integral log tensor `I = I_tensor` up to finite prime powers, and a `Qp`-linear
automorphism preserving the integral log lattice is given.  For every *integer*
prime-power scaling of `N` we prove that the automorphism carries it into the
correspondingly shifted integral lattice, and then into the correspondingly
shifted `N`.

This is NOT the paper's Step (v).  There the exponents are local fractional
exponents: `p^{a_I} R_I` is represented by
`submoduleTensorSpan (fun i => padicFractionalLattice (a i))`, and the exponent
domain is the value group `(1/e_i) Z`.  See the "Fractional single-coordinate
assembly" section below for the conditional fractional statement.  No claim is
made here that Step (v) or the N4--N7 obligations are closed.

The three sandwich inequalities are *hypotheses* of the assembly; they are the
future inputs from the normalization `(R_I)~` and from Propositions 1.1 and
1.2(i).  They are not asserted, axiomatized, or otherwise manufactured here.

The tensor block `Q` carries the scalar tower `Zp -> Qp -> Q`; it has no
standalone `Field` instance.  For that reason the integer powers of the prime
are taken in `Qp` and transported to `Q` by the algebra action.  This is the
same scalar as the corresponding integer power inside `Q`, and it keeps the
argument on the `Qp`-algebra structure that the block actually has.

## Fractional single-coordinate assembly (order-theoretic layer)

Fix a coordinate `i†`.  In the target instance `E lambda` is the
single-coordinate fractional tensor
`arithmeticTupleSingleFractionalLattice i† lambda`, `F c` is the full
fractional tensor `arithmeticTupleFractionalLattice c`, `N` is
`arithmeticTupleCanonicalUnitReference`, and `U` is
`arithmeticTupleUnitLogLattice` (not `arithmeticTupleIntegralLogLattice`).
The theorem `arithmeticTensorFractionalSingleCoordinateLogShellScalingAssembly`
is purely order-theoretic: from the three arithmetic inputs

* `hEscale : E lambda * N ≤ p^m • (F c * N)`,
* `hNA : F c * N ≤ U`,
* `hB : U ≤ F (-b) * N`,

where `c = d + a`.  The assembly takes `m` as an arbitrary integer parameter.
In the target instance `m` is the paper's integer exponent
`m0 = arithmeticTensorPaperExponent lambda d a =
⌊lambda⌋ - ⌈∑ i, d i⌉ - ⌈∑ i, a i⌉`; the ord bound
`m0 ≤ lambda - ∑ i, (d i + a i)` is
`arithmeticTensorPaperExponent_le_ordBound`.  The endpoint container is the
diagonal integer scalar `p^{m0 - arithmeticTensorPaperLogShift b} * N =
p^{m0 - ⌈∑ i, b i⌉} * N`, proved by
`arithmeticTensorFractionalSingleCoordinateLogShellScalingAssembly_paperEndpoint`.
The theorem proves

`phi '' (E lambda * N) ⊆ p^m • U` and
`phi '' (E lambda * N) ⊆ p^m • (F (-b) * N)`

for every `Qp`-linear automorphism `phi` preserving `U`.  The automorphism
commutes with the integer scalar `p^m` only; it is not asserted to commute with
a fractional power.

No decomposition `E (t)` of a fractional tensor along the total exponent is
used: the identity `F a * N = E (∑ i, a i) * N` is false in general (for
example for two copies of `Qp (sqrt p)` with `a = (1/2, 1/2)`).  The assembly
itself uses no floor arithmetic; the element chain uses the single central
base-field scalar `p^m` (the image of `(p : Qp)^m`).  Per-slot orders of a
general tensor element are not defined, and the scalar may be placed in any
slot.  What is used is the order `ord_L(r) = lambda - m - ∑ i, (d i + a i)` on
each field component `L` of `Q`, which is the same for every `L`.  No
decomposition of `p^m` into pure tensors is used.  The constant-exponent pure
tensor `arithmeticTupleCommonPrimePower m` has total exponent `m * card ι` and
is not this scalar.

## Element-chain inputs (guidance §12.3)

The three hypotheses are supplied by the element chain, not by any lattice
identity.  For the target instance:

* `hNA` is the tensor of Sagan's `δ • N ≤ R_I` with Curie's local
  `α_i R_i ≤ log_i`, where `δ = ⊗ δ_i` has order `d_i` and `α = ⊗ α_i` has
  order `a_i`; then `α δ` has order `c_i = d_i + a_i` and
  `α δ N ⊆ α R_I = F (d + a)`, which is `F c`.
* `hB` is the tensor of Curie's local `log_i ≤ β_i R_i`, where `β = ⊗ β_i`
  has order `-b_i`.
* `hEscale` is proved through `r = ϖ / (p^m0 α δ) ∈ N`, where `ϖ ∈ E lambda`
  has total exponent `lambda`.  The factor `p^m0` is the single central
  base-field scalar (the image of `(p : Qp)^m0`); it is not decomposed into
  pure tensors.  On each field component `L` of `Q` the well-defined order is
  `ord_L(r) = lambda - m0 - ∑ i, (d i + a i)`, the same for every `L`.  By
  `arithmeticTensorPaperExponent_le_ordBound` this equals
  `(lambda - ⌊lambda⌋) + (⌈d_I⌉ - d_I) + (⌈a_I⌉ - a_I) ≥ 0`.  Taking `E` a
  common multiple of the ramification indices makes
  `r^E = p^{E (lambda - m0 - ∑ i, (d i + a i))} * w` with `w ∈ R_I` and the
  exponent a nonnegative integer, hence `r^E ∈ R_I`; since `r` is a root of
  `X^E - r^E`, `IsIntegral.of_pow` gives `r ∈ N = (R_I)~`.  Hence
  `ϖ N = p^m0 α δ (r N) ⊆ p^m0 α δ N ⊆ p^m0 α R_I = p^m0 F c`.
  No sign hypothesis on `lambda` is used (`lambda = 0` at good places and
  `lambda > 0` at bad places are both allowed).

These element-chain statements are not asserted in this file.

## Handoff status (append-only; supersedes nothing above)

- File: `LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceLogShellScalingAssembly.lean`
  (sole owned source; ownership retained, source not copied to anyone).
- Last completed guard build: `D:\lean\tmp\n4n7-consolidation-20261017\logshell-scaling-assembly-build23.log`,
  final line `cmd exit=0`, 3636 jobs, 0 warnings attributed to this file.
  Axiom probe: `logshell-scaling-assembly-axioms-build23.log`, `cmd exit=0`;
  all 11 probed declarations depend only on `[propext, Classical.choice, Quot.sound]`;
  no `sorryAx`. Built-version SHA256 was
  `EC54CE8EC30D32E3FF9BD07C33C2E5E859DAFFF549048E4BB05D03EFF4E765F8`.
  The only change after build23 is this handoff note (docstring only, no code lines).
- Proved declarations present at build23 (all axiom-clean): the prime-cast/scalar-map/
  mul-submodule helpers; `arithmeticTensorPrimePower` and
  `arithmeticTensorPrimePowerScale` with `add`/`zero`/`mono`;
  `arithmeticTensorIntegerPrimePower_scale_le_integralLogLattice`;
  `arithmeticTensorIntegerLogShellScalingAssembly` (integer special case only);
  `arithmeticTensorSubmodule_mul_map_smul`;
  `arithmeticTensorPrimePowerScale_image_le_of_preserves`;
  `arithmeticTensorPaperExponent`; `arithmeticTensorPaperLogShift`;
  `arithmeticTensorPaperExponent_le_ordBound`; `arithmeticTensorPaperExponent_ord_nonneg`;
  `arithmeticTensorFractionalSingleCoordinateLogShellScalingAssembly` (abstract order-theoretic API);
  `arithmeticTensorFractionalSingleCoordinateLogShellScalingAssembly_paperEndpoint`;
  `arithmeticTensorNonposLambdaSingleCoordinateSlotBound` (lambda <= 0 reference only);
  `arithmeticTensorFractionalSingleCoordinateLogShellScalingAssembly_of_element`
  (element-chain backup API, explicitly NOT the Step (v) instance path).
- Not implemented: the five-item direct integer-scalar chain requested last.
  (1) `arithmeticTensorPaperNormalizationScale_le_integral`: absent; intended only as a
      named wrapper around the external `hNdiff` input (Sagan), not a proof of it.
  (2) `arithmeticTensorPaperShift_scale_le_unitLog`: absent. Wegener's tensorized local
      lemma is `arithmeticTupleFractionalLattice_paperA_le_unitLogLattice` in
      `FinitePlaceLocalInclusionTensorization.lean` (it bounds
      `F (paperA_exponents)` by `U`, not `p^(ceil (sum a)) * O` by `U`).
      The intermediate step `p^(ceil (sum a)) * O <= F a` was not verified and must not
      be assumed; next action is to take the explicit input
      `hAlog : p^(ceil (sum a)) * O <= U` (Curie tensorized).
  (3) `arithmeticTensorPaperExponent_split`: absent; provable immediately from
      `arithmeticTensorPrimePowerScale_add` and the definition of
      `arithmeticTensorPaperExponent` (pure integer bookkeeping).
  (4) `arithmeticTensorPaperStepV_endpoint`: absent; purely order-theoretic and ready to
      write: from `hE : E lambda * N <= p^(floor lambda) * N`,
      `hNdiff : p^(ceil (sum d)) * N <= O`, `hAlog : p^(ceil (sum a)) * O <= U`,
      `hB : U <= p^(-ceil (sum b)) * N`, `hphiU`, conclude
      `phi ' (E lambda * N) <= p^(m0 - ceil (sum b)) * N` using
      `arithmeticTensorPrimePowerScale_add`, `_mono`, `_image_le_of_preserves`.
  (5) `arithmeticTensorSingleCoordinateFractional_le_floorScale`: absent. Needed new
      ingredient: the integer identity `E k = p^k * O` for
      `E k = arithmeticTupleSingleFractionalLattice i† (k : R)` (single-coordinate
      integer fractional lattice equals the base-scalar scale of `O`).
      Road map: `arithmeticTupleFractionalLattice_eq_valuationInteger_mul_span_of_norm_eq`
      (Lorentz, `FinitePlaceFractionalTensorLattice.lean`) with generator
      `Pi.mulSingle i† ((p : K_i)^k)`, `norm_prime_zpow`, and
      `MultilinearMap.map_update_smul` to identify the pure tensor
      `tprod (mulSingle i† c)` with the base scalar `algebraMap c`; then
      `O.map (mulLeft varpi) = p^k * O`. Then `E lambda <= E floor(lambda)` by
      `arithmeticTupleFractionalLattice_mono`, and
      `(p^k * O) * N = (O * N).map scalar` by `arithmeticTensorSubmodule_mul_map_smul`.
      IMPORTANT: for an arbitrary `N` the target inequality is false; an
      `O`-module hypothesis is required. Use `hON : O * N <= N` (for
      `N = arithmeticTupleCanonicalUnitReference` this is discharged from
      `arithmeticTupleValuationIntegerLattice_subset_canonicalUnitReference` and
      `arithmeticTupleCanonicalUnitReference_eq_integralClosure` in
      `FinitePlaceHolomorphicIntegralClosure.lean`, plus closure of `integralClosure`
      under multiplication; both files are not yet imported here).
- Imports still to add for the above: `FinitePlaceFractionalTensorLattice`,
  `FinitePlaceLocalInclusionTensorization` (for the paperA lemma),
  `FinitePlaceUnscaledLogTensorLattice` (for `U`), possibly
  `FinitePlaceHolomorphicIntegralClosure`. Probe `probe15.lean` currently covers
  11 declarations only; it must be extended with each new declaration after build24.
- Standing boundaries: no `sorry`/`admit`/custom axioms were introduced; Step (v) is NOT
  claimed closed; the integer special case and `_of_element` remain backup only; the
  hull / `mu_log` / `CardAMPLThetaBoundSupply` consumer and Proposition 1.4(iii) constants
  were not touched; the normalizable theta of `FinitePlaceIQHullSharpUpperBound` is not used.
- Next exact action: implement item (3), then (4), then the `E k = p^k * O` lemma and
  item (5) with `hON`, then guard build24
  (`build_guard.ps1 -Slots 1 ... logshell-scaling-assembly-build24.log`), then extend and
  run `probe15.lean` under the same guard.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open scoped LeanFormal.IUT.FinitePadicIntegralLattice

noncomputable section

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)

/-- The prime is nonzero in `Qp`. -/
theorem arithmeticTensorPrimeCast_ne_zero : (p : ℚ_[p]) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero

/-- Multiplication by a `Qp`-scalar, bundled as a `Zp`-linear endomorphism of the
tensor block.  It is `Zp`-linear because the `Zp`-action factors through `Qp`. -/
def arithmeticTensorScalarLinearMap (c : ℚ_[p]) :
    ArithmeticTensorTupleBlock places tuple →ₗ[ℤ_[p]]
      ArithmeticTensorTupleBlock places tuple where
  toFun x := c • x
  map_add' x y := smul_add c x y
  map_smul' r x := (smul_comm r c x).symm

@[simp]
theorem arithmeticTensorScalarLinearMap_one :
    arithmeticTensorScalarLinearMap places tuple (1 : ℚ_[p]) = LinearMap.id := by
  ext x
  simp [arithmeticTensorScalarLinearMap]

/-- The image of a `Zp`-submodule of the tensor block under multiplication by a
`Qp`-scalar. -/
def arithmeticTensorMulSubmodule (c : ℚ_[p])
    (N : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)) :
    Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple) :=
  N.map (arithmeticTensorScalarLinearMap places tuple c)

@[simp]
theorem arithmeticTensorMulSubmodule_mem_iff {c : ℚ_[p]}
    {N : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)}
    {x : ArithmeticTensorTupleBlock places tuple} :
    x ∈ arithmeticTensorMulSubmodule places tuple c N ↔
      ∃ w ∈ N, c • w = x := by
  simp [arithmeticTensorMulSubmodule, arithmeticTensorScalarLinearMap]

/-- Scalar multiplications compose: multiplying first by `d` and then by `c`
is multiplication by `c * d`. -/
theorem arithmeticTensorMulSubmodule_mul (c d : ℚ_[p])
    {N : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)} :
    arithmeticTensorMulSubmodule places tuple c
        (arithmeticTensorMulSubmodule places tuple d N) =
      arithmeticTensorMulSubmodule places tuple (c * d) N := by
  unfold arithmeticTensorMulSubmodule
  rw [← Submodule.map_comp]
  congr 1
  ext x
  simp [arithmeticTensorScalarLinearMap, mul_smul]

/-- The integer power of the prime, taken in `Qp`. -/
def arithmeticTensorPrimePower (k : ℤ) : ℚ_[p] :=
  (p : ℚ_[p]) ^ k

/-- Integer powers of the prime add under multiplication. -/
theorem arithmeticTensorPrimePower_add (m n : ℤ) :
    arithmeticTensorPrimePower (p := p) (m + n) =
      arithmeticTensorPrimePower (p := p) m * arithmeticTensorPrimePower (p := p) n := by
  unfold arithmeticTensorPrimePower
  exact zpow_add₀ (arithmeticTensorPrimeCast_ne_zero (p := p)) m n

/-- The `Zp`-submodule `p^k • N`, i.e. the image of `N` under multiplication by
the integer power of the prime in the tensor block. -/
def arithmeticTensorPrimePowerScale (k : ℤ)
    (N : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)) :
    Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple) :=
  arithmeticTensorMulSubmodule places tuple (arithmeticTensorPrimePower (p := p) k) N

/-- Integer prime-power scalings add under composition. -/
theorem arithmeticTensorPrimePowerScale_add (m n : ℤ)
    {N : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)} :
    arithmeticTensorPrimePowerScale places tuple m
        (arithmeticTensorPrimePowerScale places tuple n N) =
      arithmeticTensorPrimePowerScale places tuple (m + n) N := by
  unfold arithmeticTensorPrimePowerScale
  rw [arithmeticTensorMulSubmodule_mul, arithmeticTensorPrimePower_add]

/-- Scaling by the zeroth power of the prime is the identity. -/
theorem arithmeticTensorPrimePowerScale_zero
    {N : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)} :
    arithmeticTensorPrimePowerScale places tuple 0 N = N := by
  unfold arithmeticTensorPrimePowerScale arithmeticTensorMulSubmodule
  have h0 : arithmeticTensorPrimePower (p := p) 0 = (1 : ℚ_[p]) := by
    simp [arithmeticTensorPrimePower]
  rw [h0, arithmeticTensorScalarLinearMap_one, Submodule.map_id]

/-- Scaling by a fixed integer prime power is monotone on `Zp`-submodules. -/
theorem arithmeticTensorPrimePowerScale_mono (k : ℤ)
    {N M : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)} (h : N ≤ M) :
    arithmeticTensorPrimePowerScale places tuple k N ≤
      arithmeticTensorPrimePowerScale places tuple k M :=
  Submodule.map_mono h

/-- The main integer-scaling inclusion: if `p^d • N <= R` and `p^a • R <= I`, then
`p^k • N <= p^(k - d - a) • I` for every integer `k`. -/
theorem arithmeticTensorIntegerPrimePower_scale_le_integralLogLattice
    (N : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple))
    (d a : ℕ)
    (hN : arithmeticTensorMulSubmodule places tuple ((p : ℚ_[p]) ^ d) N ≤
      arithmeticTupleValuationIntegerLattice places tuple)
    (hA : arithmeticTensorMulSubmodule places tuple ((p : ℚ_[p]) ^ a)
      (arithmeticTupleValuationIntegerLattice places tuple) ≤
      arithmeticTupleIntegralLogLattice places tuple) :
    ∀ k : ℤ,
      arithmeticTensorPrimePowerScale places tuple k N ≤
        arithmeticTensorPrimePowerScale places tuple (k - (d : ℤ) - (a : ℤ))
          (arithmeticTupleIntegralLogLattice places tuple) := by
  intro k
  have hN' : arithmeticTensorPrimePowerScale places tuple (d : ℤ) N ≤
      arithmeticTupleValuationIntegerLattice places tuple := by
    simpa [arithmeticTensorPrimePowerScale, arithmeticTensorPrimePower, zpow_natCast]
      using hN
  have hA' : arithmeticTensorPrimePowerScale places tuple (a : ℤ)
      (arithmeticTupleValuationIntegerLattice places tuple) ≤
      arithmeticTupleIntegralLogLattice places tuple := by
    simpa [arithmeticTensorPrimePowerScale, arithmeticTensorPrimePower, zpow_natCast]
      using hA
  have hstep : arithmeticTensorPrimePowerScale places tuple
      ((a : ℤ) + (d : ℤ)) N ≤ arithmeticTupleIntegralLogLattice places tuple := by
    have h1 : arithmeticTensorPrimePowerScale places tuple (a : ℤ)
        (arithmeticTensorPrimePowerScale places tuple (d : ℤ) N) ≤
        arithmeticTensorPrimePowerScale places tuple (a : ℤ)
          (arithmeticTupleValuationIntegerLattice places tuple) :=
      arithmeticTensorPrimePowerScale_mono places tuple (a : ℤ) hN'
    have h2 := h1.trans hA'
    rwa [arithmeticTensorPrimePowerScale_add] at h2
  have hmain : arithmeticTensorPrimePowerScale places tuple (k - (d : ℤ) - (a : ℤ))
      (arithmeticTensorPrimePowerScale places tuple ((a : ℤ) + (d : ℤ)) N) ≤
      arithmeticTensorPrimePowerScale places tuple (k - (d : ℤ) - (a : ℤ))
        (arithmeticTupleIntegralLogLattice places tuple) :=
    arithmeticTensorPrimePowerScale_mono places tuple _ hstep
  rwa [arithmeticTensorPrimePowerScale_add,
    show k - (d : ℤ) - (a : ℤ) + ((a : ℤ) + (d : ℤ)) = k by ring] at hmain

/-- The image of `p^k • N` under a `Qp`-linear automorphism preserving the
integral log lattice is contained in `p^(k - d - a) • I`. -/
theorem arithmeticTensorIntegerLogShellScalingAssembly_image_le_integralLogLattice
    (N : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple))
    (d a : ℕ)
    (hN : arithmeticTensorMulSubmodule places tuple ((p : ℚ_[p]) ^ d) N ≤
      arithmeticTupleValuationIntegerLattice places tuple)
    (hA : arithmeticTensorMulSubmodule places tuple ((p : ℚ_[p]) ^ a)
      (arithmeticTupleValuationIntegerLattice places tuple) ≤
      arithmeticTupleIntegralLogLattice places tuple)
    (k : ℤ)
    (φ : ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple)
    (hφ : ∀ x ∈ arithmeticTupleIntegralLogLattice places tuple,
      φ x ∈ arithmeticTupleIntegralLogLattice places tuple) :
    φ '' (arithmeticTensorPrimePowerScale places tuple k N :
        Set (ArithmeticTensorTupleBlock places tuple)) ⊆
      (arithmeticTensorPrimePowerScale places tuple (k - (d : ℤ) - (a : ℤ))
        (arithmeticTupleIntegralLogLattice places tuple) :
          Set (ArithmeticTensorTupleBlock places tuple)) := by
  intro y hy
  rw [Set.mem_image] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hx' : x ∈ arithmeticTensorPrimePowerScale places tuple (k - (d : ℤ) - (a : ℤ))
      (arithmeticTupleIntegralLogLattice places tuple) :=
    (arithmeticTensorIntegerPrimePower_scale_le_integralLogLattice places tuple N d a hN hA k) hx
  rw [arithmeticTensorPrimePowerScale, arithmeticTensorMulSubmodule_mem_iff] at hx'
  obtain ⟨w, hwI, hwx⟩ := hx'
  change φ x ∈ arithmeticTensorMulSubmodule places tuple
    (arithmeticTensorPrimePower (p := p) (k - (d : ℤ) - (a : ℤ)))
    (arithmeticTupleIntegralLogLattice places tuple)
  refine (arithmeticTensorMulSubmodule_mem_iff places tuple).mpr ⟨φ w, hφ w hwI, ?_⟩
  rw [← hwx, φ.map_smul]

/-- The image of `p^k • N` under a `Qp`-linear automorphism preserving the
integral log lattice is contained in `p^(k - d - a - b) • N`. -/
theorem arithmeticTensorIntegerLogShellScalingAssembly_image_le_normalization
    (N : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple))
    (d a b : ℕ)
    (hN : arithmeticTensorMulSubmodule places tuple ((p : ℚ_[p]) ^ d) N ≤
      arithmeticTupleValuationIntegerLattice places tuple)
    (hA : arithmeticTensorMulSubmodule places tuple ((p : ℚ_[p]) ^ a)
      (arithmeticTupleValuationIntegerLattice places tuple) ≤
      arithmeticTupleIntegralLogLattice places tuple)
    (hB : arithmeticTensorMulSubmodule places tuple ((p : ℚ_[p]) ^ b)
      (arithmeticTupleIntegralLogLattice places tuple) ≤ N)
    (k : ℤ)
    (φ : ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple)
    (hφ : ∀ x ∈ arithmeticTupleIntegralLogLattice places tuple,
      φ x ∈ arithmeticTupleIntegralLogLattice places tuple) :
    φ '' (arithmeticTensorPrimePowerScale places tuple k N :
        Set (ArithmeticTensorTupleBlock places tuple)) ⊆
      (arithmeticTensorPrimePowerScale places tuple
        (k - (d : ℤ) - (a : ℤ) - (b : ℤ)) N :
          Set (ArithmeticTensorTupleBlock places tuple)) := by
  intro y hy
  have hfirst := arithmeticTensorIntegerLogShellScalingAssembly_image_le_integralLogLattice
    places tuple N d a hN hA k φ hφ
  have hB' : arithmeticTensorPrimePowerScale places tuple (b : ℤ)
      (arithmeticTupleIntegralLogLattice places tuple) ≤ N := by
    simpa [arithmeticTensorPrimePowerScale, arithmeticTensorPrimePower, zpow_natCast]
      using hB
  have hscale : arithmeticTensorPrimePowerScale places tuple (k - (d : ℤ) - (a : ℤ))
      (arithmeticTupleIntegralLogLattice places tuple) ≤
      arithmeticTensorPrimePowerScale places tuple
        (k - (d : ℤ) - (a : ℤ) - (b : ℤ)) N := by
    have h := arithmeticTensorPrimePowerScale_mono places tuple
      (k - (d : ℤ) - (a : ℤ) - (b : ℤ)) hB'
    rwa [arithmeticTensorPrimePowerScale_add,
      show k - (d : ℤ) - (a : ℤ) - (b : ℤ) + (b : ℤ) = k - (d : ℤ) - (a : ℤ) by ring]
      at h
  exact hscale (hfirst hy)

/-- The assembled integer-exponent special-case consequences, conditional on the
two lower sandwiches `p^d • N <= R` and `p^a • R <= I` and the upper sandwich
`p^b • I <= N`. -/
theorem arithmeticTensorIntegerLogShellScalingAssembly
    (N : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple))
    (d a b : ℕ)
    (hN : arithmeticTensorMulSubmodule places tuple ((p : ℚ_[p]) ^ d) N ≤
      arithmeticTupleValuationIntegerLattice places tuple)
    (hA : arithmeticTensorMulSubmodule places tuple ((p : ℚ_[p]) ^ a)
      (arithmeticTupleValuationIntegerLattice places tuple) ≤
      arithmeticTupleIntegralLogLattice places tuple)
    (hB : arithmeticTensorMulSubmodule places tuple ((p : ℚ_[p]) ^ b)
      (arithmeticTupleIntegralLogLattice places tuple) ≤ N)
    (k : ℤ)
    (φ : ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple)
    (hφ : ∀ x ∈ arithmeticTupleIntegralLogLattice places tuple,
      φ x ∈ arithmeticTupleIntegralLogLattice places tuple) :
    (φ '' (arithmeticTensorPrimePowerScale places tuple k N :
        Set (ArithmeticTensorTupleBlock places tuple)) ⊆
      (arithmeticTensorPrimePowerScale places tuple (k - (d : ℤ) - (a : ℤ))
        (arithmeticTupleIntegralLogLattice places tuple) :
          Set (ArithmeticTensorTupleBlock places tuple))) ∧
    (φ '' (arithmeticTensorPrimePowerScale places tuple k N :
        Set (ArithmeticTensorTupleBlock places tuple)) ⊆
      (arithmeticTensorPrimePowerScale places tuple
        (k - (d : ℤ) - (a : ℤ) - (b : ℤ)) N :
          Set (ArithmeticTensorTupleBlock places tuple))) :=
  ⟨arithmeticTensorIntegerLogShellScalingAssembly_image_le_integralLogLattice
      places tuple N d a hN hA k φ hφ,
    arithmeticTensorIntegerLogShellScalingAssembly_image_le_normalization
      places tuple N d a b hN hA hB k φ hφ⟩

section FractionalSingleCoordinate

open scoped Pointwise BigOperators
local instance arithmeticTensorFractionalScalarAlgebra :
    Algebra ℤ_[p] (ArithmeticTensorTupleBlock places tuple) :=
  Algebra.restrictScalars ℤ_[p] ℚ_[p] (ArithmeticTensorTupleBlock places tuple)

/-- Multiplication by a base-field scalar distributes over the product of
`Zp`-submodules of the tensor algebra. -/
theorem arithmeticTensorSubmodule_mul_map_smul
    (M N : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple))
    (c : ℚ_[p]) :
    (M * N).map (arithmeticTensorScalarLinearMap places tuple c) =
      (M.map (arithmeticTensorScalarLinearMap places tuple c)) * N := by
  apply le_antisymm
  · intro z hz
    rcases Submodule.mem_map.mp hz with ⟨w, hw, rfl⟩
    refine Submodule.mul_induction_on (M := M) (N := N) hw ?_ ?_
    · intro x hx y hy
      have hmul : (arithmeticTensorScalarLinearMap places tuple c) (x * y) =
          (arithmeticTensorScalarLinearMap places tuple c) x * y := by
        change c • (x * y) = (c • x) * y
        exact (smul_mul_assoc c x y).symm
      rw [hmul]
      exact Submodule.mul_mem_mul (Submodule.mem_map.mpr ⟨x, hx, rfl⟩) hy
    · intro x y hx hy
      simpa using add_mem hx hy
  · apply Submodule.mul_le.mpr
    intro x hx y hy
    rcases Submodule.mem_map.mp hx with ⟨x0, hx0, rfl⟩
    refine Submodule.mem_map.mpr ⟨x0 * y, Submodule.mul_mem_mul hx0 hy, ?_⟩
    change c • (x0 * y) = (c • x0) * y
    exact (smul_mul_assoc c x0 y).symm

/-- A `Qp`-linear automorphism preserving `U` preserves every integer
prime-power scaling of `U`. -/
theorem arithmeticTensorPrimePowerScale_image_le_of_preserves
    (k : ℤ) (U : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple))
    (phi : ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple)
    (hphiU : ∀ x ∈ U, phi x ∈ U) :
    phi '' (arithmeticTensorPrimePowerScale places tuple k U :
        Set (ArithmeticTensorTupleBlock places tuple)) ⊆
      (arithmeticTensorPrimePowerScale places tuple k U :
        Set (ArithmeticTensorTupleBlock places tuple)) := by
  intro y hy
  rw [Set.mem_image] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  change x ∈ arithmeticTensorMulSubmodule places tuple
    (arithmeticTensorPrimePower (p := p) k) U at hx
  rw [arithmeticTensorMulSubmodule_mem_iff] at hx
  obtain ⟨u, hu, hux⟩ := hx
  rw [← hux, phi.map_smul]
  exact (arithmeticTensorMulSubmodule_mem_iff places tuple).mpr
    ⟨phi u, hphiU u hu, rfl⟩

/-- The paper's integer exponent of IV Step (v) and Proposition 1.4:
`m0 = ⌊lambda⌋ - ⌈∑ i, d i⌉ - ⌈∑ i, a i⌉`. -/
noncomputable def arithmeticTensorPaperExponent (lambda : ℝ) (d a : ι → ℝ) : ℤ :=
  ⌊lambda⌋ - ⌈∑ i, d i⌉ - ⌈∑ i, a i⌉

/-- The integer ceiling `⌈b_I⌉ = ⌈∑ i, b i⌉` of the endpoint shift. -/
noncomputable def arithmeticTensorPaperLogShift (b : ι → ℝ) : ℤ :=
  ⌈∑ i, b i⌉

/-- The paper exponent is bounded by the total order:
`m0 ≤ lambda - ∑ i, (d i + a i)`. -/
theorem arithmeticTensorPaperExponent_le_ordBound
    (lambda : ℝ) (d a : ι → ℝ) :
    (arithmeticTensorPaperExponent lambda d a : ℝ) ≤
      lambda - ∑ i, (d i + a i) := by
  have hfloor : (⌊lambda⌋ : ℝ) ≤ lambda := Int.floor_le lambda
  have hceilD : (∑ i, d i : ℝ) ≤ (⌈∑ i, d i⌉ : ℝ) := Int.le_ceil _
  have hceilA : (∑ i, a i : ℝ) ≤ (⌈∑ i, a i⌉ : ℝ) := Int.le_ceil _
  have hsum : (∑ i, (d i + a i) : ℝ) = (∑ i, d i) + (∑ i, a i) := by
    rw [Finset.sum_add_distrib]
  unfold arithmeticTensorPaperExponent
  push_cast
  linarith

/-- The order `ord_L(r) = lambda - m0 - ∑ i, (d i + a i)` is nonnegative. -/
theorem arithmeticTensorPaperExponent_ord_nonneg
    (lambda : ℝ) (d a : ι → ℝ) :
    0 ≤ lambda - (arithmeticTensorPaperExponent lambda d a : ℝ) -
      ∑ i, (d i + a i) := by
  have h := arithmeticTensorPaperExponent_le_ordBound lambda d a
  linarith

/-- Order-theoretic Step (v) assembly on the actual `N`/`U` carrier.

In the target instance `E lambda` is the single-coordinate fractional tensor
`arithmeticTupleSingleFractionalLattice i† lambda`, `F c` is the full
fractional tensor `arithmeticTupleFractionalLattice c`, `N` is
`arithmeticTupleCanonicalUnitReference`, and `U` is
`arithmeticTupleUnitLogLattice` (not `arithmeticTupleIntegralLogLattice`).
The three arithmetic inputs `hEscale`, `hNA`, `hB` are the outputs of the element
chain of guidance §12.3, not consequences of a lattice identity.

In the target instance `m` is the paper's integer exponent
`m0 = arithmeticTensorPaperExponent lambda d a =
⌊lambda⌋ - ⌈∑ i, d i⌉ - ⌈∑ i, a i⌉`; the element-chain ord bound
`m0 ≤ lambda - ∑ i, (d i + a i)` is
`arithmeticTensorPaperExponent_le_ordBound`.  The assembly takes `m` as a
parameter.  No equality
`F a * N = E (∑ i, a i) * N` is used; it fails in general (for example for
two copies of `Qp (sqrt p)` with `a = (1/2, 1/2)`). -/
theorem arithmeticTensorFractionalSingleCoordinateLogShellScalingAssembly
    (N U : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple))
    (E : ℝ → Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple))
    (F : (ι → ℝ) → Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple))
    (lambda : ℝ) (c b : ι → ℝ) (m : ℤ)
    (hEscale : E lambda * N ≤
      arithmeticTensorPrimePowerScale places tuple m (F c * N))
    (hNA : F c * N ≤ U)
    (hB : U ≤ F (-b) * N)
    (phi : ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple)
    (hphiU : ∀ x ∈ U, phi x ∈ U) :
    (phi '' ((E lambda * N :
          Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)) :
        Set (ArithmeticTensorTupleBlock places tuple)) ⊆
      (arithmeticTensorPrimePowerScale places tuple m U :
        Set (ArithmeticTensorTupleBlock places tuple))) ∧
    (phi '' ((E lambda * N :
          Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)) :
        Set (ArithmeticTensorTupleBlock places tuple)) ⊆
      (arithmeticTensorPrimePowerScale places tuple m (F (-b) * N) :
        Set (ArithmeticTensorTupleBlock places tuple))) := by
  have hEU : E lambda * N ≤ arithmeticTensorPrimePowerScale places tuple m U :=
    hEscale.trans (arithmeticTensorPrimePowerScale_mono places tuple m hNA)
  have hUN : arithmeticTensorPrimePowerScale places tuple m U ≤
      arithmeticTensorPrimePowerScale places tuple m (F (-b) * N) :=
    arithmeticTensorPrimePowerScale_mono places tuple m hB
  have hfirst : phi '' ((E lambda * N :
        Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)) :
        Set (ArithmeticTensorTupleBlock places tuple)) ⊆
      (arithmeticTensorPrimePowerScale places tuple m U :
        Set (ArithmeticTensorTupleBlock places tuple)) :=
    (Set.image_mono hEU).trans
      (arithmeticTensorPrimePowerScale_image_le_of_preserves places tuple m U phi hphiU)
  exact ⟨hfirst, hfirst.trans fun x hx => hUN hx⟩

/-- Paper-form endpoint of the Step (v) assembly: the image of `E lambda * N`
is contained in the diagonal integer scalar multiple `p^{m0 - ⌈b_I⌉} * N` of
the normalization, where `b_I = ∑ i, b i`.

The hypothesis `hB` is the integer form of Curie's bound,
`U ≤ p^{-⌈b_I⌉} * N`.  Only integer prime powers occur on the path, and `phi`
is used only through its preservation of `U`. -/
theorem arithmeticTensorFractionalSingleCoordinateLogShellScalingAssembly_paperEndpoint
    (N U : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple))
    (E : ℝ → Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple))
    (F : (ι → ℝ) → Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple))
    (lambda : ℝ) (b c : ι → ℝ) (m0 : ℤ)
    (hEscale : E lambda * N ≤
      arithmeticTensorPrimePowerScale places tuple m0 (F c * N))
    (hNA : F c * N ≤ U)
    (hB : U ≤ arithmeticTensorPrimePowerScale places tuple
      (-(arithmeticTensorPaperLogShift b)) N)
    (phi : ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple)
    (hphiU : ∀ x ∈ U, phi x ∈ U) :
    (phi '' ((E lambda * N :
          Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)) :
        Set (ArithmeticTensorTupleBlock places tuple)) ⊆
      (arithmeticTensorPrimePowerScale places tuple
        (m0 - arithmeticTensorPaperLogShift b) N :
        Set (ArithmeticTensorTupleBlock places tuple))) := by
  have hEU : E lambda * N ≤ arithmeticTensorPrimePowerScale places tuple m0 U :=
    hEscale.trans (arithmeticTensorPrimePowerScale_mono places tuple m0 hNA)
  have hUN : arithmeticTensorPrimePowerScale places tuple m0 U ≤
      arithmeticTensorPrimePowerScale places tuple
        (m0 - arithmeticTensorPaperLogShift b) N := by
    have h := arithmeticTensorPrimePowerScale_mono places tuple m0 hB
    rwa [arithmeticTensorPrimePowerScale_add,
      show m0 + -(arithmeticTensorPaperLogShift b) =
        m0 - arithmeticTensorPaperLogShift b by ring] at h
  have himage : phi '' ((E lambda * N :
        Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)) :
        Set (ArithmeticTensorTupleBlock places tuple)) ⊆
      (arithmeticTensorPrimePowerScale places tuple m0 U :
        Set (ArithmeticTensorTupleBlock places tuple)) :=
    (Set.image_mono hEU).trans
      (arithmeticTensorPrimePowerScale_image_le_of_preserves places tuple m0 U phi hphiU)
  exact himage.trans fun x hx => hUN hx

/-- Special case (`lambda ≤ 0`) of the single-coordinate slot bound.  It is
kept for reference only and is not the Step (v) instance path: there
`lambda ≥ 0` and the integer exponent is `arithmeticTensorPaperExponent`. -/
theorem arithmeticTensorNonposLambdaSingleCoordinateSlotBound
    [DecidableEq ι] (lambda : ℝ) (d a : ι → ℝ) (istar : ι) (m : ℤ)
    (hlambda : lambda ≤ 0)
    (hd : ∀ i, 0 ≤ d i) (ha : ∀ i, 0 ≤ a i)
    (hm_bound : (m : ℝ) ≤ ⌊lambda - ∑ i, (d i + a i)⌋) :
    ∀ i, (m : ℝ) ≤ lambda * (if i = istar then 1 else 0) - d i - a i := by
  have hm' : (m : ℝ) ≤ lambda - ∑ i, (d i + a i) :=
    hm_bound.trans (Int.floor_le (lambda - ∑ i, (d i + a i)))
  intro i
  have hsingle : d i + a i ≤ ∑ j, (d j + a j) := by
    simpa using Finset.single_le_sum (f := fun j => d j + a j)
      (fun j _ => add_nonneg (hd j) (ha j)) (Finset.mem_univ i)
  by_cases hi : i = istar
  · rw [if_pos hi]
    simp only [mul_one]
    linarith
  · rw [if_neg hi]
    simp only [mul_zero, zero_sub]
    linarith

/-- Element-chain instantiation of the `hEscale` input of
`arithmeticTensorFractionalSingleCoordinateLogShellScalingAssembly`.

The single-coordinate fractional lattice `E lambda` is generated by an element
`varpi` of order `lambda`.  Writing `varpi = p^m * alpha * delta * r` with
`alpha` of order `c` and `delta` of order `d`, the hypotheses record:

* `hspanN`: `E lambda * N` is generated by `varpi * N`.  (The lattice-level
  form `E lambda ≤ span {varpi}` is false in a multi-factor instance: `E lambda`
  is `varpi * R_I` of `Zp`-rank `∏ [k_i : Qp]`, while `span {varpi}` has rank
  one.  Only the `N`-level form is used.)
* `hr : r ∈ N`.  The factor `p^m` is the single central base-field scalar
  (the image of `(p : Qp)^m`); no pure-tensor decomposition and no per-slot
  orders are used.  On each field component `L` of `Q`,
  `ord_L(r) = lambda - m - ∑ i, (d i + a i)`.  In the target instance
  `m = arithmeticTensorPaperExponent lambda d a`;
  `arithmeticTensorPaperExponent_le_ordBound` then gives
  `ord_L(r) = (lambda - ⌊lambda⌋) + (⌈d_I⌉ - d_I) + (⌈a_I⌉ - a_I) ≥ 0`.
  Taking `E` a common multiple of the ramification indices gives
  `r^E = p^{E (lambda - m - ∑ i, (d i + a i))} * w` with `w ∈ R_I` and a
  nonnegative integer exponent, so `r^E ∈ R_I` and `IsIntegral.of_pow` gives
  `r ∈ N = (R_I)~`.  No sign hypothesis on `lambda` is used.
* `hδ : delta • N ⊆ R_I` (Sagan);
* `hαR : alpha • R_I ⊆ F c` (the tensor of Curie's `alpha_i R_i ⊆ log_i`).

These give `hEscale : E lambda * N ≤ p^m • (F c * N)`, and the abstract
assembly then yields the two image inclusions.  The paper-form endpoint in
`p^{m0 - ⌈b_I⌉} • N` is obtained by applying
`arithmeticTensorFractionalSingleCoordinateLogShellScalingAssembly_paperEndpoint`
to the same `hEscale` with the integer form `U ≤ p^{-⌈b_I⌉} • N` of Curie's
bound.  The merged inputs `hNA : F c * N ≤ U` and `hB : U ≤ F (-b) * N` are
the tensors of Sagan's `delta • N ⊆ R_I` with Curie's
`alpha_i R_i ⊆ log_i`, and of Curie's `log_i ⊆ beta_i R_i`. -/
theorem arithmeticTensorFractionalSingleCoordinateLogShellScalingAssembly_of_element
    (N U : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple))
    (E : ℝ → Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple))
    (F : (ι → ℝ) → Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple))
    (lambda : ℝ) (c b : ι → ℝ) (m : ℤ)
    (varpi alpha delta r : ArithmeticTensorTupleBlock places tuple)
    (hscale : varpi = arithmeticTensorPrimePower (p := p) m •
      (alpha * delta * r))
    (hspanN : E lambda * N ≤
      Submodule.span ℤ_[p] ({varpi} : Set (ArithmeticTensorTupleBlock places tuple)) * N)
    (hN1 : (1 : ArithmeticTensorTupleBlock places tuple) ∈ N)
    (hNN : N * N ≤ N)
    (hr : r ∈ N)
    (hδ : ∀ n ∈ N, delta * n ∈ arithmeticTupleValuationIntegerLattice places tuple)
    (hαR : ∀ x ∈ arithmeticTupleValuationIntegerLattice places tuple, alpha * x ∈ F c)
    (hNA : F c * N ≤ U)
    (hB : U ≤ F (-b) * N)
    (phi : ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple)
    (hphiU : ∀ x ∈ U, phi x ∈ U) :
    (phi '' ((E lambda * N :
          Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)) :
        Set (ArithmeticTensorTupleBlock places tuple)) ⊆
      (arithmeticTensorPrimePowerScale places tuple m U :
        Set (ArithmeticTensorTupleBlock places tuple))) ∧
    (phi '' ((E lambda * N :
          Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)) :
        Set (ArithmeticTensorTupleBlock places tuple)) ⊆
      (arithmeticTensorPrimePowerScale places tuple m (F (-b) * N) :
        Set (ArithmeticTensorTupleBlock places tuple))) := by
  have hEscale : E lambda * N ≤
      arithmeticTensorPrimePowerScale places tuple m (F c * N) := by
    have hmem : ∀ n ∈ N, varpi * n ∈
        arithmeticTensorPrimePowerScale places tuple m (F c) := by
      intro n hn
      have hrn : r * n ∈ N := hNN (Submodule.mul_mem_mul hr hn)
      have hd : delta * (r * n) ∈ arithmeticTupleValuationIntegerLattice places tuple :=
        hδ (r * n) hrn
      have ha : alpha * (delta * (r * n)) ∈ F c := hαR (delta * (r * n)) hd
      have heq : varpi * n = arithmeticTensorPrimePower (p := p) m •
          (alpha * (delta * (r * n))) := by
        rw [hscale, smul_mul_assoc]
        congr 1
        simp only [mul_assoc]
      exact (arithmeticTensorMulSubmodule_mem_iff places tuple).mpr
        ⟨alpha * (delta * (r * n)), ha, heq.symm⟩
    have hspanmul : Submodule.span ℤ_[p]
          ({varpi} : Set (ArithmeticTensorTupleBlock places tuple)) * N ≤
        arithmeticTensorPrimePowerScale places tuple m (F c) := by
      refine Submodule.mul_le.mpr ?_
      intro z hz n hn
      refine Submodule.span_induction
        (p := fun y _ => y * n ∈ arithmeticTensorPrimePowerScale places tuple m (F c))
        ?_ ?_ ?_ ?_ hz
      · intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hmem n hn
      · simp
      · intro x y hx hy hx' hy'
        rw [add_mul]
        exact add_mem hx' hy'
      · intro a x hx hx'
        rw [smul_mul_assoc]
        exact Submodule.smul_mem _ a hx'
    have h1 : E lambda * N ≤ arithmeticTensorPrimePowerScale places tuple m (F c) :=
      hspanN.trans hspanmul
    refine h1.trans (arithmeticTensorPrimePowerScale_mono places tuple m ?_)
    intro x hx
    simpa using Submodule.mul_mem_mul hx hN1
  exact arithmeticTensorFractionalSingleCoordinateLogShellScalingAssembly
    places tuple N U E F lambda c b m hEscale hNA hB phi hphiU

end FractionalSingleCoordinate

end

end LeanFormal.IUT.NumberFieldFinitePlace




