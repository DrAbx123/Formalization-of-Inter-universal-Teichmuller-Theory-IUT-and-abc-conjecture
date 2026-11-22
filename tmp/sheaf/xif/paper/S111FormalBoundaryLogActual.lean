import tmp.sheaf.xif.paper.S87OBoundaryDecompositionActual

/-! # S111: formal boundary log with codomain K x Z

Instead of seeking log(pi) in the completion, use the formal symbol logPi = (0,1)
in K x Z.  For x in O-boundary with DVR decomposition x = u * pi^n, define

  boundaryLogFormal x = (unitLog u, n),
  unitLogFormal u = (unitLog u, 0),
  boundaryLogFormal(pi) = (0,1).

The DVR decomposition is unique for fixed pi, so this is an actual multiplicative-
to-additive homomorphism and it extends the unit logarithm.  Changing pi changes
only the integer coordinate/unit part.

No fake field logarithm/sorry/axiom/True/PUnit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S111FormalBoundaryLogActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S63OBoundaryLogShellActual
open LeanFormal.IUT.XiFPaper.S87OBoundaryDecompositionActual

universe u

variable {K : Type u} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)

/-- Uniqueness of the DVR decomposition for a fixed uniformizer. -/
theorem boundaryUnitDecomposition_unique
    (x : sourceOBoundaryMonoid (K := K) (p := p) place)
    (n : ℕ) (u : (Integers (CommonPrimeCompletion place))ˣ)
    (h : (x : CommonPrimeCompletion place) =
      (u : CommonPrimeCompletion place) *
        ((dvrUniformizer (K := K) (p := p) place :
          Integers (CommonPrimeCompletion place)) : CommonPrimeCompletion place) ^ n) :
    (boundaryUnitDecomposition (K := K) (p := p) place x).n = n ∧
      (boundaryUnitDecomposition (K := K) (p := p) place x).u = u := by
  letI : IsDiscreteValuationRing (Integers (CommonPrimeCompletion place)) :=
    isDiscreteValuationRingIntegers (K := CommonPrimeCompletion place) (p := p)
  let d := boundaryUnitDecomposition (K := K) (p := p) place x
  have hInt : boundaryToIntegers (K := K) (p := p) place x =
      u * (dvrUniformizer (K := K) (p := p) place) ^ n := by
    apply Subtype.ext
    exact h
  have hdInt : boundaryToIntegers (K := K) (p := p) place x =
      d.u * (dvrUniformizer (K := K) (p := p) place) ^ d.n := by
    apply Subtype.ext
    exact d.eq
  have hxval : IsDiscreteValuationRing.addVal
      (Integers (CommonPrimeCompletion place))
      (boundaryToIntegers (K := K) (p := p) place x) = (n : ℕ∞) := by
    rw [hInt, IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_eq_zero_of_unit u, zero_add,
      Irreducible.addVal_pow
        (dvrUniformizer_irreducible (K := K) (p := p) place)]
  have hdval : IsDiscreteValuationRing.addVal
      (Integers (CommonPrimeCompletion place))
      (boundaryToIntegers (K := K) (p := p) place x) = (d.n : ℕ∞) := by
    rw [hdInt, IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_eq_zero_of_unit d.u, zero_add,
      Irreducible.addVal_pow
        (dvrUniformizer_irreducible (K := K) (p := p) place)]
  have hn : d.n = n := by
    exact_mod_cast (hdval.symm.trans hxval)
  constructor
  · exact hn
  · apply Units.ext
    have heqInt : u * (dvrUniformizer (K := K) (p := p) place) ^ n =
        d.u * (dvrUniformizer (K := K) (p := p) place) ^ n := by
      calc u * (dvrUniformizer (K := K) (p := p) place) ^ n
          = boundaryToIntegers (K := K) (p := p) place x := hInt.symm
        _ = d.u * (dvrUniformizer (K := K) (p := p) place) ^ d.n := hdInt
        _ = d.u * (dvrUniformizer (K := K) (p := p) place) ^ n := by rw [hn]
    exact (mul_right_cancel₀
      (pow_ne_zero n
        (Irreducible.ne_zero (dvrUniformizer_irreducible (K := K) (p := p) place)))
      heqInt).symm

/-- Formal boundary log with formal logPi = (0,1). -/
noncomputable def boundaryLogFormal
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) :
    CommonPrimeCompletion place × ℤ :=
  let d := boundaryUnitDecomposition (K := K) (p := p) place x
  (unitLog (K := CommonPrimeCompletion place) d.u, (d.n : ℤ))

/-- Formal unit logarithm: the unit part with integer coordinate 0. -/
noncomputable def unitLogFormal
    (u : (Integers (CommonPrimeCompletion place))ˣ) :
    CommonPrimeCompletion place × ℤ :=
  (unitLog (K := CommonPrimeCompletion place) u, 0)

/-- Formal boundary log of 1 is zero. -/
theorem boundaryLogFormal_one :
    boundaryLogFormal (K := K) (p := p) place
        (1 : sourceOBoundaryMonoid (K := K) (p := p) place) = 0 := by
  have huniq := boundaryUnitDecomposition_unique (K := K) (p := p) place
    (1 : sourceOBoundaryMonoid (K := K) (p := p) place) 0 1 (by simp)
  unfold boundaryLogFormal
  dsimp only
  rw [huniq.1, huniq.2]
  simp [unitLog_one (K := CommonPrimeCompletion place) (p := p)]

/-- Formal boundary log is additive on O-boundary. -/
theorem boundaryLogFormal_mul
    (x y : sourceOBoundaryMonoid (K := K) (p := p) place) :
    boundaryLogFormal (K := K) (p := p) place (x * y) =
      boundaryLogFormal (K := K) (p := p) place x +
        boundaryLogFormal (K := K) (p := p) place y := by
  let dx := boundaryUnitDecomposition (K := K) (p := p) place x
  let dy := boundaryUnitDecomposition (K := K) (p := p) place y
  have hprod : (x * y : CommonPrimeCompletion place) =
      ((dx.u * dy.u : (Integers (CommonPrimeCompletion place))ˣ) :
        CommonPrimeCompletion place) *
        ((dvrUniformizer (K := K) (p := p) place :
          Integers (CommonPrimeCompletion place)) : CommonPrimeCompletion place) ^
          (dx.n + dy.n) := by
    calc (x * y : CommonPrimeCompletion place)
        = ((dx.u : CommonPrimeCompletion place) *
            ((dvrUniformizer (K := K) (p := p) place :
              Integers (CommonPrimeCompletion place)) : CommonPrimeCompletion place) ^ dx.n) *
          ((dy.u : CommonPrimeCompletion place) *
            ((dvrUniformizer (K := K) (p := p) place :
              Integers (CommonPrimeCompletion place)) : CommonPrimeCompletion place) ^ dy.n) := by
          rw [dx.eq, dy.eq]
      _ = ((dx.u * dy.u : (Integers (CommonPrimeCompletion place))ˣ) :
            CommonPrimeCompletion place) *
          ((dvrUniformizer (K := K) (p := p) place :
            Integers (CommonPrimeCompletion place)) : CommonPrimeCompletion place) ^
            (dx.n + dy.n) := by
          simp only [Units.val_mul, Subring.coe_mul, pow_add]
          ring
  have huniq := boundaryUnitDecomposition_unique (K := K) (p := p) place
    (x * y) (dx.n + dy.n) (dx.u * dy.u) hprod
  have hdx_eq : boundaryUnitDecomposition (K := K) (p := p) place x = dx := rfl
  have hdy_eq : boundaryUnitDecomposition (K := K) (p := p) place y = dy := rfl
  unfold boundaryLogFormal
  dsimp only
  rw [hdx_eq, hdy_eq, huniq.1, huniq.2]
  rw [unitLog_mul (K := CommonPrimeCompletion place) (p := p)]
  ext <;> simp

/-- Actual monoid homomorphism to the formal additive codomain K x Z. -/
noncomputable def boundaryLogFormalHom :
    sourceOBoundaryMonoid (K := K) (p := p) place →*
      Multiplicative (CommonPrimeCompletion place × ℤ) where
  toFun x := Multiplicative.ofAdd (boundaryLogFormal (K := K) (p := p) place x)
  map_one' := by
    rw [boundaryLogFormal_one]
    rfl
  map_mul' := by
    intro x y
    rw [boundaryLogFormal_mul]
    rfl

/-- The formal log extends unitLog on the embedded O-times. -/
theorem boundaryLogFormal_ext_unit
    (u : (Integers (CommonPrimeCompletion place))ˣ) :
    boundaryLogFormal (K := K) (p := p) place
        (sourceOTimesToBoundary (K := K) (p := p) place u) =
      unitLogFormal (K := K) (p := p) place u := by
  have hx : ((sourceOTimesToBoundary (K := K) (p := p) place u :
      sourceOBoundaryMonoid (K := K) (p := p) place) :
      CommonPrimeCompletion place) =
      (u : CommonPrimeCompletion place) *
        ((dvrUniformizer (K := K) (p := p) place :
          Integers (CommonPrimeCompletion place)) : CommonPrimeCompletion place) ^ 0 := by
    change (u : CommonPrimeCompletion place) =
      (u : CommonPrimeCompletion place) *
        ((dvrUniformizer (K := K) (p := p) place :
          Integers (CommonPrimeCompletion place)) : CommonPrimeCompletion place) ^ 0
    simp
  have huniq := boundaryUnitDecomposition_unique (K := K) (p := p) place
    (sourceOTimesToBoundary (K := K) (p := p) place u) 0 u hx
  unfold boundaryLogFormal unitLogFormal
  dsimp only
  rw [huniq.1, huniq.2]
  simp

/-- The chosen uniformizer as an O-boundary element. -/
def dvrUniformizerBoundary :
    sourceOBoundaryMonoid (K := K) (p := p) place :=
  ⟨(dvrUniformizer (K := K) (p := p) place :
      CommonPrimeCompletion place),
    (dvrUniformizer (K := K) (p := p) place).property,
    fun h => Irreducible.ne_zero
      (dvrUniformizer_irreducible (K := K) (p := p) place)
      (Subtype.ext h)⟩

/-- The formal log of the chosen uniformizer is (0,1). -/
theorem boundaryLogFormal_uniformizer :
    boundaryLogFormal (K := K) (p := p) place
        (dvrUniformizerBoundary (K := K) (p := p) place) = (0, 1) := by
  have hx : ((dvrUniformizerBoundary (K := K) (p := p) place :
      sourceOBoundaryMonoid (K := K) (p := p) place) :
      CommonPrimeCompletion place) =
      ((1 : (Integers (CommonPrimeCompletion place))ˣ) :
        CommonPrimeCompletion place) *
        ((dvrUniformizer (K := K) (p := p) place :
          Integers (CommonPrimeCompletion place)) : CommonPrimeCompletion place) ^ 1 := by
    simp [dvrUniformizerBoundary]
  have huniq := boundaryUnitDecomposition_unique (K := K) (p := p) place
    (dvrUniformizerBoundary (K := K) (p := p) place) 1 1 hx
  unfold boundaryLogFormal
  dsimp only
  rw [huniq.1, huniq.2]
  simp [unitLog_one (K := CommonPrimeCompletion place) (p := p)]

end LeanFormal.IUT.XiFPaper.S111FormalBoundaryLogActual

end
