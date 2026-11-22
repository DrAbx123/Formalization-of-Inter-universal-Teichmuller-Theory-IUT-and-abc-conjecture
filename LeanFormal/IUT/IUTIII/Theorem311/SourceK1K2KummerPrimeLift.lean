import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2Realization
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic

/-!
  # K1/K2 kappa-slot arithmetic upgrade: prime-exponent Kummer lift injectivity
  (run k1k2-realization-20261016, continuation package)

  E3 of `SourceK1K2Realization.lean` builds the labelled Kummer iso on the
  adjoined quotient `AdjoinRoot (X ^ n - C a)` from injectivity of the
  AdjoinRoot lift into the algebraic closure (`hinj`).  This file discharges
  that injectivity in the first arithmetic case:

  * `padic_pow_ne_self_of_two_le`: no element of `Q_[p]` has `n`-th power
    `p` when `2 <= n` (normalized `p`-adic valuation: `v p = 1` while
    `v (b ^ n) = n * v b`).
  * `adjoinRootEmbedding_lift_injective_of_irreducible`: for any Kummer
    polynomial data over a field, irreducibility of the Kummer polynomial
    makes the quotient a field (Mathlib `AdjoinRoot.instField`) and every
    AdjoinRoot lift into a field extension injective.
  * `localKummerPolynomial_irreducible_of_prime_exponent`: for prime exponent
    `n`, the Mathlib theorem `X_pow_sub_C_irreducible_of_prime` combined with
    the valuation argument makes `X ^ n - C p` irreducible over `Q_[p]`.
  * `localKummerLift_injective_of_prime_exponent` and
    `labelledKummerIso_nonempty_of_localKummerRootRealizationFor_prime`: the
    E3 labelled Kummer iso is inhabited for prime exponents with no remaining
    hypothesis.
  * `labelledKummerIso_nonempty_of_irreducible_localKummerPolynomial`: the
    exact conditional form for an arbitrary exponent; the named missing
    object is irreducibility of the Kummer polynomial (for composite `n` the
    Mathlib criterion used here does not apply; over `Q_[p]` the polynomial
    is expected to be irreducible by the Eisenstein-at-`p` argument, which is
    not formalized here).

  Status boundary: this closes the interface-level kappa slot for prime
  exponent in the frozen E3 shape.  It does not identify the Kummer roots
  with the source's compatible system of rational roots, and it does not
  prove `hsep`/`hpres` or any IUT II section 5-6 content.  The label
  component of the E3 iso is constant; the frozen record imposes no
  arithmetic label law on it.
-/

set_option linter.unusedVariables false

namespace LeanFormal.IUT

namespace K1K2Realization

noncomputable section

open Theorem311Source

/-- No power collision: for `2 <= n`, no `b : Q_[p]` satisfies `b ^ n = p`.
Valuation count: `v (b ^ n) = n * v b` must equal `v p = 1`, impossible
since `n` divides no unit. -/
theorem padic_pow_ne_self_of_two_le {p n : Nat} [Fact (Nat.Prime p)]
    (hn : 2 ≤ n) (b : ℚ_[p]) : b ^ n ≠ (p : ℚ_[p]) := by
  intro hb
  have hval : (b ^ n).valuation = (p : ℚ_[p]).valuation :=
    congrArg Padic.valuation hb
  rw [Padic.valuation_pow, Padic.valuation_p] at hval
  have hdvdInt : (n : ℤ) ∣ (1 : ℤ) := ⟨b.valuation, hval.symm⟩
  have hdvd : n ∣ 1 := Int.natCast_dvd_natCast.mp hdvdInt
  have hone : n = 1 := Nat.dvd_one.mp hdvd
  omega

/-- Irreducible Kummer polynomial gives injective AdjoinRoot lift: the
quotient `D.Adjoined` is then a field (Mathlib `AdjoinRoot.instField`), and
the lift `AdjoinRoot.liftAlgHom` from a field into a field extension has
trivial kernel. -/
theorem adjoinRootEmbedding_lift_injective_of_irreducible
    {K : Type*} [Field K] (D : KummerPolynomialData K) (Lt : Type*)
    [Field Lt] [Algebra K Lt] (Radj : AdjoinRootEmbedding D Lt)
    (hirr : Irreducible D.polynomial) :
    Function.Injective (Radj.lift D Lt) := by
  haveI : Fact (Irreducible D.polynomial) := ⟨hirr⟩
  have hker : RingHom.ker (Radj.lift D Lt).toRingHom = ⊥ := by
    rcases Ideal.eq_bot_or_top (RingHom.ker (Radj.lift D Lt).toRingHom)
      with h | h
    · exact h
    · exfalso
      have hmem : (1 : D.Adjoined) ∈
          RingHom.ker (Radj.lift D Lt).toRingHom := by
        rw [h]
        exact Submodule.mem_top
      have hz : (Radj.lift D Lt) 1 = 0 := RingHom.mem_ker.mp hmem
      simp only [map_one] at hz
      exact one_ne_zero hz
  exact (RingHom.injective_iff_ker_eq_bot (Radj.lift D Lt).toRingHom).mpr hker

/-- For prime exponent `n`, `X ^ n - C p` is irreducible over `Q_[p]`
(Mathlib Kummer-polynomial criterion plus the valuation argument). -/
theorem localKummerPolynomial_irreducible_of_prime_exponent
    (p n : Nat) [Fact (Nat.Prime p)] (hn : n.Prime) :
    Irreducible (localKummerPolynomialFor p n hn.pos).polynomial := by
  have hpol : (localKummerPolynomialFor p n hn.pos).polynomial =
      Polynomial.X ^ n - Polynomial.C (p : ℚ_[p]) := rfl
  rw [hpol]
  exact X_pow_sub_C_irreducible_of_prime hn
    (fun b => padic_pow_ne_self_of_two_le hn.two_le b)

/-- E3 prime upgrade: for prime exponent the lift of the local Kummer root
into the algebraic closure is injective, unconditionally. -/
theorem localKummerLift_injective_of_prime_exponent
    (p n : Nat) [Fact (Nat.Prime p)] (hn : n.Prime) :
    Function.Injective
      ((localKummerRootRealizationFor p n hn.pos).lift
        (localKummerPolynomialFor p n hn.pos) (AlgebraicClosure ℚ_[p])) :=
  adjoinRootEmbedding_lift_injective_of_irreducible
    (localKummerPolynomialFor p n hn.pos) (AlgebraicClosure ℚ_[p])
    (localKummerRootRealizationFor p n hn.pos)
    (localKummerPolynomial_irreducible_of_prime_exponent p n hn)

/-- E3 general conditional form: irreducibility of the Kummer polynomial is
exactly the named residual input for the labelled Kummer iso in the frozen
E3 shape. -/
theorem labelledKummerIso_nonempty_of_irreducible_localKummerPolynomial
    (p n : Nat) [Fact (Nat.Prime p)] (hn : 0 < n)
    (hirr : Irreducible (localKummerPolynomialFor p n hn).polynomial) :
    Nonempty (LabelledKummerIso (localKummerPolynomialFor p n hn).Adjoined
      (Set.range ((localKummerRootRealizationFor p n hn).lift
        (localKummerPolynomialFor p n hn) (AlgebraicClosure ℚ_[p])))) :=
  labelledKummerIso_nonempty_of_localKummerRootRealizationFor p n hn
    (adjoinRootEmbedding_lift_injective_of_irreducible
      (localKummerPolynomialFor p n hn) (AlgebraicClosure ℚ_[p])
      (localKummerRootRealizationFor p n hn) hirr)

/-- E3-b unconditional, prime exponent: the labelled Kummer iso of the local
root realization exists with no injectivity hypothesis. -/
theorem labelledKummerIso_nonempty_of_localKummerRootRealizationFor_prime
    (p n : Nat) [Fact (Nat.Prime p)] (hn : n.Prime) :
    Nonempty (LabelledKummerIso (localKummerPolynomialFor p n hn.pos).Adjoined
      (Set.range ((localKummerRootRealizationFor p n hn.pos).lift
        (localKummerPolynomialFor p n hn.pos) (AlgebraicClosure ℚ_[p])))) :=
  labelledKummerIso_nonempty_of_irreducible_localKummerPolynomial p n hn.pos
    (localKummerPolynomial_irreducible_of_prime_exponent p n hn)

end

end K1K2Realization

end LeanFormal.IUT
