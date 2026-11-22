import tmp.sheaf.xif.paper.S2216D5QuadraticTransportActual
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.RingTheory.PrincipalIdealDomain
noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace LeanFormal.IUT.XiFPaper.S2228TwentyNineInertActual
open Polynomial NumberField IsCyclotomicExtension Ideal
local instance : NeZero 3 := ⟨by norm_num⟩
local instance : NeZero (3 : ℚ) := ⟨by norm_num⟩
abbrev K : Type := CyclotomicField 3 ℚ
local instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
open LeanFormal.IUT.XiFPaper.S2216D5QuadraticTransportActual
/-- **29 is inert in Q(sqrt(-3))**: the ideal (29) is prime in O_K. -/
theorem s2228_twentyNineInert :
    (Ideal.span {(29 : RingOfIntegers K)}).IsPrime := by
  let hζ := zeta_spec 3 ℚ K
  let θ := hζ.toInteger
  have hexp1 : RingOfIntegers.exponent θ = 1 := by
    rw [RingOfIntegers.exponent_eq_one_iff]
    simpa [θ] using hζ.integralPowerBasis.adjoin_gen_eq_top
  have hexp : ¬ 29 ∣ RingOfIntegers.exponent θ := by
    rw [hexp1]
    norm_num
  have hmin : minpoly ℤ θ = (X^2 + X + 1 : ℤ[X]) := by
    rw [← RingOfIntegers.minpoly_coe θ]
    rw [show (↑θ : K) = zeta 3 ℚ K from hζ.coe_toInteger]
    simpa [cyclotomic_three] using (cyclotomic_eq_minpoly hζ (by norm_num)).symm
  let Q : (ZMod 29)[X] := X^2 + X + 1
  have hQ : (X^2 + X + 1 : ℤ[X]).map (Int.castRingHom (ZMod 29)) = Q := by
    simp [Q]
  let e := RingOfIntegers.ZModXQuotSpanEquivQuotSpan (K := K) (θ := θ) (p := 29) hexp
  have hI : Ideal.span {(minpoly ℤ θ).map (Int.castRingHom (ZMod 29))} = Ideal.span {Q} := by
    rw [hmin, hQ]
  let e' : ((ZMod 29)[X] ⧸ Ideal.span {Q}) ≃+* (RingOfIntegers K ⧸ Ideal.span {(29 : RingOfIntegers K)}) :=
    (Ideal.quotEquivOfEq hI).symm.trans e
  have hfieldP : IsField ((ZMod 29)[X] ⧸ Ideal.span {Q}) := by
    haveI : (Ideal.span {Q}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible
        (by simpa [Q] using s2216_cyclotomic_three_mod29_irreducible)
    letI : Field ((ZMod 29)[X] ⧸ Ideal.span {Q}) := Ideal.Quotient.field (Ideal.span {Q})
    exact Field.toIsField _
  have hfieldO : IsField (RingOfIntegers K ⧸ Ideal.span {(29 : RingOfIntegers K)}) :=
    e'.symm.toMulEquiv.isField hfieldP
  exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr hfieldO |>.isPrime
/-- The S2216 inertness target is now proved. -/
theorem s2228_TwentyNineInert_holds : s2216TwentyNineInert := by
  unfold s2216TwentyNineInert s2216QsqrtNeg3
  exact s2228_twentyNineInert
/-- Linear disjointness remains the exact missing transport. -/
def s2228LinearDisjointnessRequired : Prop :=
  s2216LinearDisjointnessRequired
#print axioms s2228_twentyNineInert
#print axioms s2228_TwentyNineInert_holds
end LeanFormal.IUT.XiFPaper.S2228TwentyNineInertActual
end
