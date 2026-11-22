import tmp.sheaf.xif.paper.S2578Prime613Actual
import tmp.sheaf.xif.paper.S1720SourceArithmeticActual
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.FieldTheory.PrimitiveElement

/-!
# S2579: the degree-one prime of S over 613 via Kummer-Dedekind

Let F' be the number field S1720Field = SplittingField (S1687H * (X^2+1)) and let
S = O_F'[1/Cden] be the localised ring of integers of S2565ConcreteIntegralClosureCActual.

## What is actually proved in this file

* S2579Candidate = a * S1720Lift(S1687Y) + i, where a = 463856467968 is the leading
  coefficient of the sextic S1687H and i is an actual square root of -1 in F';
* S2579_isIntegral_candidate: the candidate is an algebraic integer.  The scaling by a
  is necessary: S1687Y itself is a root of the non-monic polynomial S1687H, hence it is
  not an algebraic integer in general;
* S2579Theta: the candidate as an element of the ring of integers C = O_F';
* the Kummer-Dedekind core: if 613 is prime to the conductor exponent of theta and
  minpoly of theta has a root r modulo 613, then the prime over 613 attached to the
  linear factor X - C r lies over 613 and has inertia degree one
  (S2579_linearFactor_prime), and its residue field is ZMod 613
  (S2579_quotient_equiv);
* the localisation step to S: the extended prime is prime, lies over 613, and its
  residue field is unchanged (S2579_localized_quotient_equiv);
* consequently, for any theta satisfying the two arithmetic inputs, S has a prime over
  613 with residue field ZMod 613 (S2579_prime613_of_theta), in particular for the
  actual candidate (S2579_prime613_of_arithmetic).

## The exact remaining arithmetic inputs

Three statements are isolated as named Props and are NOT proved here:

1. S2579Primitive: theta generates F' over Q.  (It is implied by the conductor
   condition below, but that implication is not formalised here.)
2. S2579Conductor613: 613 does not divide the conductor exponent of Z[theta].
   By RingOfIntegers.not_dvd_exponent_iff this is the codisjointness statement recorded
   in S2579_conductor_iff.
3. S2579LinearFactor613: minpoly of theta modulo 613 has a root in ZMod 613.

## External exact computation (sympy, not formalised)

* the minimal polynomial of the candidate over Q is the monic integer polynomial of
  degree 12

  X^12 + 3686686718987773113532422 X^10 + ... + 17461463173174011582761234456954928886602725098127406596813431452619322589360189151409387505478783853884785910317333751256475494692028676046849

  (all coefficients are integers; the exact polynomial was computed by sympy's
  minimal_polynomial).  It is irreducible over Q;
* modulo 613 this polynomial factors as

  (X - 269)(X - 224)(X - 199)(X - 154)(X - 49)(X - 21)
        (X + 21)(X + 49)(X + 154)(X + 199)(X + 224)(X + 269)

  so the linear-factor condition holds, for instance with r = 21;
* the discriminant of this polynomial is nonzero modulo 613 (it is 403 modulo 613),
  so 613 does not divide the index of Z[theta] in O_F' and hence does not divide the
  conductor exponent.  Computing the exponent itself in Lean is the remaining step;
* the Galois group of S1687H has order 6 (computed with sympy), so
  F = SplittingField S1687H = Q(S1687Y) and F' = F(i) has degree 12 over Q.

These computations are evidence for the remaining Props; they are not used as axioms
and the Lean theorems below only claim what is proved.

No sorry, axiom, True/PUnit gate or native_decide is used.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2579Kummer613Actual

open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual

local instance : Fact (Nat.Prime 613) := ⟨by norm_num⟩

/-- The integer leading coefficient of the defining sextic S1687H. -/
def S2579a : ℤ := 463856467968

/-- The chosen root of S1687H pushed into F' by the splitting-field lift. -/
noncomputable def S2579Y : S1720Field := S1720Lift S1687Y

theorem S2579Y_root : aeval S2579Y S1687H = 0 := by
  rw [S2579Y, Polynomial.aeval_algHom_apply, S1687Y_root, map_zero]

/-- The actual square root of -1 in F'. -/
noncomputable def S2579I : S1720Field := Classical.choose S1720HasSqrtNegOne

theorem S2579I_sq : S2579I * S2579I = -1 :=
  Classical.choose_spec S1720HasSqrtNegOne

/-- The actual candidate element: a*y + i, where y is a root of S1687H. -/
noncomputable def S2579Candidate : S1720Field :=
  (S2579a : S1720Field) * S2579Y + S2579I

/-- The monic integer polynomial satisfied by a * S1687Y. -/
def S2579Hmonic : ℤ[X] :=
  X ^ 6 + C (3973952045056 * 463856467968) * X ^ 4 +
    C (1991485440000 * 463856467968 ^ 3) * X ^ 2 +
    C (6153500390625 * 463856467968 ^ 5)

lemma S2579Hmonic_monic : S2579Hmonic.Monic := by
  unfold S2579Hmonic
  monicity!

lemma S2579Hmonic_eval :
    aeval ((S2579a : S1720Field) * S2579Y) S2579Hmonic = 0 := by
  have hH : (463856467968 : S1720Field) * S2579Y ^ 6 +
      3973952045056 * S2579Y ^ 4 + 1991485440000 * S2579Y ^ 2 +
        6153500390625 = 0 := by
    have h := S2579Y_root
    unfold S1687H at h
    simp only [Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_X,
      Polynomial.aeval_C, Polynomial.aeval_X_pow] at h
    norm_num at h ⊢
    exact h
  unfold S2579Hmonic S2579a
  simp only [Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_X,
    Polynomial.aeval_C, Polynomial.aeval_X_pow]
  norm_num
  linear_combination (463856467968 : S1720Field) ^ 5 * hH

lemma S2579_isIntegral_Y : IsIntegral ℤ ((S2579a : S1720Field) * S2579Y) :=
  ⟨S2579Hmonic, S2579Hmonic_monic, S2579Hmonic_eval⟩

lemma S2579_isIntegral_I : IsIntegral ℤ S2579I := by
  apply IsIntegral.of_pow (n := 2) (by norm_num)
  rw [sq, S2579I_sq]
  exact isIntegral_one.neg

lemma S2579_isIntegral_candidate : IsIntegral ℤ S2579Candidate :=
  (S2579_isIntegral_Y).add S2579_isIntegral_I

/-! ## 2. Kummer-Dedekind: a linear factor gives a residue-degree-one prime -/

open LeanFormal.IUT.XiFPaper.S2578Prime613Actual

section KummerDedekind

variable (θ : C)

/-- The monic residue polynomial of theta at 613. -/
abbrev S2579minpolyMod (θ : C) : (ZMod 613)[X] :=
  (minpoly ℤ θ).map (Int.castRingHom (ZMod 613))

theorem S2579minpolyMod_ne_zero : S2579minpolyMod θ ≠ 0 := by
  unfold S2579minpolyMod
  exact map_monic_ne_zero (minpoly.monic θ.isIntegral)

/-- If minpoly of theta has a root modulo 613, then X - C r is a monic factor of it. -/
theorem S2579_linearFactor_mem {r : ZMod 613} (hr : (S2579minpolyMod θ).IsRoot r) :
    (X - C r : (ZMod 613)[X]) ∈
      RingOfIntegers.monicFactorsMod (p := 613) (θ := θ) := by
  have hprime : Prime (X - C r : (ZMod 613)[X]) := prime_X_sub_C r
  have hdvd : (X - C r) ∣ S2579minpolyMod θ := Polynomial.dvd_iff_isRoot.mpr hr
  simp only [RingOfIntegers.monicFactorsMod, Multiset.mem_toFinset]
  exact (Polynomial.mem_normalizedFactors_iff (S2579minpolyMod_ne_zero θ)).mpr
    ⟨hprime.irreducible, monic_X_sub_C r, hdvd⟩

/-- Kummer-Dedekind at a linear factor. -/
theorem S2579_linearFactor_prime
    (hexp : ¬ (613 : ℕ) ∣ RingOfIntegers.exponent θ)
    {r : ZMod 613} (hr : (S2579minpolyMod θ).IsRoot r) :
    ∃ P : Ideal (C), P.IsPrime ∧
      P.LiesOver (Ideal.span {(613 : ℤ)}) ∧ P.inertiaDeg ℤ = 1 := by
  let Q : (ZMod 613)[X] := X - C r
  have hQmem : Q ∈ RingOfIntegers.monicFactorsMod (p := 613) (θ := θ) :=
    S2579_linearFactor_mem θ (r := r) hr
  let P0 : Ideal.primesOver (Ideal.span {(613 : ℤ)}) C :=
    (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod (p := 613) (θ := θ) hexp).symm
      ⟨Q, hQmem⟩
  refine ⟨P0.1, P0.prop.1, P0.prop.2, ?_⟩
  have h := NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
    (p := 613) (θ := θ) hexp (Q := Q) hQmem
  simpa [Q] using h

/-- Residue field of a degree-one prime over 613 is ZMod 613. -/
theorem S2579_quotient_equiv (P : Ideal (C)) [hPp : P.IsPrime]
    (hP : P.LiesOver (Ideal.span {(613 : ℤ)})) (hf : P.inertiaDeg ℤ = 1) :
    Nonempty (C ⧸ P ≃+* ZMod 613) := by
  haveI := hP
  have hmax : (Ideal.span {(613 : ℤ)}).IsMaximal := S2578_span613_isMaximal
  haveI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P (Ideal.span {(613 : ℤ)})
  letI : Algebra (ℤ ⧸ Ideal.span {(613 : ℤ)}) (C ⧸ P) :=
    Ideal.Quotient.algebraOfLiesOver P (Ideal.span {(613 : ℤ)})
  letI : Field (ℤ ⧸ Ideal.span {(613 : ℤ)}) := Ideal.Quotient.field _
  have hfin : Module.finrank (ℤ ⧸ Ideal.span {(613 : ℤ)})
      (C ⧸ P) = 1 := by
    rw [← Ideal.inertiaDeg_eq_of_isMaximal (R := ℤ) (S := C)
      (p := Ideal.span {(613 : ℤ)}) (q := P)]
    exact hf
  have hone : (1 : C ⧸ P) ≠ 0 := one_ne_zero
  have hsurj : Function.Surjective
      (algebraMap (ℤ ⧸ Ideal.span {(613 : ℤ)}) (C ⧸ P)) := by
    intro w
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
      (K := ℤ ⧸ Ideal.span {(613 : ℤ)})
      (V := C ⧸ P)
      (1 : C ⧸ P) hone).mp hfin w
    exact ⟨c, by simpa [Algebra.smul_def] using hc⟩
  have hinj : Function.Injective
      (algebraMap (ℤ ⧸ Ideal.span {(613 : ℤ)}) (C ⧸ P)) :=
    FaithfulSMul.algebraMap_injective _ _
  let e : (ℤ ⧸ Ideal.span {(613 : ℤ)}) ≃+* (C ⧸ P) :=
    RingEquiv.ofBijective _ ⟨hinj, hsurj⟩
  exact ⟨(e.symm).trans (Int.quotientSpanNatEquivZMod 613)⟩

end KummerDedekind

/-! ## 3. Localising the prime to S = O_F'[1/Cden] -/

section Localization

/-- The canonical quotient of the localised ring by the extended prime. -/
theorem S2579_localized_quotient_equiv (P0 : Ideal C) [hP0p : P0.IsPrime]
    (hP0 : P0.LiesOver (Ideal.span {(613 : ℤ)})) :
    ∃ P : Ideal S, P = P0.map (algebraMap C S) ∧ P.IsPrime ∧
      P.LiesOver (Ideal.span {(613 : ℤ)}) ∧ Nonempty (S ⧸ P ≃+* C ⧸ P0) := by
  haveI := hP0
  haveI hmax0 : (Ideal.span {(613 : ℤ)}).IsMaximal := S2578_span613_isMaximal
  haveI : P0.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P0 (Ideal.span {(613 : ℤ)})
  letI : Field (C ⧸ P0) := Ideal.Quotient.field P0
  have hdisj : Disjoint (Algebra.algebraMapSubmonoid C M : Set C) (P0 : Set C) :=
    S2578_disjoint P0 hP0p hP0
  have hprime : (P0.map (algebraMap C S)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint
      (M := Algebra.algebraMapSubmonoid C M) (S := S) P0 hP0p hdisj
  have hlies : (P0.map (algebraMap C S)).LiesOver P0 :=
    IsLocalization.liesOver_map_of_isPrime_disjoint
      (M := Algebra.algebraMapSubmonoid C M) (S := S) hdisj
  have hCden_ne : algebraMap ℤ (C ⧸ P0) (S2562HZcMonicCActual.Cden) ≠ 0 := by
    intro h
    have hmem : S2562HZcMonicCActual.Cden ∈ P0.under ℤ := by
      rw [Ideal.under_def, Ideal.mem_comap]
      exact Ideal.Quotient.eq_zero_iff_mem.mp
        (by simpa [Ideal.Quotient.algebraMap_eq] using h)
    rw [← hP0.over] at hmem
    exact S2578_not_dvd_Cden (Ideal.mem_span_singleton.mp hmem)
  have hunit : ∀ y : Algebra.algebraMapSubmonoid C M,
      IsUnit (Ideal.Quotient.mk P0 (y : C)) := by
    intro y
    obtain ⟨a, ha, hay⟩ := Submonoid.mem_map.mp y.2
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff a c).mp ha
    have hval : Ideal.Quotient.mk P0 (y : C) =
        (algebraMap ℤ (C ⧸ P0) (S2562HZcMonicCActual.Cden)) ^ n := by
      rw [← hay, ← hn]
      simp only [map_pow]
      congr 1
    rw [hval]
    have hunitC : IsUnit (algebraMap ℤ (C ⧸ P0) (S2562HZcMonicCActual.Cden)) :=
      (isUnit_iff_ne_zero (G₀ := C ⧸ P0)).mpr hCden_ne
    exact hunitC.pow n
  let φ : S →+* C ⧸ P0 :=
    IsLocalization.lift (M := Algebra.algebraMapSubmonoid C M)
      (g := Ideal.Quotient.mk P0) hunit
  have hφ_comp : φ.comp (algebraMap C S) = Ideal.Quotient.mk P0 :=
    IsLocalization.lift_comp hunit
  have hsurj : Function.Surjective φ := by
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨algebraMap C S x, DFunLike.congr_fun hφ_comp x⟩
  have hker : RingHom.ker φ = P0.map (algebraMap C S) := by
    apply le_antisymm
    · intro s hs
      rw [RingHom.mem_ker] at hs
      obtain ⟨x, m, hxm⟩ :=
        IsLocalization.exists_mk'_eq (Algebra.algebraMapSubmonoid C M) s
      have h0 : φ (IsLocalization.mk' S x m) = 0 := by
        rw [hxm]; exact hs
      have hgx : Ideal.Quotient.mk P0 x = 0 := by
        have hspec := (IsLocalization.lift_mk'_spec
          (M := Algebra.algebraMapSubmonoid C M) (S := S)
          (g := Ideal.Quotient.mk P0) hunit x 0 m).mp h0
        simpa using hspec
      have hxP0 : x ∈ P0 := Ideal.Quotient.eq_zero_iff_mem.mp hgx
      rw [← hxm]
      exact (IsLocalization.mk'_mem_map_algebraMap_iff
        (Algebra.algebraMapSubmonoid C M) S P0 x m).mpr
        ⟨1, (Algebra.algebraMapSubmonoid C M).one_mem, by simpa using hxP0⟩
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker]
      rw [show φ (algebraMap C S a) = Ideal.Quotient.mk P0 a from
        DFunLike.congr_fun hφ_comp a]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  let e : (S ⧸ RingHom.ker φ) ≃+* (C ⧸ P0) :=
    RingHom.quotientKerEquivOfSurjective hsurj
  have hunder : (P0.map (algebraMap C S)).under ℤ = P0.under ℤ := by
    calc (P0.map (algebraMap C S)).under ℤ
        = ((P0.map (algebraMap C S)).under C).under ℤ :=
            (Ideal.under_under (A := ℤ) (B := C)
              (𝔓 := P0.map (algebraMap C S))).symm
      _ = P0.under ℤ := congrArg (Ideal.under ℤ) hlies.over.symm
  refine ⟨P0.map (algebraMap C S), rfl, hprime, ?_, ?_⟩
  · refine ⟨? _⟩
    rw [hunder]
    exact hP0.over
  · exact ⟨(Ideal.quotEquivOfEq hker.symm).trans e⟩

end Localization

/-! ## 4. The actual candidate theta and the exact remaining arithmetic input -/

/-- The actual candidate primitive element, as an algebraic integer. -/
noncomputable def S2579Theta : C :=
  IsIntegralClosure.mk' C S2579Candidate S2579_isIntegral_candidate

@[simp] theorem S2579Theta_coe : (S2579Theta : S1720Field) = S2579Candidate := by
  simp [S2579Theta]

/-- The explicit degree-twelve monic integer polynomial computed externally (sympy)
as the minimal polynomial of the candidate a*S1687Y + i.  It is recorded here as the
target of the exact remaining certificate S2579P12Certificate; no theorem about it is
claimed in this file. -/
def S2579P12 : ℤ[X] :=
  X ^ 12 +
    C 3686686718987773113532422 * X ^ 10 +
    C 3795433823567007142194129160326239797448395456527 * X ^ 8 +
    C 997047820666501462053751168487623450855112506104272112674336787438501908 * X ^ 6 +
    C 526670884064012082338601412686825197828814168607551341522761345584496744723849057857765220810767 * X ^ 4 +
    C 52528898937498104220425280396744414010535592369189759840509931021767640039634491648742817305763558849812346150540279814 * X ^ 2 +
    C 17461463173174011582761234456954928886602725098127406596813431452619322589360189151409387505478783853884785910317333751256475494692028676046849

/-- The exact remaining certificate that the minimal polynomial of the candidate is
the explicit polynomial S2579P12. -/
def S2579P12Certificate : Prop :=
  minpoly ℤ S2579Theta = S2579P12

/-- The primitivity statement for the candidate: theta generates F' over Q. -/
def S2579Primitive : Prop :=
  IntermediateField.adjoin ℚ ({(S2579Theta : S1720Field)} : Set S1720Field) = ⊤

/-- The literal conductor condition: 613 does not divide the conductor exponent of
the order generated by theta. -/
def S2579Conductor613 : Prop :=
  ¬ (613 : ℕ) ∣ RingOfIntegers.exponent S2579Theta

/-- The literal residue condition: minpoly of theta has a root modulo 613. -/
def S2579LinearFactor613 : Prop :=
  ∃ r : ZMod 613, (S2579minpolyMod S2579Theta).IsRoot r

/-- Some primitive element of F' exists (Mathlib primitive element theorem). -/
theorem S2579_exists_primitive_field_element :
    ∃ x : S1720Field, IntermediateField.adjoin ℚ ({x} : Set S1720Field) = ⊤ :=
  Field.exists_primitive_element ℚ S1720Field

/-- The main Kummer-Dedekind step, in S. -/
theorem S2579_prime613_of_arithmetic (hc : S2579Conductor613)
    (hl : S2579LinearFactor613) :
    ∃ P : Ideal S, P.IsPrime ∧ P.LiesOver (Ideal.span {(613 : ℤ)}) ∧
      Nonempty (S ⧸ P ≃+* ZMod 613) := by
  obtain ⟨r, hr⟩ := hl
  obtain ⟨P0, hP0p, hP0over, hf⟩ := S2579_linearFactor_prime S2579Theta hc hr
  obtain ⟨eO⟩ := S2579_quotient_equiv P0 hP0over hf
  obtain ⟨P, hP, hPp, hPover, ⟨eS⟩⟩ := S2579_localized_quotient_equiv P0 hP0over
  exact ⟨P, hPp, hPover, ⟨eS.trans eO⟩⟩


/-! ## 5. Exact remaining input and general form of the Kummer-Dedekind step -/

/-- The exact remaining package: primitivity, conductor, and the linear residue factor. -/
def S2579ExactRemaining : Prop :=
  S2579Primitive ∧ S2579Conductor613 ∧ S2579LinearFactor613

/-- The conductor condition is exactly the codisjointness of the conductor with (613). -/
theorem S2579_conductor_iff :
    S2579Conductor613 ↔
      Codisjoint (Ideal.comap (algebraMap ℤ C) (conductor ℤ S2579Theta))
        (Ideal.span {(613 : ℤ)}) := by
  unfold S2579Conductor613
  exact RingOfIntegers.not_dvd_exponent_iff (K := S1720Field) (θ := S2579Theta) (p := 613)

/-- The Kummer-Dedekind step for an arbitrary integral element theta. -/
theorem S2579_prime613_of_theta (θ : C)
    (hexp : ¬ (613 : ℕ) ∣ RingOfIntegers.exponent θ)
    (hl : ∃ r : ZMod 613, (S2579minpolyMod θ).IsRoot r) :
    ∃ P : Ideal S, P.IsPrime ∧ P.LiesOver (Ideal.span {(613 : ℤ)}) ∧
      Nonempty (S ⧸ P ≃+* ZMod 613) := by
  obtain ⟨r, hr⟩ := hl
  obtain ⟨P0, hP0p, hP0over, hf⟩ := S2579_linearFactor_prime θ hexp hr
  obtain ⟨eO⟩ := S2579_quotient_equiv P0 hP0over hf
  obtain ⟨P, hP, hPp, hPover, ⟨eS⟩⟩ := S2579_localized_quotient_equiv P0 hP0over
  exact ⟨P, hPp, hPover, ⟨eS.trans eO⟩⟩

/-- The main unconditional conclusion conditional on the exact remaining package. -/
theorem S2579_prime613_of_exactRemaining (h : S2579ExactRemaining) :
    ∃ P : Ideal S, P.IsPrime ∧ P.LiesOver (Ideal.span {(613 : ℤ)}) ∧
      Nonempty (S ⧸ P ≃+* ZMod 613) :=
  S2579_prime613_of_arithmetic h.2.1 h.2.2

/-! ## 6. Axiom footprint -/


#print axioms S2579_linearFactor_mem
#print axioms S2579_linearFactor_prime
#print axioms S2579_quotient_equiv
#print axioms S2579_localized_quotient_equiv
#print axioms S2579_prime613_of_arithmetic
#print axioms S2579_prime613_of_theta
#print axioms S2579_conductor_iff
#print axioms S2579_prime613_of_exactRemaining
#print axioms S2579Theta
#print axioms S2579_isIntegral_candidate
#print axioms S2579_exists_primitive_field_element

end LeanFormal.IUT.XiFPaper.S2579Kummer613Actual