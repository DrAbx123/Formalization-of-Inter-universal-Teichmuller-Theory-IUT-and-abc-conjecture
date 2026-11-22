/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import tmp.sheaf.xif.paper.S2579Kummer613Actual
import tmp.sheaf.xif.paper.S2580P12CertificateActual
import tmp.sheaf.xif.paper.S2584PrimeDegreeOneActual
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.FieldTheory.PrimitiveElement

/-!
# S2669: the degree-one prime of S over 1249 via Kummer-Dedekind

This file is the p = 1249 analogue of
tmp/sheaf/xif/paper/S2579Kummer613Actual.lean.  The mathematical objects are
those of S2565: C = O_F' is the ring of integers of F' = S1720Field and
S = O_F'[1/Cden] is the localised ring; S2579Theta is the actual candidate
a * S1720Lift S1687Y + i of S2579.

## What is proved here

For an arbitrary theta : C, if

* hexp : not (1249 : Nat) | RingOfIntegers.exponent theta (1249 is prime to the
  conductor exponent of theta), and
* hl : exists r : ZMod 1249, (S2669minpolyMod theta).IsRoot r (the minimal
  polynomial of theta has a root modulo 1249),

then S = O_F'[1/Cden] has a prime P over (1249) with
S / P =+* ZMod 1249:

  S2669_prime1249_of_theta.

The proof is a verbatim copy of the p = 613 proof: the Kummer-Dedekind
bijection NumberField.Ideal.primesOverSpanEquivMonicFactorsMod is generic in
the prime, and only the following inputs are prime-specific:

* Fact (Nat.Prime 1249) (so that (1249) is maximal and the Kummer-Dedekind
  bijection applies);
* not (1249 : Z) | Cden (the localisation denominator is not divisible by
  1249; proved here by norm_num, since Cden = c0 * Dval with
  Dval mod 1249 = 599 and c0 mod 1249 = 248);
* the residue field ZMod 1249 and the quotient identification
  Int.quotientSpanNatEquivZMod 1249.

Thus the only essential 613's in the template are: the prime 613 itself
(used for Fact (Nat.Prime _), the span (613), the ring ZMod 613, and the
Kummer-Dedekind parameter p), the residue values r : ZMod 613, and the
conductor exponent divisibility.  Everything else (the theta/candidate
construction, S, C, Cden, the localisation proof) is independent of the prime.

Both arithmetic inputs are PROVED unconditionally in this file:

* the residue input S2669LinearFactor1249 (section 7): modulo 1249 the
  polynomial S2579P12 factors into the twelve linear factors with roots
  45, 48, 124, 127, 143, 222 and their negatives, and minpoly divides S2579P12
  (S2580_minpoly_dvd);
* the conductor input S2669Conductor1249 (section 8): no prime above 1249
  contains the conductor of Z[theta], because the reduction of P12 modulo 1249
  is separable (twelve distinct roots), so P12 and its derivative satisfy a
  Bezout identity; combined with
  conductor * differentIdeal = span {aeval theta P12'} (S2582_P12Certificate)
  this is a contradiction, and the usual minimality of the exponent upgrades
  this to not 1249 | RingOfIntegers.exponent S2579Theta.

Consequently S2669_prime1249 and S2669_exists_primeDegreeOne are
UNCONDITIONAL: S has an actual prime over (1249) whose residue field is
ZMod 1249, and O_F' has an actual prime p above 1249 of inertia degree one
with C/p =+* ZMod 1249.

No sorry, axiom, True/PUnit gate or native_decide is used.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2669Kummer1249Actual

open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2579Kummer613Actual
open LeanFormal.IUT.XiFPaper.S2580P12CertificateActual
open LeanFormal.IUT.XiFPaper.S2582P12ClosedActual
open LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual

local instance : Fact (Nat.Prime 1249) := ⟨by norm_num⟩

/-! ## 1. The localisation denominator is prime to 1249 -/

/-- 1249 is coprime to the localisation denominator Cden = c0 * Dval. -/
theorem S2669_not_dvd_Cden : ¬ (1249 : ℤ) ∣ S2562HZcMonicCActual.Cden := by
  unfold S2562HZcMonicCActual.Cden S2562HZcMonicCActual.c0 S2562HZcMonicCActual.Dval
  norm_num

/-- The ideal (1249) of Z is maximal. -/
lemma S2669_span1249_isMaximal : (Ideal.span {(1249 : ℤ)}).IsMaximal :=
  Int.ideal_span_isMaximal_of_prime 1249

lemma S2669_algebraMap_c_not_mem (p : Ideal C) (hpp : p.IsPrime)
    (hp : p.LiesOver (Ideal.span {(1249 : ℤ)})) :
    algebraMap ℤ C c ∉ p := by
  haveI := hp
  intro h
  have h1 : c ∈ (Ideal.span {(1249 : ℤ)} : Ideal ℤ) :=
    (Ideal.mem_of_liesOver p (Ideal.span {(1249 : ℤ)}) c).mpr h
  rw [Ideal.mem_span_singleton] at h1
  exact S2669_not_dvd_Cden (by simpa [S2565ConcreteIntegralClosureCActual.c] using h1)

lemma S2669_disjoint (p : Ideal C) (hpp : p.IsPrime)
    (hp : p.LiesOver (Ideal.span {(1249 : ℤ)})) :
    Disjoint (Algebra.algebraMapSubmonoid C M : Set C) (p : Set C) := by
  rw [Set.disjoint_left]
  intro x hx hxp
  have hx' : x ∈ M.map (algebraMap ℤ C) := hx
  obtain ⟨a, ha, hxa⟩ := Submonoid.mem_map.mp hx'
  rw [← hxa] at hxp
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff a c).mp ha
  have hpow : (algebraMap ℤ C c) ^ n ∈ p := by
    rw [← map_pow, hn]
    exact hxp
  exact S2669_algebraMap_c_not_mem p hpp hp (hpp.mem_of_pow_mem n hpow)

/-! ## 2. Kummer-Dedekind: a linear factor gives a residue-degree-one prime -/

section KummerDedekind

variable (θ : C)

/-- The monic residue polynomial of theta at 1249. -/
abbrev S2669minpolyMod (θ : C) : (ZMod 1249)[X] :=
  (minpoly ℤ θ).map (Int.castRingHom (ZMod 1249))

theorem S2669minpolyMod_ne_zero : S2669minpolyMod θ ≠ 0 := by
  unfold S2669minpolyMod
  exact map_monic_ne_zero (minpoly.monic θ.isIntegral)

/-- If minpoly of theta has a root modulo 1249, then X - C r is a monic factor. -/
theorem S2669_linearFactor_mem {r : ZMod 1249} (hr : (S2669minpolyMod θ).IsRoot r) :
    (X - C r : (ZMod 1249)[X]) ∈
      RingOfIntegers.monicFactorsMod (p := 1249) (θ := θ) := by
  have hprime : Prime (X - C r : (ZMod 1249)[X]) := prime_X_sub_C r
  have hdvd : (X - C r) ∣ S2669minpolyMod θ := Polynomial.dvd_iff_isRoot.mpr hr
  simp only [RingOfIntegers.monicFactorsMod, Multiset.mem_toFinset]
  exact (Polynomial.mem_normalizedFactors_iff (S2669minpolyMod_ne_zero θ)).mpr
    ⟨hprime.irreducible, monic_X_sub_C r, hdvd⟩

/-- Kummer-Dedekind at a linear factor over 1249. -/
theorem S2669_linearFactor_prime
    (hexp : ¬ (1249 : ℕ) ∣ RingOfIntegers.exponent θ)
    {r : ZMod 1249} (hr : (S2669minpolyMod θ).IsRoot r) :
    ∃ P : Ideal (C), P.IsPrime ∧
      P.LiesOver (Ideal.span {(1249 : ℤ)}) ∧ P.inertiaDeg ℤ = 1 := by
  let Q : (ZMod 1249)[X] := X - C r
  have hQmem : Q ∈ RingOfIntegers.monicFactorsMod (p := 1249) (θ := θ) :=
    S2669_linearFactor_mem θ (r := r) hr
  let P0 : Ideal.primesOver (Ideal.span {(1249 : ℤ)}) C :=
    (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod (p := 1249) (θ := θ) hexp).symm
      ⟨Q, hQmem⟩
  refine ⟨P0.1, P0.prop.1, P0.prop.2, ?_⟩
  have h := NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
    (p := 1249) (θ := θ) hexp (Q := Q) hQmem
  simpa [Q] using h

/-- The residue field of a degree-one prime over 1249 is ZMod 1249. -/
theorem S2669_quotient_equiv (P : Ideal (C)) [hPp : P.IsPrime]
    (hP : P.LiesOver (Ideal.span {(1249 : ℤ)})) (hf : P.inertiaDeg ℤ = 1) :
    Nonempty (C ⧸ P ≃+* ZMod 1249) := by
  haveI := hP
  have hmax : (Ideal.span {(1249 : ℤ)}).IsMaximal := S2669_span1249_isMaximal
  haveI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P (Ideal.span {(1249 : ℤ)})
  letI : Algebra (ℤ ⧸ Ideal.span {(1249 : ℤ)}) (C ⧸ P) :=
    Ideal.Quotient.algebraOfLiesOver P (Ideal.span {(1249 : ℤ)})
  letI : Field (ℤ ⧸ Ideal.span {(1249 : ℤ)}) := Ideal.Quotient.field _
  have hfin : Module.finrank (ℤ ⧸ Ideal.span {(1249 : ℤ)})
      (C ⧸ P) = 1 := by
    rw [← Ideal.inertiaDeg_eq_of_isMaximal (R := ℤ) (S := C)
      (p := Ideal.span {(1249 : ℤ)}) (q := P)]
    exact hf
  have hone : (1 : C ⧸ P) ≠ 0 := one_ne_zero
  have hsurj : Function.Surjective
      (algebraMap (ℤ ⧸ Ideal.span {(1249 : ℤ)}) (C ⧸ P)) := by
    intro w
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
      (K := ℤ ⧸ Ideal.span {(1249 : ℤ)})
      (V := C ⧸ P)
      (1 : C ⧸ P) hone).mp hfin w
    exact ⟨c, by simpa [Algebra.smul_def] using hc⟩
  have hinj : Function.Injective
      (algebraMap (ℤ ⧸ Ideal.span {(1249 : ℤ)}) (C ⧸ P)) :=
    FaithfulSMul.algebraMap_injective _ _
  let e : (ℤ ⧸ Ideal.span {(1249 : ℤ)}) ≃+* (C ⧸ P) :=
    RingEquiv.ofBijective _ ⟨hinj, hsurj⟩
  exact ⟨(e.symm).trans (Int.quotientSpanNatEquivZMod 1249)⟩

end KummerDedekind

/-! ## 3. Localising the prime to S = O_F'[1/Cden] -/

section Localization

/-- The canonical quotient of the localised ring by the extended prime at 1249. -/
theorem S2669_localized_quotient_equiv (P0 : Ideal C) [hP0p : P0.IsPrime]
    (hP0 : P0.LiesOver (Ideal.span {(1249 : ℤ)})) :
    ∃ P : Ideal S, P = P0.map (algebraMap C S) ∧ P.IsPrime ∧
      P.LiesOver (Ideal.span {(1249 : ℤ)}) ∧ Nonempty (S ⧸ P ≃+* C ⧸ P0) := by
  haveI := hP0
  haveI hmax0 : (Ideal.span {(1249 : ℤ)}).IsMaximal := S2669_span1249_isMaximal
  haveI : P0.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P0 (Ideal.span {(1249 : ℤ)})
  letI : Field (C ⧸ P0) := Ideal.Quotient.field P0
  have hdisj : Disjoint (Algebra.algebraMapSubmonoid C M : Set C) (P0 : Set C) :=
    S2669_disjoint P0 hP0p hP0
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
    exact S2669_not_dvd_Cden (Ideal.mem_span_singleton.mp hmem)
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

/-! ## 4. The main Kummer-Dedekind step at 1249 -/

/-- The Kummer-Dedekind step for an arbitrary integral element theta. -/
theorem S2669_prime1249_of_theta (θ : C)
    (hexp : ¬ (1249 : ℕ) ∣ RingOfIntegers.exponent θ)
    (hl : ∃ r : ZMod 1249, (S2669minpolyMod θ).IsRoot r) :
    ∃ P : Ideal S, P.IsPrime ∧ P.LiesOver (Ideal.span {(1249 : ℤ)}) ∧
      Nonempty (S ⧸ P ≃+* ZMod 1249) := by
  obtain ⟨r, hr⟩ := hl
  obtain ⟨P0, hP0p, hP0over, hf⟩ := S2669_linearFactor_prime θ hexp hr
  obtain ⟨eO⟩ := S2669_quotient_equiv P0 hP0over hf
  obtain ⟨P, hP, hPp, hPover, ⟨eS⟩⟩ := S2669_localized_quotient_equiv P0 hP0over
  exact ⟨P, hPp, hPover, ⟨eS.trans eO⟩⟩

/-! ## 5. The actual theta of S2579 and the exact remaining arithmetic inputs -/

/-- The literal conductor condition at 1249 for the actual theta of S2579. -/
def S2669Conductor1249 : Prop :=
  ¬ (1249 : ℕ) ∣ RingOfIntegers.exponent S2579Theta

/-- The literal residue condition at 1249 for the actual theta of S2579.  This
is proved unconditionally in section 7 (S2669LinearFactor1249_proof). -/
def S2669LinearFactor1249 : Prop :=
  ∃ r : ZMod 1249, (S2669minpolyMod S2579Theta).IsRoot r

/-- The conductor condition is exactly the codisjointness of the conductor with (1249). -/
theorem S2669_conductor_iff :
    S2669Conductor1249 ↔
      Codisjoint (Ideal.comap (algebraMap ℤ C) (conductor ℤ S2579Theta))
        (Ideal.span {(1249 : ℤ)}) := by
  unfold S2669Conductor1249
  exact RingOfIntegers.not_dvd_exponent_iff (K := S1720Field) (θ := S2579Theta) (p := 1249)

/-! ## 6. The twelve linear factors of S2579P12 modulo 1249

Modulo 1249 the polynomial S2579P12 factors as

  (X - 45)(X - 48)(X - 124)(X - 127)(X - 143)(X - 222)
    (X + 45)(X + 48)(X + 124)(X + 127)(X + 143)(X + 222),

i.e. the twelve roots are the pairs +-r_k, where the squares r_k^2 = w_k are the
six roots of S2580G modulo 1249.  This is the p = 1249 analogue of
S2579P12_mod613_eq from S2580P12CertificateActual. -/

/-- The six roots of S2580G modulo 1249: the squares of the twelve roots of
S2579P12 modulo 1249. -/
def S2669w : Fin 6 → ZMod 1249 := ![776, 1055, 388, 1141, 465, 573]

/-- Chosen square roots of the six values S2669w. -/
def S2669r : Fin 6 → ZMod 1249 := ![45, 48, 124, 127, 143, 222]

theorem S2669r_sq (k : Fin 6) : S2669r k * S2669r k = S2669w k := by
  fin_cases k <;> decide

theorem S2669w_injective : Function.Injective S2669w := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; revert h; decide)

/-- S2580G reduced modulo 1249. -/
def S2669G1249 : (ZMod 1249)[X] := S2580G.map (Int.castRingHom (ZMod 1249))

theorem S2669G1249_monic : S2669G1249.Monic :=
  S2580G_monic.map _

theorem S2669G1249_natDegree : S2669G1249.natDegree = 6 := by
  rw [S2669G1249, S2580G_monic.natDegree_map, S2580G_natDegree]

theorem S2669G1249_root (k : Fin 6) : S2669G1249.IsRoot (S2669w k) := by
  fin_cases k <;>
    (simp [S2669G1249, S2580G, S2669w, Polynomial.IsRoot, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
     decide)

/-- The product of the six linear factors of S2580G modulo 1249 divides it. -/
theorem S2669Q_dvd : (∏ k : Fin 6, (X - C (S2669w k))) ∣ S2669G1249 := by
  have hpair : (↑(Finset.univ : Finset (Fin 6)) : Set (Fin 6)).Pairwise
      (Function.onFun IsCoprime (fun k => (X - C (S2669w k)))) := by
    intro a _ b _ hab
    apply isCoprime_X_sub_C_of_isUnit_sub
    rw [isUnit_iff_ne_zero]
    intro hsub
    exact hab (S2669w_injective (sub_eq_zero.mp hsub))
  have hdvd : ∀ k ∈ (Finset.univ : Finset (Fin 6)), (X - C (S2669w k)) ∣ S2669G1249 := by
    intro k _
    rw [Polynomial.dvd_iff_isRoot]
    exact S2669G1249_root k
  simpa using Finset.prod_dvd_of_coprime hpair hdvd

theorem S2669G1249_eq : S2669G1249 = ∏ k : Fin 6, (X - C (S2669w k)) := by
  have hQ_monic : (∏ k : Fin 6, (X - C (S2669w k))).Monic :=
    monic_prod_X_sub_C _ _
  have hQ_deg : (∏ k : Fin 6, (X - C (S2669w k))).natDegree = 6 := by
    rw [natDegree_finsetProd_X_sub_C_eq_card]
    simp
  exact eq_of_monic_of_dvd_of_natDegree_le hQ_monic S2669G1249_monic S2669Q_dvd
    (by rw [S2669G1249_natDegree, hQ_deg])

/-- The full factorisation of S2579P12 modulo 1249 into twelve linear factors. -/
theorem S2669P12_mod1249_eq :
    S2579P12.map (Int.castRingHom (ZMod 1249)) =
      ∏ k : Fin 6, ((X - C (S2669r k)) * (X + C (S2669r k))) := by
  have hmap : S2579P12.map (Int.castRingHom (ZMod 1249)) = S2669G1249.comp (X ^ 2) := by
    rw [S2579P12_eq_comp, Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X]
    rfl
  rw [hmap, S2669G1249_eq]
  have hcomp : (∏ k : Fin 6, (X - C (S2669w k))).comp (X ^ 2) =
      ∏ k : Fin 6, ((X - C (S2669w k)).comp (X ^ 2)) := by
    simp only [Polynomial.comp_eq_aeval]
    rw [map_prod]
  rw [hcomp]
  refine Finset.prod_congr rfl ?_
  intro k _
  have hw : C (S2669w k) = C (S2669r k) * C (S2669r k) := by
    rw [← Polynomial.C_mul, ← S2669r_sq k]
  rw [Polynomial.sub_comp, Polynomial.C_comp, Polynomial.X_comp, hw]
  ring

/-! ## 7. The linear residue factor at 1249 -/

/-- A linear factor gives a root. -/
theorem S2669_root_of_dvd {p : (ZMod 1249)[X]} {c : ZMod 1249} (h : (X - C c) ∣ p) :
    p.IsRoot c := by
  obtain ⟨h', rfl⟩ := h
  simp [Polynomial.IsRoot, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C]

/-- A monic irreducible divisor of a linear polynomial is that linear polynomial. -/
theorem S2669_eq_linear_of_dvd {g : (ZMod 1249)[X]} (hg : g.Monic) (hgirr : Irreducible g)
    {c : ZMod 1249} (h : g ∣ X - C c) : g = X - C c := by
  have hle : g.natDegree ≤ 1 := by
    have h1 := natDegree_le_of_dvd h (monic_X_sub_C c).ne_zero
    rwa [natDegree_X_sub_C] at h1
  have hpos : 0 < g.natDegree := hgirr.natDegree_pos
  have h1 : g.natDegree = 1 := by omega
  exact (eq_of_monic_of_dvd_of_natDegree_le hg (monic_X_sub_C c) h
    (by rw [natDegree_X_sub_C]; omega)).symm

/-- S2669LinearFactor1249, unconditionally: the minimal polynomial of the
actual theta has a root modulo 1249.

This is proved from the factorisation of S2579P12 into twelve linear factors
modulo 1249 and the divisibility minpoly Z S2579Theta ∣ S2579P12; any monic
irreducible factor of the minimal polynomial modulo 1249 divides one of the
twelve linear factors, hence is linear.  It is the p = 1249 analogue of
S2580LinearFactor613. -/
theorem S2669LinearFactor1249_proof : S2669LinearFactor1249 := by
  unfold S2669LinearFactor1249
  have hdvd : S2669minpolyMod S2579Theta ∣ S2579P12.map (Int.castRingHom (ZMod 1249)) := by
    unfold S2669minpolyMod
    exact Polynomial.map_dvd _ S2580_minpoly_dvd
  rw [S2669P12_mod1249_eq] at hdvd
  have hmonic : (S2669minpolyMod S2579Theta).Monic := S2580_minpoly_monic.map _
  have hnotunit : ¬ IsUnit (S2669minpolyMod S2579Theta) := by
    rw [hmonic.isUnit_iff]
    intro h1
    have hdeg : (S2669minpolyMod S2579Theta).natDegree = 0 := by rw [h1]; simp
    have hdeg' : (minpoly ℤ S2579Theta).natDegree = 0 := by
      rw [← S2580_minpoly_monic.natDegree_map (Int.castRingHom (ZMod 1249))]
      exact hdeg
    have hpos : 0 < (minpoly ℤ S2579Theta).natDegree := by
      have h := minpoly.degree_pos S2579Theta.isIntegral
      rw [Polynomial.degree_eq_natDegree S2580_minpoly_monic.ne_zero] at h
      exact WithBot.coe_lt_coe.mp h
    omega
  obtain ⟨g, hgmonic, hgirr, hgdvd⟩ := Polynomial.exists_monic_irreducible_factor _ hnotunit
  have hgdvd' : g ∣ ∏ k : Fin 6, ((X - C (S2669r k)) * (X + C (S2669r k))) :=
    hgdvd.trans hdvd
  have hprime : Prime g := hgirr.prime
  obtain ⟨k, _, hk⟩ :=
    (Prime.dvd_finsetProd_iff hprime (fun k : Fin 6 => (X - C (S2669r k)) * (X + C (S2669r k)))).mp
      hgdvd'
  rcases (Prime.dvd_mul hprime).mp hk with hk | hk
  · refine ⟨S2669r k, ?_⟩
    rw [S2669_eq_linear_of_dvd hgmonic hgirr hk] at hgdvd
    exact S2669_root_of_dvd hgdvd
  · have hk' : g ∣ X - C (-(S2669r k)) := by
      rwa [show X - C (-(S2669r k)) = X + C (S2669r k) from by
        rw [Polynomial.C_neg]; ring]
    refine ⟨-(S2669r k), ?_⟩
    rw [S2669_eq_linear_of_dvd hgmonic hgirr hk'] at hgdvd
    exact S2669_root_of_dvd hgdvd

/-! ## 8. No prime above 1249 contains the conductor

This removes the last arithmetic input, exactly as S2584 does for 613.  The
argument only uses that the reduction of S2579P12 modulo 1249 is separable (it
has twelve distinct roots, section 7) and that the minimal polynomial of theta
is S2579P12 (S2582_P12Certificate). -/

/-- The twelve roots of S2579P12 modulo 1249: for each of the six roots
S2669r k of the even sextic we take both signs. -/
def S2669root : Fin 6 × Bool → ZMod 1249
  | (k, false) => S2669r k
  | (k, true) => -S2669r k

/-- The reduction of S2579P12 modulo 1249 is the product of the twelve linear
factors attached to the distinct roots S2669root. -/
theorem S2669_factorization :
    S2579P12.map (Int.castRingHom (ZMod 1249)) =
      ∏ kb : Fin 6 × Bool, (X - C (S2669root kb)) := by
  rw [S2669P12_mod1249_eq, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro k _
  rw [Fintype.prod_bool]
  simp only [S2669root]
  rw [Polynomial.C_neg, sub_neg_eq_add, mul_comm]

/-- The twelve roots are pairwise distinct modulo 1249. -/
theorem S2669_root_injective : Function.Injective S2669root := by
  rintro ⟨a, ba⟩ ⟨b, bb⟩ h
  fin_cases a <;> fin_cases b <;> cases ba <;> cases bb <;>
    simp only [S2669root, S2669r] at h ⊢
  all_goals first | rfl | (exfalso; revert h; decide)

/-- S2579P12 is separable modulo 1249: it is a product of distinct linear
factors. -/
theorem S2669_p12map_separable :
    (S2579P12.map (Int.castRingHom (ZMod 1249))).Separable := by
  rw [S2669_factorization]
  exact (Polynomial.separable_prod_X_sub_C_iff).mpr S2669_root_injective

/-- A Bezout identity modulo 1249 between P12 and its derivative. -/
theorem S2669_p12map_bezout :
    ∃ a b : (ZMod 1249)[X],
      a * S2579P12.map (Int.castRingHom (ZMod 1249)) +
        b * derivative (S2579P12.map (Int.castRingHom (ZMod 1249))) = 1 :=
  (Polynomial.separable_def' _).mp S2669_p12map_separable

/-- If a prime P above 1249 contained the conductor, then the residue of theta
in the residue field would be a common root of P12 and P12' modulo 1249,
contradicting the Bezout identity S2669_p12map_bezout. -/
theorem S2669_no_prime_over1249_le_conductor (P : Ideal C) [hPp : P.IsPrime]
    (hP : P.LiesOver (Ideal.span {(1249 : ℤ)})) :
    ¬ conductor ℤ S2579Theta ≤ P := by
  intro hle
  haveI := hP
  have hmul := conductor_mul_differentIdeal (A := ℤ) (K := ℚ) (L := S1720Field)
    S2579Theta S2584_hprim
  have hmem : aeval S2579Theta (derivative (minpoly ℤ S2579Theta)) ∈ P := by
    have hspan : Ideal.span {aeval S2579Theta (derivative (minpoly ℤ S2579Theta))} ≤ P := by
      rw [← hmul]
      exact le_trans Ideal.mul_le_right hle
    exact (Ideal.span_singleton_le_iff_mem P).mp hspan
  rw [S2582_P12Certificate] at hmem
  let t : C ⧸ P := Ideal.Quotient.mk P S2579Theta
  let psi : ZMod 1249 →+* (C ⧸ P) :=
    (algebraMap (ℤ ⧸ Ideal.span {(1249 : ℤ)}) (C ⧸ P)).comp
      (Int.quotientSpanNatEquivZMod 1249).symm.toRingHom
  letI : Algebra (ZMod 1249) (C ⧸ P) := psi.toAlgebra
  have hcompat : psi.comp (Int.castRingHom (ZMod 1249)) =
      (Ideal.Quotient.mk P).comp (algebraMap ℤ C) := by
    ext x
    change (algebraMap (ℤ ⧸ Ideal.span {(1249 : ℤ)}) (C ⧸ P))
        ((Int.quotientSpanNatEquivZMod 1249).symm (Int.castRingHom (ZMod 1249) x))
      = (Ideal.Quotient.mk P) (algebraMap ℤ C x)
    have hx : (Int.quotientSpanNatEquivZMod 1249).symm (Int.castRingHom (ZMod 1249) x)
        = Ideal.Quotient.mk (Ideal.span {(1249 : ℤ)}) x :=
      DFunLike.congr_fun (Int.quotientSpanNatEquivZMod_comp_castRingHom 1249) x
    rw [hx]
    exact Ideal.Quotient.algebraMap_mk_of_liesOver P (Ideal.span {(1249 : ℤ)}) x
  have hf0 :
      (S2579P12.map (Int.castRingHom (ZMod 1249))).eval₂ psi t = 0 := by
    rw [Polynomial.eval₂_map, hcompat]
    have h := Polynomial.hom_eval₂ S2579P12 (algebraMap ℤ C) (Ideal.Quotient.mk P) S2579Theta
    rw [← h, ← Polynomial.aeval_def, S2580_aeval_Theta]
    simp
  have hf'0 :
      (derivative (S2579P12.map (Int.castRingHom (ZMod 1249)))).eval₂ psi t = 0 := by
    rw [Polynomial.derivative_map, Polynomial.eval₂_map, hcompat]
    have h := Polynomial.hom_eval₂ (derivative S2579P12) (algebraMap ℤ C)
      (Ideal.Quotient.mk P) S2579Theta
    rw [← h, ← Polynomial.aeval_def]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  obtain ⟨a, b, hab⟩ := S2669_p12map_bezout
  have h1 := congrArg (fun p : (ZMod 1249)[X] => p.eval₂ psi t) hab
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_one,
    hf0, hf'0, mul_zero, add_zero] at h1
  exact zero_ne_one h1

/-- No prime above 1249 contains the conductor, so the conductor and 1249 C
generate the unit ideal. -/
theorem S2669_conductor_sup :
    conductor ℤ S2579Theta ⊔ Ideal.span {(1249 : C)} = ⊤ := by
  by_contra hne
  obtain ⟨P, hPmax, hPle⟩ := Ideal.exists_le_maximal _ hne
  haveI hPp : P.IsPrime := hPmax.isPrime
  have h1249 : (1249 : C) ∈ P :=
    hPle (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton (1249 : C))))
  have hPover : P.LiesOver (Ideal.span {(1249 : ℤ)}) := by
    refine ⟨?_.symm⟩
    have hle : Ideal.span {(1249 : ℤ)} ≤ P.under ℤ := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
      simpa using h1249
    have hne_top : P.under ℤ ≠ ⊤ := by
      intro htop
      have h1 : (1 : ℤ) ∈ P.under ℤ := by rw [htop]; exact Submodule.mem_top
      rw [Ideal.under_def, Ideal.mem_comap] at h1
      have h2 : (1 : C) ∈ P := by simpa using h1
      exact hPmax.ne_top (Ideal.eq_top_iff_one P |>.mpr h2)
    exact (Int.ideal_span_isMaximal_of_prime 1249).eq_of_le hne_top hle
  exact S2669_no_prime_over1249_le_conductor P hPover (le_trans le_sup_left hPle)

/-- The last arithmetic input: 1249 does not divide the exponent of the
conductor of Z[theta]. -/
theorem S2669_conductor1249 : S2669Conductor1249 := by
  unfold S2669Conductor1249
  intro hdiv
  obtain ⟨m, hm⟩ := hdiv
  have hunit : IsUnit (Ideal.Quotient.mk (conductor ℤ S2579Theta) (1249 : C)) := by
    have hsup := S2669_conductor_sup
    rw [Ideal.eq_top_iff_one] at hsup
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hsup
    rw [Ideal.mem_span_singleton] at hb
    obtain ⟨y, hy⟩ := hb
    have hmul1 : Ideal.Quotient.mk (conductor ℤ S2579Theta) (1249 : C) *
        Ideal.Quotient.mk (conductor ℤ S2579Theta) y = 1 := by
      rw [← map_mul, ← hy]
      have hb1 : b = 1 - a := by linear_combination hab
      rw [hb1, map_sub, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr ha, sub_zero]
    exact isUnit_iff_exists.mpr ⟨_, hmul1, by rw [mul_comm]; exact hmul1⟩
  have hmpos : 0 < m := by
    have hpos := S2584_exponent_pos
    omega
  have hmlt : m < RingOfIntegers.exponent S2579Theta := by
    rw [hm]
    nlinarith [hmpos]
  have hexp_mem : (RingOfIntegers.exponent S2579Theta : C) ∈ conductor ℤ S2579Theta :=
    Int.absNorm_under_mem (conductor ℤ S2579Theta)
  have hm_mem : (m : C) ∈ conductor ℤ S2579Theta := by
    have h0 : Ideal.Quotient.mk (conductor ℤ S2579Theta) (m : C) = 0 := by
      have hprod : Ideal.Quotient.mk (conductor ℤ S2579Theta) (m : C) *
          Ideal.Quotient.mk (conductor ℤ S2579Theta) (1249 : C) = 0 := by
        rw [← map_mul]
        have hcast : (m : C) * (1249 : C) = (RingOfIntegers.exponent S2579Theta : C) := by
          rw [hm, Nat.cast_mul]
          ring
        rw [hcast, Ideal.Quotient.eq_zero_iff_mem.mpr hexp_mem]
      exact (IsUnit.mul_left_eq_zero hunit).mp hprod
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  have hle : RingOfIntegers.exponent S2579Theta ≤ m := by
    rw [RingOfIntegers.exponent_eq_sInf]
    exact Nat.sInf_le ⟨hmpos, hm_mem⟩
  omega

/-! ## 9. Main theorems for the actual theta of S2579 -/

/-- Kummer-Dedekind at 1249 for the actual theta of S2579, conditional on the
conductor and residue inputs.  This is the p = 1249 analogue of
S2579_prime613_of_arithmetic. -/
theorem S2669_prime1249_of_arithmetic (hc : S2669Conductor1249)
    (hl : S2669LinearFactor1249) :
    ∃ P : Ideal S, P.IsPrime ∧ P.LiesOver (Ideal.span {(1249 : ℤ)}) ∧
      Nonempty (S ⧸ P ≃+* ZMod 1249) :=
  S2669_prime1249_of_theta S2579Theta hc hl

/-- Kummer-Dedekind at 1249 for the actual theta of S2579, with the residue
input discharged: only the conductor condition remains.

The conclusion is an actual prime P of S = O_F'[1/Cden] lying over (1249)
whose residue field is ZMod 1249. -/
theorem S2669_prime1249_of_conductor (hc : S2669Conductor1249) :
    ∃ P : Ideal S, P.IsPrime ∧ P.LiesOver (Ideal.span {(1249 : ℤ)}) ∧
      Nonempty (S ⧸ P ≃+* ZMod 1249) :=
  S2669_prime1249_of_arithmetic hc S2669LinearFactor1249_proof

/-- The headline Kummer-Dedekind step at 1249, UNCONDITIONAL: S has a prime
over (1249) whose residue field is ZMod 1249.  This is the p = 1249 analogue of
S2584_prime613. -/
theorem S2669_prime1249 :
    ∃ P : Ideal S, P.IsPrime ∧ P.LiesOver (Ideal.span {(1249 : ℤ)}) ∧
      Nonempty (S ⧸ P ≃+* ZMod 1249) :=
  S2669_prime1249_of_conductor S2669_conductor1249

/-- The actual prime p of O_F' above 1249 with inertia degree one, its extension
P = p.map (algebraMap C S) to S, and the two residue equivalences, all
unconditional.  This is the p = 1249 analogue of S2584_exists_primeDegreeOne. -/
theorem S2669_exists_primeDegreeOne :
    ∃ p : Ideal C, p.IsPrime ∧ p.LiesOver (Ideal.span {(1249 : ℤ)}) ∧
      p.inertiaDeg ℤ = 1 ∧ Nonempty (C ⧸ p ≃+* ZMod 1249) ∧
      ∃ P : Ideal S, P = p.map (algebraMap C S) ∧ P.IsPrime ∧
        P.LiesOver (Ideal.span {(1249 : ℤ)}) ∧
        Nonempty (S ⧸ P ≃+* ZMod 1249) := by
  obtain ⟨r, hr⟩ := S2669LinearFactor1249_proof
  obtain ⟨p, hp_prime, hp_over, hp_deg⟩ :=
    S2669_linearFactor_prime S2579Theta S2669_conductor1249 hr
  haveI : p.IsPrime := hp_prime
  obtain ⟨eO⟩ := S2669_quotient_equiv p hp_over hp_deg
  obtain ⟨P, hP_eq, hP_prime, hP_over, ⟨eS⟩⟩ :=
    S2669_localized_quotient_equiv p hp_over
  exact ⟨p, hp_prime, hp_over, hp_deg, ⟨eO⟩, P, hP_eq, hP_prime, hP_over, ⟨eS.trans eO⟩⟩

/-! ## 10. Axiom footprint -/

#print axioms S2669_linearFactor_mem
#print axioms S2669_linearFactor_prime
#print axioms S2669_quotient_equiv
#print axioms S2669_localized_quotient_equiv
#print axioms S2669_prime1249_of_theta
#print axioms S2669r_sq
#print axioms S2669G1249_eq
#print axioms S2669P12_mod1249_eq
#print axioms S2669LinearFactor1249_proof
#print axioms S2669_prime1249_of_arithmetic
#print axioms S2669_prime1249_of_conductor
#print axioms S2669_factorization
#print axioms S2669_root_injective
#print axioms S2669_p12map_separable
#print axioms S2669_p12map_bezout
#print axioms S2669_no_prime_over1249_le_conductor
#print axioms S2669_conductor_sup
#print axioms S2669_conductor1249
#print axioms S2669_prime1249
#print axioms S2669_exists_primeDegreeOne
#print axioms S2669_conductor_iff

end LeanFormal.IUT.XiFPaper.S2669Kummer1249Actual
