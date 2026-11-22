/-
# S2502: the actual chart identification `Away K[X₀,X₁]_{X₁} ≃+* K[X]`

This file constructs the ring isomorphism

    HomogeneousLocalization.Away S2504Grading (MvPolynomial.X 1) ≃+* MvPolynomial (Fin 1) UB

where `S2504Grading = MvPolynomial.homogeneousSubmodule (Fin 2) UB` is the
degree grading of the polynomial ring in the two projective coordinates `X 0`, `X 1` over the
Gaussian field `UB`.  This is the degree-zero part of the homogeneous localization
at the coordinate `X 1`, i.e. the affine chart `X 1 ≠ 0` of `Proj S2504Grading`, which is
the affine line over `UB` with coordinate `t = X 0 / X 1`.

## Construction

* `t = X 0 / X 1` is the chart coordinate.
* `phi : Away S2504Grading (X 1) →+* K[X]` is the dehomogenization `X 0 ↦ X`,
  `X 1 ↦ 1`, extended to the localization at `X 1` by `Localization.awayLift`.
* `psi : K[X] →+* Away S2504Grading (X 1)` is the inverse chart parametrization
  `X ↦ t`.
* The *homogeneity identity* `fraction_eq_mk` gives surjectivity of `psi`, and together with
  `phi ∘ psi = id` (checked on the generator `X` and on constants) the two maps are
  mutually inverse.

No `sorry`, no new axiom: the only axioms are those of Mathlib's localization API.
-/
import tmp.sheaf.xif.paper.S2504UnifiedBaseActual
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

open HomogeneousLocalization
open AlgebraicGeometry CategoryTheory

namespace LeanFormal.IUT.XiFPaper.S2505AwayEquivActual

open LeanFormal.IUT.XiFPaper.S2490RestrictionSectionActual
open LeanFormal.IUT.XiFPaper.S2504UnifiedBaseActual
local instance : Field UB := inferInstance
local instance : CommRing UB := inferInstance

abbrev S2504Grading : ℕ → Submodule UB (MvPolynomial (Fin 2) UB) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) UB
attribute [local instance] MvPolynomial.gradedAlgebra
open LeanFormal.IUT.XiFPaper.S2504UnifiedBaseActual

open LeanFormal.IUT.XiFPaper.S2490RestrictionSectionActual
open LeanFormal.IUT.XiFPaper.S2504UnifiedBaseActual

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## 1. The two homogeneous coordinates and the chart coordinate -/

/-- The projective coordinate `X 1` is homogeneous of degree one. -/
theorem X1_mem :
    (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB) ∈ S2504Grading 1 := by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  exact MvPolynomial.isHomogeneous_X UB 1

/-- The affine coordinate `X 0` is homogeneous of degree one. -/
theorem X0_mem :
    (MvPolynomial.X 0 : MvPolynomial (Fin 2) UB) ∈ S2504Grading 1 := by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  exact MvPolynomial.isHomogeneous_X UB 0

/-- `X 1 ^ n` as an element of the power submonoid at `X 1`. -/
def zp (n : ℕ) :
    Submonoid.powers (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB) :=
  ⟨(MvPolynomial.X 1) ^ n, n, rfl⟩

theorem zp_coe (n : ℕ) :
    ((zp n : Submonoid.powers (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB)) :
      MvPolynomial (Fin 2) UB) = (MvPolynomial.X 1) ^ n := rfl

theorem zp_zero :
    (1 : Submonoid.powers (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB)) = zp 0 := rfl

theorem zp_mul (a b : ℕ) :
    zp (a + b) = zp a * zp b := by
  apply Subtype.ext
  simp only [Submonoid.coe_mul, zp_coe, pow_add]

theorem zp_pow (k : ℕ) :
    (zp 1) ^ k = zp k := by
  induction k with
  | zero => rw [pow_zero, zp_zero]
  | succ k ih => rw [pow_succ, ih, zp_mul]

theorem one_mul_zp (n : ℕ) :
    (1 : Submonoid.powers (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB)) * zp n = zp n := by
  rw [zp_zero, ← zp_mul, Nat.zero_add]

/-- The chart coordinate `t = X 0 / X 1` of the affine chart `X 1 ≠ 0`. -/
def t : Away S2504Grading (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB) :=
  HomogeneousLocalization.Away.mk S2504Grading X1_mem 1 (MvPolynomial.X 0) X0_mem

/-! ## 2. The base field acts on the chart ring through the degree-zero part -/

/-- The Gaussian field acts on the chart ring through the degree-zero part. -/
instance S2502AwayAlgebra :
    Algebra UB (Away S2504Grading (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB)) :=
  ((HomogeneousLocalization.fromZeroRingHom S2504Grading
      (Submonoid.powers (MvPolynomial.X 1))).comp
    (algebraMap UB (S2504Grading 0))).toAlgebra

theorem S2502Away_algebraMap :
    algebraMap UB (Away S2504Grading (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB)) =
      (HomogeneousLocalization.fromZeroRingHom S2504Grading
        (Submonoid.powers (MvPolynomial.X 1))).comp
        (algebraMap UB (S2504Grading 0)) := by
  rw [S2502AwayAlgebra, RingHom.algebraMap_toAlgebra]

/-- The localization map on the degree-zero part, explicitly. -/
theorem algebraMap_away_eq (c : UB) :
    algebraMap (Away S2504Grading (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB))
      (Localization.Away (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB))
      (algebraMap UB (Away S2504Grading (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB)) c)
      = Localization.mk (algebraMap UB (MvPolynomial (Fin 2) UB) c) 1 := by
  rw [S2502Away_algebraMap]
  rfl

/-- The chart coordinate inside the localization at `X 1`. -/
theorem t_val :
    algebraMap (Away S2504Grading (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB))
      (Localization.Away (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB)) t
      = Localization.mk (MvPolynomial.X 0) (zp 1) := by
  rw [t, HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk]
  rfl

/-- Powers of the chart coordinate inside the localization at `X 1`. -/
theorem algebraMap_t_pow (k : ℕ) :
    algebraMap (Away S2504Grading (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB))
      (Localization.Away (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB)) (t ^ k)
      = Localization.mk ((MvPolynomial.X 0) ^ k) (zp k) := by
  rw [map_pow, t_val, Localization.mk_pow, zp_pow]

/-! ## 3. The forward chart map: dehomogenization at `X 1 = 1` -/

/-- Dehomogenization at `X 1 = 1`: the substitution `X 0 ↦ X`, `X 1 ↦ 1`. -/
def dehom : MvPolynomial (Fin 2) UB →ₐ[UB] MvPolynomial (Fin 1) UB :=
  MvPolynomial.aeval (R := UB) ![MvPolynomial.X 0, (1 : MvPolynomial (Fin 1) UB)]

theorem dehom_X (i : Fin 2) :
    dehom (MvPolynomial.X i)
      = ![MvPolynomial.X 0, (1 : MvPolynomial (Fin 1) UB)] i :=
  MvPolynomial.aeval_X (R := UB) ![MvPolynomial.X 0, (1 : MvPolynomial (Fin 1) UB)] i

theorem dehom_X0 : dehom (MvPolynomial.X 0) = MvPolynomial.X 0 := by
  rw [dehom_X]
  rfl

theorem dehom_X1 : dehom (MvPolynomial.X 1) = 1 := by
  rw [dehom_X]
  rfl

/-- The dehomogenization sends `X 1` to the unit `1`. -/
theorem dehomUnit : IsUnit (dehom.toRingHom (MvPolynomial.X 1)) := by
  change IsUnit (dehom (MvPolynomial.X 1))
  rw [dehom_X1]
  exact isUnit_one

/-- The dehomogenization sends base-field constants to base-field constants. -/
theorem dehom_algebraMap (c : UB) :
    dehom (algebraMap UB (MvPolynomial (Fin 2) UB) c)
      = algebraMap UB (MvPolynomial (Fin 1) UB) c := by
  rw [MvPolynomial.algebraMap_eq]
  exact MvPolynomial.aeval_C (R := UB)
    ![MvPolynomial.X 0, (1 : MvPolynomial (Fin 1) UB)] c

/-- **The forward chart map**: the dehomogenization at `X 1 = 1` extended to the
localization at `X 1` (where `X 1` becomes the unit `1`). -/
def phi :
    Away S2504Grading (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB) →+*
      MvPolynomial (Fin 1) UB :=
  (Localization.awayLift dehom.toRingHom (MvPolynomial.X 1) dehomUnit).comp
    (algebraMap (Away S2504Grading (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB))
      (Localization.Away (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB)))

theorem phi_apply (y : Away S2504Grading (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB)) :
    phi y = Localization.awayLift dehom.toRingHom (MvPolynomial.X 1) dehomUnit
      (algebraMap (Away S2504Grading (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB))
        (Localization.Away (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB)) y) := rfl

/-- The value of the chart map on a homogeneous fraction `a / X 1 ^ n`. -/
theorem phi_mk {n : ℕ} {a : MvPolynomial (Fin 2) UB}
    (ha : a ∈ S2504Grading (n • (1 : ℕ))) :
    phi (HomogeneousLocalization.Away.mk S2504Grading X1_mem n a ha) = dehom a := by
  rw [phi_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  have hv : dehom.toRingHom (MvPolynomial.X 1) * (1 : MvPolynomial (Fin 1) UB) = 1 := by
    change dehom (MvPolynomial.X 1) * 1 = 1
    rw [dehom_X1, one_mul]
  rw [Localization.awayLift_mk dehom.toRingHom (MvPolynomial.X 1) a 1 hv n, one_pow, mul_one]
  rfl

/-- The chart map sends `t = X 0 / X 1` to the affine coordinate `X`. -/
theorem phi_t : phi t = MvPolynomial.X 0 := by
  rw [t, phi_mk (n := 1) (a := MvPolynomial.X 0) X0_mem, dehom_X0]

/-! ## 4. The inverse chart map `K[X] →+* Away` -/

/-- **The inverse chart map** `K[X] →+* Away`: the affine coordinate `X ↦ t`. -/
def psi :
    MvPolynomial (Fin 1) UB →ₐ[UB]
      Away S2504Grading (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB) :=
  MvPolynomial.aeval (R := UB) (fun _ : Fin 1 => t)

theorem psi_X (i : Fin 1) : psi (MvPolynomial.X i) = t :=
  MvPolynomial.aeval_X (R := UB) (fun _ : Fin 1 => t) i

theorem psi_C (c : UB) :
    psi (MvPolynomial.C c)
      = algebraMap UB
        (Away S2504Grading (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB)) c :=
  MvPolynomial.aeval_C (R := UB) (fun _ : Fin 1 => t) c

/-- The chart fraction map sends constants to base-field constants. -/
theorem psi_algebraMap (c : UB) :
    psi (algebraMap UB (MvPolynomial (Fin 1) UB) c)
      = algebraMap UB
        (Away S2504Grading (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB)) c := by
  rw [MvPolynomial.algebraMap_eq]
  exact MvPolynomial.aeval_C (R := UB) (fun _ : Fin 1 => t) c

/-! ## 5. The homogeneity identity -/

/-- Addition of fractions with a common denominator. -/
theorem mk_add_zp (a b : MvPolynomial (Fin 2) UB) (n : ℕ) :
    Localization.mk (a + b) (zp n)
      = Localization.mk a (zp n) + Localization.mk b (zp n) := by
  rw [Localization.add_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨⟨1, Submonoid.one_mem _⟩, ?_⟩
  simp only [Submonoid.coe_mul, zp_coe, one_mul]
  ring

/-- `monomial d 1` is the corresponding monomial in two variables. -/
theorem monomial_eq (d : Fin 2 →₀ ℕ) :
    (MvPolynomial.monomial d 1 : MvPolynomial (Fin 2) UB)
      = (MvPolynomial.X 0) ^ d 0 * (MvPolynomial.X 1) ^ d 1 := by
  rw [← MvPolynomial.prod_X_pow_eq_monomial]
  rw [Finset.prod_subset (Finset.subset_univ _)
    (fun i _ hi => by rw [Finsupp.notMem_support_iff.mp hi, pow_zero]), Fin.prod_univ_two]

/-- The monomial identity `X 0 ^ a * X 1 ^ b / X 1 ^ (a + b) = X 0 ^ a / X 1 ^ a`. -/
theorem mk_monomial_eq (a b : ℕ) :
    Localization.mk ((MvPolynomial.X 0 : MvPolynomial (Fin 2) UB) ^ a
        * (MvPolynomial.X 1) ^ b) (zp (a + b))
      = Localization.mk ((MvPolynomial.X 0 : MvPolynomial (Fin 2) UB) ^ a) (zp a) := by
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨⟨1, Submonoid.one_mem _⟩, ?_⟩
  simp only [Submonoid.coe_mul, SubmonoidClass.coe_pow, zp_coe, one_mul]
  ring

/-- Monomials of total degree `n` span the homogeneous polynomials of degree `n`. -/
theorem homogeneousSubmodule_eq_span_monomial (n : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 2) UB n
      = Submodule.span UB (Set.range (fun d : {d : Fin 2 →₀ ℕ // Finsupp.degree d = n} =>
          MvPolynomial.monomial (d : Fin 2 →₀ ℕ) 1)) := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (Fin 2) UB n,
    AddMonoidAlgebra.supported_eq_span_single]
  congr 1
  ext x
  simp only [MvPolynomial.single_eq_monomial, Set.mem_image, Set.mem_range, Set.mem_setOf_eq,
    Subtype.exists, exists_prop]

/-- The total degree of an exponent vector in two variables. -/
theorem degree_eq_sum_two (d : Fin 2 →₀ ℕ) : d.degree = d 0 + d 1 := by
  rw [Finsupp.degree_apply,
    Finset.sum_subset (Finset.subset_univ _)
      (fun i _ hi => by rw [Finsupp.notMem_support_iff.mp hi]),
    Fin.sum_univ_two]

/-- **The homogeneity identity.**  For a homogeneous polynomial `p` of degree `n`, the
class of `p / X 1 ^ n` in the localization at `X 1` is the dehomogenization
`p(t, 1)` of `p`. -/
theorem fraction_eq_mk (n : ℕ) (p : MvPolynomial (Fin 2) UB) (hp : p ∈ S2504Grading n) :
    algebraMap (Away S2504Grading (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB))
      (Localization.Away (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB))
      (psi (dehom p))
      = Localization.mk p (zp n) := by
  have hspan : Submodule.span UB
      (Set.range (fun d : {d : Fin 2 →₀ ℕ // Finsupp.degree d = n} =>
        MvPolynomial.monomial (d : Fin 2 →₀ ℕ) 1))
      = MvPolynomial.homogeneousSubmodule (Fin 2) UB n :=
    (homogeneousSubmodule_eq_span_monomial n).symm
  have hmem : p ∈ Submodule.span UB
      (Set.range (fun d : {d : Fin 2 →₀ ℕ // Finsupp.degree d = n} =>
        MvPolynomial.monomial (d : Fin 2 →₀ ℕ) 1)) := by
    rw [hspan]
    exact hp
  clear hp hspan
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, hxd⟩ := hx
    obtain ⟨dd, hdd⟩ := d
    simp only at hxd
    subst hxd
    have hn : dd 0 + dd 1 = n := by
      rw [← degree_eq_sum_two]
      exact hdd
    have hdm : dehom (MvPolynomial.monomial dd 1)
        = (MvPolynomial.X 0 : MvPolynomial (Fin 1) UB) ^ dd 0 := by
      rw [monomial_eq, map_mul, map_pow, map_pow, dehom_X0, dehom_X1, one_pow, mul_one]
    have hL : algebraMap (Away S2504Grading (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB))
        (Localization.Away (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB))
        (psi (dehom (MvPolynomial.monomial dd 1)))
        = Localization.mk ((MvPolynomial.X 0) ^ dd 0) (zp (dd 0)) := by
      rw [hdm, map_pow, psi_X]
      exact algebraMap_t_pow (dd 0)
    have hR : Localization.mk (MvPolynomial.monomial dd 1) (zp n)
        = Localization.mk ((MvPolynomial.X 0) ^ dd 0) (zp (dd 0)) := by
      have key := mk_monomial_eq (dd 0) (dd 1)
      rw [hn] at key
      rw [monomial_eq]
      exact key
    exact hL.trans hR.symm
  | zero =>
    simp only [map_zero, Localization.mk_zero]
  | add x y hx hy ihx ihy =>
    simp only [map_add, ihx, ihy, mk_add_zp]
  | smul c x hx ih =>
    have hcx : c • x = algebraMap UB (MvPolynomial (Fin 2) UB) c * x :=
      Algebra.smul_def c x
    have h1 : algebraMap UB
        (Localization.Away (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB)) c
        = Localization.mk (algebraMap UB (MvPolynomial (Fin 2) UB) c) 1 := by
      rw [Localization.mk_eq_mk', IsLocalization.mk'_one,
        IsScalarTower.algebraMap_apply UB (MvPolynomial (Fin 2) UB)
          (Localization.Away (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB))]
    rw [hcx]
    simp only [map_mul, dehom_algebraMap, psi_algebraMap, algebraMap_away_eq, ih, h1,
      Localization.mk_mul, one_mul_zp]

/-! ## 6. The two chart maps are mutually inverse -/

/-- **Surjectivity of the chart fraction map**: every class `a / X 1 ^ n` with `a`
homogeneous of degree `n` is the dehomogenization `a(t, 1)` of `a`. -/
theorem psi_surjective : Function.Surjective psi := by
  intro y
  obtain ⟨n, a, ha, hx⟩ :=
    HomogeneousLocalization.Away.mk_surjective S2504Grading X1_mem y
  have ha' : a ∈ S2504Grading n := by simpa using ha
  refine ⟨dehom a, ?_⟩
  rw [← hx]
  apply HomogeneousLocalization.val_injective
  show algebraMap (Away S2504Grading (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB))
      (Localization.Away (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB)) (psi (dehom a))
    = algebraMap (Away S2504Grading (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB))
      (Localization.Away (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB))
      (HomogeneousLocalization.Away.mk S2504Grading X1_mem n a ha)
  rw [fraction_eq_mk n a ha',
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk]
  rfl

/-- The chart map sends the base-field constants to the constants. -/
theorem phi_algebraMap (c : UB) :
    phi (algebraMap UB
        (Away S2504Grading (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB)) c)
      = algebraMap UB (MvPolynomial (Fin 1) UB) c := by
  rw [phi_apply, algebraMap_away_eq]
  have hv : dehom.toRingHom (MvPolynomial.X 1) * (1 : MvPolynomial (Fin 1) UB) = 1 := by
    change dehom (MvPolynomial.X 1) * 1 = 1
    rw [dehom_X1, one_mul]
  have hzp0 : (1 : Submonoid.powers (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB))
      = ⟨(MvPolynomial.X 1) ^ 0, ⟨0, rfl⟩⟩ := rfl
  rw [hzp0]
  rw [Localization.awayLift_mk dehom.toRingHom (MvPolynomial.X 1)
    (algebraMap UB (MvPolynomial (Fin 2) UB) c) 1 hv 0, pow_zero, mul_one]
  rw [MvPolynomial.algebraMap_eq]
  exact MvPolynomial.aeval_C (R := UB)
    ![MvPolynomial.X 0, (1 : MvPolynomial (Fin 1) UB)] c

/-- The chart maps agree on the generator `X` of `K[X]`. -/
theorem phi_vec (i : Fin 1) : phi (psi (MvPolynomial.X i)) = MvPolynomial.X i := by
  rw [psi_X]
  fin_cases i
  exact phi_t

/-- **The dehomogenization inverts the chart fraction map.** -/
theorem phi_psi (p : MvPolynomial (Fin 1) UB) : phi (psi p) = p := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [psi_C, phi_algebraMap, MvPolynomial.algebraMap_eq]
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, hp, phi_vec i]

theorem phi_comp_psi :
    phi.comp psi.toRingHom = RingHom.id (MvPolynomial (Fin 1) UB) :=
  RingHom.ext phi_psi

/-! ## 7. The chart identification -/

/-- **The actual chart identification**: the degree-zero part of the homogeneous
localization of `K[X 0, X 1]` at `X 1` is the affine coordinate ring `K[X]`. -/
noncomputable def S2504AwayEquiv :
    Away S2504Grading (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB) ≃+*
      MvPolynomial (Fin 1) UB where
  toFun := phi
  invFun := psi
  left_inv := fun y => by
    obtain ⟨r, rfl⟩ := psi_surjective y
    rw [phi_psi r]
  right_inv := phi_psi
  map_mul' := phi.map_mul
  map_add' := phi.map_add

/-- **The chart identification in the frozen form of the task.** -/
noncomputable def S2504AwayRingEquiv :
    HomogeneousLocalization.Away S2504Grading (MvPolynomial.X 1) ≃+*
      MvPolynomial (Fin 1) UB :=
  S2504AwayEquiv

theorem S2504AwayEquiv_apply (y : Away S2504Grading
    (MvPolynomial.X 1 : MvPolynomial (Fin 2) UB)) :
    S2504AwayEquiv y = phi y := rfl

/-- The chart identification sends `t = X 0 / X 1` to `X`. -/
theorem S2504AwayEquiv_t : S2504AwayEquiv t = MvPolynomial.X 0 := phi_t

/-- The chart identification sends `X` to `t = X 0 / X 1`. -/
theorem S2504AwayEquiv_symm_X :
    S2504AwayEquiv.symm (MvPolynomial.X 0) = t := by
  rw [RingEquiv.symm_apply_eq]
  exact (phi_t).symm

/-! ## 8. Axiom audit -/

#print axioms fraction_eq_mk
#print axioms psi_surjective
#print axioms phi_algebraMap
#print axioms phi_psi
#print axioms phi_comp_psi
#print axioms S2504AwayEquiv
#print axioms S2504AwayRingEquiv
#print axioms S2504AwayEquiv_t
#print axioms S2504AwayEquiv_symm_X

/-! ## 9. The frozen type of the identification -/

/-- Type lock: `S2504AwayRingEquiv` has exactly the frozen target type of the task. -/
example : HomogeneousLocalization.Away S2504Grading (MvPolynomial.X 1) ≃+*
    MvPolynomial (Fin 1) UB :=
  S2504AwayRingEquiv


abbrev S2504P1 : Scheme := AlgebraicGeometry.Proj S2504Grading
abbrev S2504Open : Scheme :=
  Spec (CommRingCat.of (HomogeneousLocalization.Away S2504Grading (MvPolynomial.X 1)))
abbrev S2504OpenMap : S2504Open ⟶ S2504P1 :=
  AlgebraicGeometry.Proj.awayι S2504Grading (MvPolynomial.X 1)
    (by rw [MvPolynomial.mem_homogeneousSubmodule]; exact MvPolynomial.isHomogeneous_X UB 1)
    (by norm_num)
abbrev S2504Dom : Scheme :=
  Spec (CommRingCat.of (MvPolynomial (Fin 1) UB))

abbrev S2504DomHom : S2504Dom ⟶ Spec (CommRingCat.of UB) :=
  Spec.map (CommRingCat.ofHom (algebraMap UB (MvPolynomial (Fin 1) UB)))

abbrev S2504SpecMap : S2504Dom ⟶ S2504Open :=
  Spec.map (CommRingCat.ofHom S2504AwayRingEquiv.toRingHom)
abbrev S2504ToP1 : S2504Dom ⟶ S2504P1 :=
  S2504SpecMap ≫ S2504OpenMap
abbrev S2504P1Over : Iut.SchemeOverField UB :=
  Over.mk (AlgebraicGeometry.Proj.toSpecZero S2504Grading ≫
    Spec.map (CommRingCat.ofHom
      ((GradedRing.projZeroRingHom' S2504Grading).comp
        (MvPolynomial.C : UB →+* MvPolynomial (Fin 2) UB))))

abbrev S2504FOver' : Iut.SchemeOverField UB :=
  Over.mk S2504DomHom

end LeanFormal.IUT.XiFPaper.S2505AwayEquivActual
end
