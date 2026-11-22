import tmp.sheaf.xif.paper.S1681UnitRootKummerActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceAdicCompletionRingEquiv
import Mathlib.RingTheory.Henselian

/-!
# S1682: the principal-unit 2l-th power map and the residue-unit obstruction

This file closes the principal-unit half of the S1681 root gap and isolates
the remaining residue-unit input exactly.

Let K = Completion (sectionKPlace T b) be the source-designated completion,
O = Valued.v.valuationSubring its valuation ring, m the maximal ideal, and
let n = 2 * l.value.  Assume Nat.Coprime n (residueCharacteristic ...), i.e.
p = residueCharacteristic does not divide 2l.  Then:

* principalUnit_pow_eq proves, via Hensel's lemma applied to X^n - a over
  the m-adically complete DVR O (FinitePlaceAdicCompletionRingEquiv
  supplies IsAdicComplete, hence HenselianRing), that every
  a = 1 (mod m) has an n-th root in K.
* principalUnit_pow_surjective and
  s1682PrincipalUnitPowerSurjective spell this out as the exact statement
  S1681PrincipalUnitPowerSurjective from S1681.  No algebraic-closure root,
  no order-divisibility root, and no pro-p-group infinity argument are used:
  the only analytic input is Hensel/Newton for the complete DVR.
* unit_pow_surjective_of_residue_pow handles the residue-unit factor:
  if the residue of a unit u : O^x has an n-th root in the residue field,
  then u itself has an n-th root in K.
* S1682ResidueUnitTwoLRootRequired is the exact remaining input for the
  specific source unit s1668QUnitPart; from it and the coprime hypothesis we
  derive S1677UnitRootRequired.
* s1682ResidueUnitPower_not_surjective shows that the residue-unit
  surjectivity cannot be deduced from the coprime hypothesis alone: in odd
  residue characteristic 2 divides n, the power map on the finite residue unit
  group has the nontrivial kernel element -1, hence is not surjective.

Thus after this file the S1681 gap is exactly the residue-unit condition, a
genuine extra Kummer input; the principal-unit condition is proved.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open scoped WithZero Valued

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.InitialThetaSource.PlaceQParameterUniformization
open LeanFormal.IUT.XiFPaper.S1444ReportAKPlaceQActual
open LeanFormal.IUT.XiFPaper.S1647RouteARootActual
open LeanFormal.IUT.XiFPaper.S1660SectionKPlaceRootActual
open LeanFormal.IUT.XiFPaper.S1668UnitRootDescentActual
open LeanFormal.IUT.XiFPaper.S1677UnitKummerActual
open LeanFormal.IUT.XiFPaper.S1681UnitRootKummerActual

namespace LeanFormal.IUT.XiFPaper.S1682PrincipalUnitPowerActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The source-designated completion K_v. -/
abbrev K : Type := Completion (sectionKPlace T b)

/-- The residue field of the source-designated place. -/
abbrev F : Type := ResidueField (sectionKPlace T b)

/-- The valuation ring of the completion, bundled so that its maximal ideal and
principal-unit subgroup are available. -/
abbrev O : ValuationSubring (K T b) := (Valued.v (R := K T b)).valuationSubring

/-- The same valuation ring as the completed integer ring of the number-field
place; this is the form for which IsAdicComplete is already proved in
FinitePlaceAdicCompletionRingEquiv. -/
abbrev A : ValuationSubring (K T b) :=
  (sectionKPlace T b).maximalIdeal.adicCompletionIntegers T.arithmetic.K

/-! ## 1. The derivative unit -/

/-- If n is coprime to the residue characteristic, then n is a unit of the
completed valuation ring.  This is the only place where residue coprimality is
used for Hensel's lemma. -/
lemma n_isUnit (n : Nat)
    (hcop : Nat.Coprime n (residueCharacteristic (sectionKPlace T b))) :
    IsUnit ((n : Nat) : O T b) := by
  let v := (sectionKPlace T b).maximalIdeal
  letI : CharP (F T b) (residueCharacteristic (sectionKPlace T b)) := by
    dsimp [F, residueCharacteristic]
    infer_instance
  have hp : Nat.Prime (residueCharacteristic (sectionKPlace T b)) :=
    residueCharacteristic_prime _
  have hpn : Not (residueCharacteristic (sectionKPlace T b) ∣ n) := by
    intro hdvd
    have hdvdgcd : residueCharacteristic (sectionKPlace T b) ∣
        Nat.gcd n (residueCharacteristic (sectionKPlace T b)) :=
      Nat.dvd_gcd hdvd (dvd_refl _)
    rw [hcop] at hdvdgcd
    exact hp.not_dvd_one hdvdgcd
  have hnF : ((n : F T b) ≠ 0) := by
    intro h
    exact hpn ((CharP.cast_eq_zero_iff (F T b)
      (residueCharacteristic (sectionKPlace T b)) n).mp h)
  have hnR : (Ideal.Quotient.mk v.asIdeal
      ((n : Nat) : NumberField.RingOfIntegers T.arithmetic.K)) ≠ 0 := by
    intro h
    exact hnF h
  have hformula : (adicCompletionQuotientPowEquiv (K := T.arithmetic.K) v 1
      (Ideal.Quotient.mk (v.asIdeal ^ 1)
        ((n : Nat) : NumberField.RingOfIntegers T.arithmetic.K))) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (A T b) ^ 1) ((n : Nat) : A T b) := by
    rw [show ((n : Nat) : A T b) =
        algebraMap (NumberField.RingOfIntegers T.arithmetic.K) (A T b)
          ((n : Nat) : NumberField.RingOfIntegers T.arithmetic.K) by simp]
    rw [← adicCompletionQuotientPowHom_mk (K := T.arithmetic.K) v 1
      ((n : Nat) : NumberField.RingOfIntegers T.arithmetic.K)]
    rfl
  have hnAclassPow : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (A T b) ^ 1)
      ((n : Nat) : A T b)) ≠ 0 := by
    intro h
    have h2 := congrArg
      (adicCompletionQuotientPowEquiv (K := T.arithmetic.K) v 1).symm h
    rw [map_zero] at h2
    rw [← hformula, RingEquiv.symm_apply_apply] at h2
    rw [pow_one] at h2
    exact hnR h2
  have hnAclass : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (A T b))
      ((n : Nat) : A T b)) ≠ 0 := by
    rw [pow_one] at hnAclassPow
    exact hnAclassPow
  have hnA : IsUnit ((n : Nat) : A T b) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem
    exact hnAclass (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  exact hnA

/-! ## 2. Hensel: principal units have n-th roots -/

/-- Principal-unit power surjectivity, element form.  For a in O with
a - 1 in m and Nat.Coprime n p, the polynomial X^n - a has a root r in O
with r = 1 (mod m), hence r is a unit and its image in K is an n-th root of a. -/
lemma principalUnit_pow_eq
    (n : Nat) (hn : 0 < n)
    (hcop : Nat.Coprime n (residueCharacteristic (sectionKPlace T b)))
    (a : O T b) (ha : a - 1 ∈ IsLocalRing.maximalIdeal (O T b)) :
    ∃ v : (K T b)ˣ, (v : K T b) ^ n = algebraMap (O T b) (K T b) a := by
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (O T b)) (O T b) :=
    inferInstanceAs (IsAdicComplete (IsLocalRing.maximalIdeal (A T b)) (A T b))
  haveI : HenselianRing (O T b) (IsLocalRing.maximalIdeal (O T b)) :=
    inferInstanceAs (HenselianRing (A T b) (IsLocalRing.maximalIdeal (A T b)))
  let f : Polynomial (O T b) := Polynomial.X ^ n - Polynomial.C a
  have hmonic : f.Monic := Polynomial.monic_X_pow_sub_C a hn.ne'
  have hfeval : f.eval 1 ∈ IsLocalRing.maximalIdeal (O T b) := by
    have hfe : f.eval 1 = -(a - 1) := by
      rw [show f.eval 1 = 1 - a by simp [f]]
      abel
    rw [hfe]
    exact neg_mem ha
  have hnUnitO : IsUnit ((n : Nat) : O T b) :=
    n_isUnit (T := T) (b := b) n hcop
  have hderEval : f.derivative.eval 1 = (n : O T b) := by
    simp [f, Polynomial.derivative_X_pow]
  have hder : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (O T b))
      (f.derivative.eval 1)) := by
    rw [hderEval]
    exact hnUnitO.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (O T b)))
  obtain ⟨r, hrroot, hrsub⟩ :=
    HenselianRing.is_henselian f hmonic 1 hfeval hder
  have hrpow : r ^ n = a := by
    have h := hrroot
    change f.eval r = 0 at h
    rw [show f.eval r = r ^ n - a by simp [f]] at h
    exact sub_eq_zero.mp h
  have hrnot : r ∉ IsLocalRing.maximalIdeal (O T b) := by
    intro hr
    have h1 : (1 : O T b) ∈ IsLocalRing.maximalIdeal (O T b) := by
      have h := Ideal.sub_mem (IsLocalRing.maximalIdeal (O T b)) hr hrsub
      simpa only [sub_sub_cancel] using h
    exact (IsLocalRing.notMem_maximalIdeal.mpr isUnit_one) h1
  let rUnit : (O T b)ˣ := (IsLocalRing.notMem_maximalIdeal.mp hrnot).unit
  let v : (K T b)ˣ := Units.map (algebraMap (O T b) (K T b)) rUnit
  refine ⟨v, ?_⟩
  change (algebraMap (O T b) (K T b) (rUnit : O T b)) ^ n =
    algebraMap (O T b) (K T b) a
  rw [← map_pow]
  have hrUnit : (rUnit : O T b) = r := IsUnit.unit_spec _
  rw [hrUnit, hrpow]

/-- Principal-unit power surjectivity, unit form.  This is exactly the
principal-unit condition left open in S1681. -/
lemma principalUnit_pow_surjective
    (n : Nat) (hn : 0 < n)
    (hcop : Nat.Coprime n (residueCharacteristic (sectionKPlace T b)))
    (u : (K T b)ˣ)
    (hu : (Valued.v ((u : K T b) - 1) : WithZero (Multiplicative Int)) < 1) :
    ∃ v : (K T b)ˣ, v ^ n = u := by
  have hmem : (u : K T b) ∈ O T b := by
    have hu1 : (u : K T b) - 1 ∈ O T b := by
      rw [Valuation.mem_valuationSubring_iff]
      exact le_of_lt hu
    have h := add_mem hu1 (one_mem (O T b))
    simpa [sub_add_cancel] using h
  let a : O T b := ⟨(u : K T b), hmem⟩
  have ha : a - 1 ∈ IsLocalRing.maximalIdeal (O T b) := by
    rw [Valuation.mem_maximalIdeal_iff]
    have hcoe : ((a - 1 : O T b) : K T b) = (u : K T b) - 1 := rfl
    rw [hcoe]
    exact hu
  obtain ⟨v, hv⟩ := principalUnit_pow_eq (T := T) (b := b) n hn hcop a ha
  refine ⟨v, ?_⟩
  apply Units.ext
  change (v : K T b) ^ n = (u : K T b)
  rw [hv]
  rfl

/-- The exact S1681 principal-unit statement, under coprimality of
2 * l.value with the residue characteristic. -/
theorem s1682PrincipalUnitPowerSurjective
    (hcop : Nat.Coprime (2 * l.value)
      (residueCharacteristic (sectionKPlace T b))) :
    S1681PrincipalUnitPowerSurjective (l := l) T b := by
  intro u hu
  exact principalUnit_pow_surjective (T := T) (b := b) (2 * l.value)
    (Nat.mul_pos (by norm_num) l.prime.pos) hcop u hu

/-- The coprimality hypothesis used by Hensel: if l is prime to the
residue characteristic and the residue characteristic is odd, then 2 * l is
prime to the residue characteristic. -/
lemma coprime_twoL_of_coprime_of_ne_two
    (hl : Nat.Coprime l.value (residueCharacteristic (sectionKPlace T b)))
    (hp2 : residueCharacteristic (sectionKPlace T b) ≠ 2) :
    Nat.Coprime (2 * l.value) (residueCharacteristic (sectionKPlace T b)) :=
  Nat.Coprime.mul_left
    (by
      rw [Nat.coprime_two_left]
      exact (residueCharacteristic_prime _).odd_of_ne_two hp2)
    hl

/-- The exact S1681 principal-unit statement under the source-style hypothesis:
the residue characteristic is odd and coprime to l. -/
theorem s1682PrincipalUnitPowerSurjective_of_coprime_of_odd
    (hl : Nat.Coprime l.value (residueCharacteristic (sectionKPlace T b)))
    (hp2 : residueCharacteristic (sectionKPlace T b) ≠ 2) :
    S1681PrincipalUnitPowerSurjective (l := l) T b :=
  s1682PrincipalUnitPowerSurjective (T := T) (b := b)
    (coprime_twoL_of_coprime_of_ne_two (T := T) (b := b) hl hp2)

/-! ## 3. The source unit part as a unit of the completed valuation ring -/

/-- The inclusion of the subring Valued.v.integer into the bundled valuation
subring O (they have the same carrier). -/
noncomputable def integerToO :
    (Valued.v (R := K T b)).integer →+* O T b where
  toFun x := ⟨x.1, x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The source unit part s1668QUnitPart regarded as a unit of O. -/
noncomputable def s1682QUnitPartO : (O T b)ˣ :=
  Units.map (integerToO T b) (s1668QUnitPart T b)

/-- The transported unit part maps back to the field unit part of S1668. -/
@[simp] theorem s1682QUnitPartO_field :
    Units.map (algebraMap (O T b) (K T b)) (s1682QUnitPartO T b) =
      s1668QUnitPartField T b := by
  apply Units.ext
  rfl

/-! ## 4. Residue-unit factor and the exact remaining input -/

/-- Residue-unit reduction.  If the residue of u : O^x is an n-th power
in the residue field, and n is coprime to the residue characteristic, then
u itself is an n-th power in K. -/
lemma unit_pow_surjective_of_residue_pow
    (n : Nat) (hn : 0 < n)
    (hcop : Nat.Coprime n (residueCharacteristic (sectionKPlace T b)))
    (u : (O T b)ˣ)
    (hres : ∃ β : (IsLocalRing.ResidueField (O T b))ˣ,
      β ^ n = Units.map (IsLocalRing.residue (O T b)).toMonoidHom u) :
    ∃ v : (K T b)ˣ, v ^ n = Units.map (algebraMap (O T b) (K T b)) u := by
  obtain ⟨β, hβ⟩ := hres
  have hsurj : Function.Surjective
      (Units.map (IsLocalRing.residue (O T b)).toMonoidHom) :=
    IsLocalRing.surjective_units_map_of_local_ringHom
      (IsLocalRing.residue (O T b)) Ideal.Quotient.mk_surjective
      (inferInstanceAs (IsLocalHom (IsLocalRing.residue (O T b))))
  obtain ⟨bU, hbU⟩ := hsurj β
  let c : (O T b)ˣ := u * (bU ^ n)⁻¹
  have hc_res : IsLocalRing.residue (O T b) c = 1 := by
    have hmap : Units.map (IsLocalRing.residue (O T b)).toMonoidHom c = 1 := by
      dsimp [c]
      rw [map_mul, map_inv, map_pow]
      have hbUn : (Units.map (IsLocalRing.residue (O T b)).toMonoidHom bU) ^ n =
          β ^ n := by
        rw [hbU]
      calc
        Units.map (IsLocalRing.residue (O T b)).toMonoidHom u *
            ((Units.map (IsLocalRing.residue (O T b)).toMonoidHom bU) ^ n)⁻¹
            = Units.map (IsLocalRing.residue (O T b)).toMonoidHom u *
                (β ^ n)⁻¹ :=
              congrArg (fun w => Units.map (IsLocalRing.residue (O T b)).toMonoidHom u * w⁻¹)
                hbUn
        _ = 1 := by rw [← hβ]; simp
    exact congrArg (fun w : (IsLocalRing.ResidueField (O T b))ˣ =>
      (w : IsLocalRing.ResidueField (O T b))) hmap
  have hc_mem : (c : O T b) - 1 ∈ IsLocalRing.maximalIdeal (O T b) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change IsLocalRing.residue (O T b) ((c : O T b) - 1) = 0
    rw [map_sub, map_one, hc_res]
    simp
  have hbc : bU ^ n * c = u := by
    dsimp [c]
    rw [← mul_assoc, mul_comm (bU ^ n) u, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨d, hd⟩ := principalUnit_pow_eq (T := T) (b := b) n hn hcop c hc_mem
  refine ⟨Units.map (algebraMap (O T b) (K T b)) bU * d, ?_⟩
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_mul, mul_pow, hd]
  change (algebraMap (O T b) (K T b) (bU : O T b)) ^ n *
      (algebraMap (O T b) (K T b) (c : O T b)) =
    (algebraMap (O T b) (K T b) (u : O T b))
  rw [← map_pow, ← map_mul]
  congr 1
  simpa using congrArg (fun w : (O T b)ˣ => (w : O T b)) hbc

/-- The exact remaining residue-unit input for the source unit part: its
residue in the residue field of the completed valuation ring has a 2l-th
root.  This is a genuine Kummer condition; it is not derivable from
l != residueCharacteristic alone (see the obstruction below). -/
def S1682ResidueUnitTwoLRootRequired : Prop :=
  ∃ β : (IsLocalRing.ResidueField (O T b))ˣ,
    β ^ (2 * l.value) =
      Units.map (IsLocalRing.residue (O T b)).toMonoidHom (s1682QUnitPartO T b)

/-- Reduction of the S1677 unit-root requirement to the exact residue-unit
input. -/
theorem s1682QUnitPartField_twoLRoot_of_residueRoot
    (hcop : Nat.Coprime (2 * l.value)
      (residueCharacteristic (sectionKPlace T b)))
    (hres : S1682ResidueUnitTwoLRootRequired (l := l) T b) :
    ∃ v : (K T b)ˣ, v ^ (2 * l.value) = s1668QUnitPartField T b := by
  obtain ⟨v, hv⟩ := unit_pow_surjective_of_residue_pow (T := T) (b := b)
    (2 * l.value) (Nat.mul_pos (by norm_num) l.prime.pos) hcop
    (s1682QUnitPartO T b) hres
  refine ⟨v, ?_⟩
  rw [← s1682QUnitPartO_field]
  exact hv

/-- The exact S1677 unit-root lemma, conditional on the residue-unit root.
Together with s1682PrincipalUnitPowerSurjective, this shows that the only
remaining input is S1682ResidueUnitTwoLRootRequired. -/
theorem s1682S1677UnitRootRequired_of_residueRoot
    (hcop : Nat.Coprime (2 * l.value)
      (residueCharacteristic (sectionKPlace T b)))
    (hres : S1682ResidueUnitTwoLRootRequired (l := l) T b) :
    S1677UnitRootRequired (l := l) T b :=
  s1682QUnitPartField_twoLRoot_of_residueRoot (T := T) (b := b) hcop hres

/-! ## 5. The residue-unit obstruction in odd residue characteristic -/

/-- Universal n-th power surjectivity on the residue units of the source
place. -/
def ResidueUnitPowerSurjective (n : Nat) : Prop :=
  ∀ a : (F T b)ˣ, ∃ c : (F T b)ˣ, c ^ n = a

/-- The residue-unit power map is not surjective in odd residue
characteristic.  For n = 2 * l.value, -1 is a nontrivial element of the
kernel of the power map on the finite residue unit group (because n is even
and -1 != 1).  Hence the power map is not injective, and on a finite type it
cannot be surjective.  So the residue-unit root is a genuine additional input;
it is not a consequence of l != residueCharacteristic. -/
theorem s1682ResidueUnitPower_not_surjective
    (hp2 : residueCharacteristic (sectionKPlace T b) ≠ 2) :
    Not (ResidueUnitPowerSurjective (l := l) T b (2 * l.value)) := by
  intro hsurj
  let p := residueCharacteristic (sectionKPlace T b)
  letI : CharP (F T b) p := by
    dsimp [p, F, residueCharacteristic]
    infer_instance
  have hp : Nat.Prime p := residueCharacteristic_prime _
  have hpgt : 2 < p := by
    have h2 : 2 ≤ p := hp.two_le
    omega
  letI : Fact (2 < p) := ⟨hpgt⟩
  have hneg : (-1 : F T b) ≠ 1 := CharP.neg_one_ne_one (F T b) p
  have hnegUnit : (-1 : (F T b)ˣ) ≠ 1 := by
    intro h
    apply hneg
    exact congrArg (fun u : (F T b)ˣ => (u : F T b)) h
  haveI : Finite (F T b) := residueFieldFinite (sectionKPlace T b)
  haveI : Finite (F T b)ˣ := Finite.of_injective
    (fun u : (F T b)ˣ => (u : F T b)) Units.val_injective
  have hnEven : Even (2 * l.value) := ⟨l.value, by ring⟩
  have hpow : (-1 : (F T b)ˣ) ^ (2 * l.value) = 1 := by
    apply Units.ext
    change ((-1 : F T b) ^ (2 * l.value)) = 1
    exact Even.neg_one_pow hnEven
  have hnotinj : Not (Function.Injective (fun x : (F T b)ˣ => x ^ (2 * l.value))) := by
    intro hinj
    apply hnegUnit
    apply hinj
    change (-1 : (F T b)ˣ) ^ (2 * l.value) =
      (1 : (F T b)ˣ) ^ (2 * l.value)
    rw [hpow]
    simp
  have hsurj' : Function.Surjective (fun x : (F T b)ˣ => x ^ (2 * l.value)) := hsurj
  exact hnotinj (Finite.injective_iff_surjective.mpr hsurj')

end LeanFormal.IUT.XiFPaper.S1682PrincipalUnitPowerActual

end