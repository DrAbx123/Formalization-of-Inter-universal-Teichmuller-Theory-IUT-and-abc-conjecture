/- G1a radical support final3: radical divisibility plus the tame-different
arithmetic bridge for route section 8.5 (F7).

The tame Dedekind equality (repo donor count_differentIdeal_eq_of_tame) gives
d = e - 1 at a tamely ramified place; lead's Mzk1F7TameOrderActual turns that into
the paper-normalized bound d/e <= 1.  The bridge below removes the mismatch
between the local-field ramification exponent (logShellRamificationExponent) and
the Dedekind ramification index (ramificationIdx'), so the tame equality can be
fed to the arithmetic end. -/
import tmp.sheaf.xif.paper.Mzk1G1ABCCompactnessActual
import tmp.sheaf.xif.paper.Mzk1G1EllipticHeightCriterionActual
import tmp.sheaf.xif.paper.Mzk1F7TameOrderActual
import LeanFormal.IUT.IUTIV.Estimates.DifferentTameEquality
import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentUpperBound
import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentNormOrder
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Tactic
noncomputable section
open scoped NumberField
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatRadicalSupportFinal3Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.IntegralTraceDualTensorInclusion
open LeanFormal.IUT.LocalDifferentUpperBound
open LeanFormal.IUT.LocalDifferentNormOrder
open LeanFormal.IUT.XiFPaper.Mzk1F7TameOrderActual
open IsLocalRing

theorem radical_dvd_self_final3 (n : Nat) : radical n ∣ n := by
  simpa [radical] using Nat.prod_primeFactors_dvd n
theorem radical_pos_final3 (n : Nat) : 0 < radical n := by
  unfold radical
  refine Finset.prod_pos ?_
  intro p hp
  exact Nat.pos_of_mem_primeFactors (by simpa using hp)
theorem freyConductor_dvd_abc_final3 (a b c : Nat) : freyConductor a b c ∣ a * b * c := by
  rw [freyConductor_eq_radical]; exact radical_dvd_self_final3 (a * b * c)
theorem freyConductor_pos_final3 (a b c : Nat) : 0 < freyConductor a b c := by
  rw [freyConductor_eq_radical]; exact radical_pos_final3 (a * b * c)

/-! ## Tame different bridge at an actual p-adic local field -/

variable {p : Nat} [Fact p.Prime]
variable {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L]
  [IsUltrametricDist L] [ProperSpace L] [NormedAlgebra ℚ_[p] L]
  [FiniteDimensional ℚ_[p] L]

/-- **Tame local bridge, Dedekind form.**  If the multiplicity of the maximal
ideal in the actual local different ideal is the Dedekind ramification index minus
one (this is exactly the conclusion of the donor count_differentIdeal_eq_of_tame),
then the paper-normalized different order is at most one.  The rewrite uses the
donor logShellRamificationExponent_eq_ramificationIdx. -/
theorem tame_localDifferentPaperOrder_le_one
    [IsDiscreteValuationRing (Integers L)] [IsDedekindDomain (Integers L)]
    (h : (UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ_[p] (Integers L))).count
        (maximalIdeal (Integers L)) =
      (maximalIdeal ℤ_[p]).ramificationIdx' (maximalIdeal (Integers L)) - 1) :
    localDifferentPaperOrder (p := p) (L := L) ≤ 1 := by
  classical
  apply localDifferentPaperOrder_le_one_of_factorCount_eq (p := p) (L := L)
  rw [h, ← logShellRamificationExponent_eq_ramificationIdx (K := L) (p := p)]

#print axioms radical_dvd_self_final3

/-! ## The tame different donor at the actual local field -/

section TameDonor

variable [IsDiscreteValuationRing (Integers L)] [IsDedekindDomain (Integers L)]
variable [Algebra (FractionRing ℤ_[p]) (FractionRing (Integers L))]

/-- **Tame different count equality at the actual local field.**  Specialization of
the accepted IUT IV Prop 1.3(i) tame equality (donor
LeanFormal.IUT.IUTIV.Estimates.count_differentIdeal_eq_of_tame) to A = ℤ_[p] and
B = Integers L.  The fraction-ring algebra structure is supplied concretely by
FractionRing.liftAlgebra (see the note below); it is required only to state the
separability of the fraction fields. -/
theorem tame_count_differentIdeal_eq
    (hsepFrac : Algebra.IsSeparable (FractionRing ℤ_[p]) (FractionRing (Integers L)))
    (hsep : Algebra.IsSeparable (ℤ_[p] ⧸ maximalIdeal ℤ_[p])
      (Integers L ⧸ maximalIdeal (Integers L)))
    (he : ((maximalIdeal ℤ_[p]).ramificationIdx' (maximalIdeal (Integers L)) :
        ℤ_[p] ⧸ maximalIdeal ℤ_[p]) ≠ 0) :
    (UniqueFactorizationMonoid.normalizedFactors
        (differentIdeal ℤ_[p] (Integers L))).count
        (maximalIdeal (Integers L)) =
      (maximalIdeal ℤ_[p]).ramificationIdx' (maximalIdeal (Integers L)) - 1 := by
  classical
  haveI hFin : Module.Finite ℤ_[p] (Integers L) :=
    integersModuleFinite (p := p) (L := L)
  haveI hTF : Module.IsTorsionFree ℤ_[p] (Integers L) :=
    integersIsTorsionFree (p := p) (L := L)
  haveI hOver : (maximalIdeal (Integers L)).LiesOver (maximalIdeal ℤ_[p]) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap ℤ_[p] (Integers L))).symm⟩
  haveI hsepFracI : Algebra.IsSeparable (FractionRing ℤ_[p]) (FractionRing (Integers L)) :=
    hsepFrac
  haveI hsepI : Algebra.IsSeparable (ℤ_[p] ⧸ maximalIdeal ℤ_[p])
      (Integers L ⧸ maximalIdeal (Integers L)) := hsep
  exact LeanFormal.IUT.IUTIV.Estimates.count_differentIdeal_eq_of_tame
    (A := ℤ_[p]) (B := Integers L)
    (p := maximalIdeal ℤ_[p])
    (LeanFormal.IUT.IUTIV.Estimates.dvr_maximalIdeal_ne_bot ℤ_[p])
    (maximalIdeal (Integers L))
    (Ring.ne_bot_of_isMaximal_of_not_isField (maximalIdeal.isMaximal (Integers L))
      (IsDiscreteValuationRing.not_isField (Integers L))) he

/-- The tame step at the actual local field: the donor count equality combined with
the ramificationIdx' bridge gives the normalized different bound d <= 1. -/
theorem tame_localDifferentPaperOrder_le_one_of_tame
    (hsepFrac : Algebra.IsSeparable (FractionRing ℤ_[p]) (FractionRing (Integers L)))
    (hsep : Algebra.IsSeparable (ℤ_[p] ⧸ maximalIdeal ℤ_[p])
      (Integers L ⧸ maximalIdeal (Integers L)))
    (he : ((maximalIdeal ℤ_[p]).ramificationIdx' (maximalIdeal (Integers L)) :
        ℤ_[p] ⧸ maximalIdeal ℤ_[p]) ≠ 0) :
    localDifferentPaperOrder (p := p) (L := L) ≤ 1 :=
  tame_localDifferentPaperOrder_le_one
    (tame_count_differentIdeal_eq (p := p) (L := L) hsepFrac hsep he)

#print axioms tame_count_differentIdeal_eq
#print axioms tame_localDifferentPaperOrder_le_one_of_tame

end TameDonor
/-! ## Discharging the fraction-ring and residue separability inputs -/

section Glue

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable [IsDiscreteValuationRing (Integers L)] [IsDedekindDomain (Integers L)]

/-- Fraction-field separability at the actual local field.  The fraction field
of Integers L is L and that of Z_p is Q_p; the extension is finite, hence
integral in characteristic zero, hence separable. -/
theorem separable_fractionRing :
    Algebra.IsSeparable (FractionRing ℤ_[p]) (FractionRing (Integers L)) := by
  haveI : IsIntegrallyClosed ℤ_[p] := padicInt_isIntegrallyClosed (p := p)
  haveI : IsIntegralClosure (Integers L) ℤ_[p] (FractionRing (Integers L)) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  haveI : IsLocalization
      (Algebra.algebraMapSubmonoid (Integers L) (nonZeroDivisors ℤ_[p]))
      (FractionRing (Integers L)) :=
    IsIntegralClosure.isLocalization ℤ_[p] (FractionRing ℤ_[p])
      (FractionRing (Integers L)) (Integers L)
  haveI : FiniteDimensional (FractionRing ℤ_[p]) (FractionRing (Integers L)) :=
    .of_isLocalization ℤ_[p] (Integers L) (nonZeroDivisors ℤ_[p])
  exact Algebra.IsSeparable.of_integral _ _


/-- Tame bound at the actual local field, partially glued: the fraction-field
separability is discharged; the residue-field separability (finite fields are
perfect) and the arithmetic tameness hypothesis remain as explicit inputs. -/
theorem tame_localDifferentPaperOrder_le_one_glued
    (hsep : Algebra.IsSeparable (ℤ_[p] ⧸ maximalIdeal ℤ_[p])
      (Integers L ⧸ maximalIdeal (Integers L)))
    (he : ((maximalIdeal ℤ_[p]).ramificationIdx' (maximalIdeal (Integers L)) :
        ℤ_[p] ⧸ maximalIdeal ℤ_[p]) ≠ 0) :
    localDifferentPaperOrder (p := p) (L := L) ≤ 1 :=
  tame_localDifferentPaperOrder_le_one_of_tame (p := p) (L := L)
    (separable_fractionRing (p := p) (L := L)) hsep he

#print axioms separable_fractionRing
#print axioms tame_localDifferentPaperOrder_le_one_glued

end Glue
/-! ## The tameness arithmetic input (b): p not dividing e makes e invertible mod p -/

/-- A class in the residue ring Z / (p) is nonzero exactly when p does not divide
the representative. -/
theorem quotient_span_mk_ne_zero_iff {p : Nat} (e : Int) :
    (Ideal.Quotient.mk (Ideal.span {(p : Int)}) e) ≠ 0 ↔ ¬ ((p : Int) ∣ e) := by
  rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

/-- Tameness arithmetic input (b).  If e divides n and p does not divide n, then e
is invertible modulo p: its class in Z / (p) is nonzero. -/
theorem ramificationIdx_invertible_of_dvd {p e n : Nat} (he : e ∣ n) (hpn : ¬ p ∣ n) :
    (Ideal.Quotient.mk (Ideal.span {(p : Int)}) ((e : Int))) ≠ 0 := by
  rw [quotient_span_mk_ne_zero_iff]
  intro hpe
  have hpe' : p ∣ e := by exact_mod_cast hpe
  exact hpn (hpe'.trans he)

#print axioms quotient_span_mk_ne_zero_iff
#print axioms ramificationIdx_invertible_of_dvd
/-! ## Residue separability via the ZMod route (Lead ruling (i)) -/

section ZModResidue

variable {K : Type*} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span {(p : Int)})]

/-- The ZMod-p algebra structure on the residue field of O_K at P, transported from
the quotient-ring algebra along Int.quotientSpanNatEquivZMod. -/
noncomputable instance algebraZModQuotient : Algebra (ZMod p) (𝓞 K ⧸ P) := by
  classical
  have hle : Ideal.span {(p : Int)} ≤ P.comap (algebraMap Int (𝓞 K)) :=
    le_of_eq (Ideal.over_def (p := Ideal.span {(p : Int)}) (P := P))
  letI : Algebra (Int ⧸ Ideal.span {(p : Int)}) (𝓞 K ⧸ P) :=
    Ideal.Quotient.algebraQuotientOfLEComap hle
  exact ((algebraMap (Int ⧸ Ideal.span {(p : Int)}) (𝓞 K ⧸ P)).comp
    (Int.quotientSpanNatEquivZMod p).symm.toRingHom).toAlgebra

/-- The canonical quotient-ring algebra and the ZMod algebra agree under the
quotientSpanNatEquivZMod identification (definition of the ZMod algebra). -/
theorem algebraMap_zmod_comp_eq :
    RingHom.comp (algebraMap (ZMod p) (𝓞 K ⧸ P))
        (Int.quotientSpanNatEquivZMod p : (Int ⧸ Ideal.span {(p : Int)}) →+* ZMod p)
      = algebraMap (Int ⧸ Ideal.span {(p : Int)}) (𝓞 K ⧸ P) := by
  classical
  have hle : Ideal.span {(p : Int)} ≤ P.comap (algebraMap Int (𝓞 K)) :=
    le_of_eq (Ideal.over_def (p := Ideal.span {(p : Int)}) (P := P))
  letI : Algebra (Int ⧸ Ideal.span {(p : Int)}) (𝓞 K ⧸ P) :=
    Ideal.Quotient.algebraQuotientOfLEComap hle
  ext x
  show algebraMap (ZMod p) (𝓞 K ⧸ P) ((Int.quotientSpanNatEquivZMod p) x)
      = algebraMap (Int ⧸ Ideal.span {(p : Int)}) (𝓞 K ⧸ P) x
  rw [show algebraMap (ZMod p) (𝓞 K ⧸ P)
      = ((algebraMap (Int ⧸ Ideal.span {(p : Int)}) (𝓞 K ⧸ P)).comp
          (Int.quotientSpanNatEquivZMod p).symm.toRingHom) from rfl]
  show (algebraMap (Int ⧸ Ideal.span {(p : Int)}) (𝓞 K ⧸ P))
      ((Int.quotientSpanNatEquivZMod p).symm ((Int.quotientSpanNatEquivZMod p) x))
    = algebraMap (Int ⧸ Ideal.span {(p : Int)}) (𝓞 K ⧸ P) x
  rw [RingEquiv.symm_apply_apply]

/-- Tameness arithmetic input (3): e is invertible in ZMod p when e divides n and
p does not divide n. -/
theorem ramificationIdx_invertible_zmod {p e n : Nat} (he : e ∣ n) (hpn : ¬ p ∣ n) :
    ((e : ZMod p)) ≠ 0 := by
  rintro hzero
  have hz : ((e : Int) : ZMod p) = 0 := by
    rw [Int.cast_natCast]
    exact hzero
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
  have hpe' : p ∣ e := by exact_mod_cast hz
  exact hpn (hpe'.trans he)

#print axioms ramificationIdx_invertible_zmod

end ZModResidue
/-! ## Global residue separability via the Finite/PerfectField instance chain -/

section GlobalResidue

attribute [local instance] Ideal.Quotient.field

variable {K : Type*} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]

/-- **Tameness arithmetic input (a), global form.**  At a maximal ideal P of the
ring of integers of a number field lying over (p), the residue extension
Z/(p) -> O_K/P is separable: both residue fields are finite, so the base is
perfect and the finite extension is algebraic; the separability instance fires
from PerfectField + Algebraic without touching ring structures. -/
theorem residue_separable_global (P : Ideal (𝓞 K)) [P.IsMaximal]
    [P.LiesOver (Ideal.span {(p : Int)})] :
    Algebra.IsSeparable (Int ⧸ Ideal.span {(p : Int)}) (𝓞 K ⧸ P) := by
  classical
  haveI hpm : (Ideal.span {(p : Int)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  haveI : Fintype (Int ⧸ Ideal.span {(p : Int)}) :=
    Fintype.ofEquiv (ZMod p) (Int.quotientSpanNatEquivZMod p).toEquiv.symm
  have hp_ne_bot : Ideal.span {(p : Int)} ≠ ⊥ := by
    intro h
    have hpzero : ((p : Int)) = 0 := by
      have : (p : Int) ∈ (⊥ : Ideal Int) := by
        rw [← h]; exact Ideal.mem_span_singleton_self _
      simpa using this
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hpzero)
  have hP_ne_bot : P ≠ ⊥ := by
    intro h
    apply hp_ne_bot
    rw [Ideal.over_def (p := Ideal.span {(p : Int)}) (P := P)]
    simp [h]
  haveI : Finite (𝓞 K ⧸ P) :=
    (Ideal.absNorm_ne_zero_iff P).mp
      (fun h => hP_ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
  haveI : Module.Finite (Int ⧸ Ideal.span {(p : Int)}) (𝓞 K ⧸ P) := inferInstance
  haveI : Algebra.IsAlgebraic (Int ⧸ Ideal.span {(p : Int)}) (𝓞 K ⧸ P) := inferInstance
  haveI : PerfectField (Int ⧸ Ideal.span {(p : Int)}) := PerfectField.ofFinite
  exact inferInstance

#print axioms residue_separable_global

end GlobalResidue