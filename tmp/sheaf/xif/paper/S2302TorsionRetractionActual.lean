import tmp.sheaf.xif.paper.S2297QuotientSectionActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Algebra.Group.TypeTags.Basic

/-! # S2302: torsion retraction from divisibility of the torsion subgroup

The torsion subgroup of the integral-closure units is divisible: every root of
unity has an n-th root in the algebraically closed field, which is again a root
of unity and an integral unit.  Hence it is an injective ℤ-module and the
inclusion into the units splits, giving the S2297 torsion retraction. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2302TorsionRetractionActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S2147PaperIntegralClosureOUnitsActionActual
open LeanFormal.IUT.XiFPaper.S2219PaperOUnitsCarrierActual
open LeanFormal.IUT.XiFPaper.S2222PaperOUnitsMuAttachmentActual
open LeanFormal.IUT.XiFPaper.S2297QuotientSectionActual
open LeanFormal.IUT.XiFPaper.S2288UnitLiftActual
open LeanFormal.IUT.XiFPaper.S2249LogKummerTransportActual
open LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

local notation "U" => S2219PaperOUnits T b
local notation "mu" => CommGroup.torsion U

theorem s2302_exists_root
    (n : Nat) (hn : 0 < n) (t : mu) :
    ∃ s : mu, ((s : U) ^ n = (t : U)) := by
  letI : IsAlgClosed (S2147PaperIntegralClosure T b) := by
    change IsAlgClosed (AlgebraicClosure (NormalizedCompletion (sectionKPlace T b)))
    infer_instance
  let x : S2147PaperIntegralClosure T b := ((t : U) : Integers (S2147PaperIntegralClosure T b))
  have hxne : x ≠ 0 := by
    intro hx0
    exact Units.ne_zero (t : U) (Subtype.ext hx0)
  let f : Polynomial (S2147PaperIntegralClosure T b) := Polynomial.X ^ n - Polynomial.C x
  have hfdeg : f.degree ≠ 0 := by
    dsimp [f]
    rw [Polynomial.degree_X_pow_sub_C hn]
    exact_mod_cast hn.ne'
  obtain ⟨y, hyroot⟩ := IsAlgClosed.exists_root f hfdeg
  have hy : y ^ n = x := by
    have h := hyroot
    simp [f, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow] at h
    exact sub_eq_zero.mp h
  have hyne : y ≠ 0 := by
    intro hy0
    have : x = 0 := by simpa [hy0, zero_pow hn.ne'] using hy.symm
    exact hxne this
  have hnormx : ‖x‖ = 1 := by
    simpa [x] using norm_unit_eq_one (t : U)
  have hnormsq : ‖y‖ ^ n = 1 := by
    rw [← norm_pow, hy, hnormx]
  have hnormy : ‖y‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg y) hn.ne').mp hnormsq
  let sU : U := unitOfNormOne ⟨y, hnormy⟩
  have hspow : sU ^ n = (t : U) := by
    apply Units.ext
    apply Subtype.ext
    change y ^ n = x
    exact hy
  have hs_torsion : sU ∈ mu := by
    rw [CommGroup.mem_torsion]
    have ht : IsOfFinOrder (t : U) := (CommGroup.mem_torsion (t : U)).mp t.property
    obtain ⟨m, hmpos, hm⟩ := isOfFinOrder_iff_pow_eq_one.mp ht
    exact isOfFinOrder_iff_pow_eq_one.mpr
      ⟨n * m, Nat.mul_pos hn hmpos, by
        rw [pow_mul, hspow, hm]⟩
  exact ⟨⟨sU, hs_torsion⟩, by simpa using hspow⟩

#check s2302_exists_root
noncomputable instance s2302Rootable : RootableBy mu ℕ where
  root t n :=
    if hn : n = 0 then 1
    else Classical.choose (s2302_exists_root T b n (Nat.pos_of_ne_zero hn) t)
  root_zero t := by
    apply Subtype.ext
    simp
  root_cancel := by
    intro n t hn
    simp only [hn, dif_neg, not_false_eq_true]
    apply Subtype.ext
    exact Classical.choose_spec (s2302_exists_root T b n (Nat.pos_of_ne_zero hn) t)

noncomputable instance s2302DivisibleNat : DivisibleBy (Additive mu) ℕ where
  div a n := Additive.ofMul (RootableBy.root (Additive.toMul a) n)
  div_zero a := by simp [RootableBy.root_zero]
  div_cancel := by
    intro n a hn
    change n • Additive.ofMul (RootableBy.root (Additive.toMul a) n) = a
    apply Additive.toMul.injective
    simpa [RootableBy.root_cancel _ hn]

noncomputable instance s2302DivisibleInt : DivisibleBy (Additive mu) ℤ :=
  AddGroup.divisibleByIntOfDivisibleByNat (A := Additive mu)

noncomputable def s2302TorsionRetraction : S2297TorsionRetractionRequired T b := by
  classical
  letI : DivisibleBy (Additive mu) ℤ := s2302DivisibleInt T b
  have hBaer : Module.Baer ℤ (Additive mu) := Module.Baer.of_divisible (Additive mu)
  let f : Additive mu →+ Additive U :=
    (CommGroup.torsion U).toAddSubgroup.subtype
  let g : Additive mu →+ Additive mu := AddMonoidHom.id _
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext hxy
  let h := Classical.choose
    (Module.Baer.extension_property_addMonoidHom hBaer f hf g)
  have hcomp := Classical.choose_spec
    (Module.Baer.extension_property_addMonoidHom hBaer f hf g)
  let r : U →* mu :=
    { toFun := fun u => Multiplicative.ofAdd (h (Additive.ofMul u))
      map_one' := by
        change Multiplicative.ofAdd (h 0) = 1
        rw [map_zero h]
        rfl
      map_mul' := by
        intro u v
        change Multiplicative.ofAdd
          (h (Additive.ofMul u + Additive.ofMul v)) =
          Multiplicative.ofAdd (h (Additive.ofMul u)) *
            Multiplicative.ofAdd (h (Additive.ofMul v))
        rw [map_add]
        rfl }
  refine { retraction := r, retraction_torsion := ?_ }
  intro t
  have hval : h (Additive.ofMul (t : U)) = Additive.ofMul (t : mu) := by
    change (h.comp f) (Additive.ofMul (t : mu)) = Additive.ofMul (t : mu)
    rw [hcomp]
    rfl
  have hrt : r t = t := by
    change Multiplicative.ofAdd (h (Additive.ofMul (t : U))) = t
    rw [hval]
    rfl
  exact hrt

/-- Actual S2288 quotient section from the constructed torsion retraction. -/
noncomputable def s2302QuotientSection :
    S2288QuotientSectionRequired T b :=
  s2297Section T b (s2302TorsionRetraction T b)

/-- With S2135, the constructed retraction gives the actual S2249 unit lift. -/
noncomputable def s2302LogKummerOnUnitsOfStrip
    (h : S2135PrimeAlignmentRequired T b) :
    S2249LogKummerOnUnitsRequired T b :=
  s2297LogKummerOnUnitsOfStripAndRetraction T b h
    (s2302TorsionRetraction T b)

/-- The only remaining datum is S2135 prime alignment. -/
structure S2302RemainingRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  primeAlignment : S2135PrimeAlignmentRequired T b

#check s2302QuotientSection
#check s2302LogKummerOnUnitsOfStrip
#check S2302RemainingRequired
#check s2302TorsionRetraction


end LeanFormal.IUT.XiFPaper.S2302TorsionRetractionActual
end
