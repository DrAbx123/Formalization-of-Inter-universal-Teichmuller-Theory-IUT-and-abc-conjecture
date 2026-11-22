import tmp.sheaf.xif.paper.S1660SectionKPlaceRootActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionLocalInputs
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped WithZero Valued
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1444ReportAKPlaceQActual
open LeanFormal.IUT.XiFPaper.S1647RouteARootActual
open LeanFormal.IUT.XiFPaper.S1660SectionKPlaceRootActual
open LeanFormal.IUT.InitialThetaSource.PlaceQParameterUniformization
namespace LeanFormal.IUT.XiFPaper.S1668UnitRootDescentActual
variable {K : Type*} [Field K] [NumberField K] (v : NumberField.FinitePlace K)
abbrev A : Type _ := Completion v
noncomputable def s1668Pi : A v :=
  ((adicCompletion_uniformizer (K := K) v.maximalIdeal).1 : A v)
theorem s1668Pi_valued :
    (Valued.v (s1668Pi v) : WithZero (Multiplicative Int)) =
      WithZero.exp (-1 : Int) := by
  simpa [s1668Pi] using uniformizer_valued_eq_exp_neg_one (K := K) v.maximalIdeal
    (adicCompletion_uniformizer (K := K) v.maximalIdeal)
theorem s1668Pi_ne_zero : s1668Pi v ≠ 0 := by
  intro h
  have hval := s1668Pi_valued v
  rw [h, map_zero] at hval
  exact WithZero.exp_ne_zero hval.symm
theorem s1668Unit_valued_ne_zero (u : (A v)ˣ) :
    (Valued.v (u : A v) : WithZero (Multiplicative Int)) ≠ 0 :=
  fun h => Units.ne_zero u ((Valued.v).map_eq_zero_iff.mp h)
noncomputable def s1668UnitValuationExponent (u : (A v)ˣ) : Int :=
  WithZero.log (Valued.v (u : A v))
theorem s1668Unit_valued_eq_exp (u : (A v)ˣ) :
    (Valued.v (u : A v) : WithZero (Multiplicative Int)) =
      WithZero.exp (s1668UnitValuationExponent v u) := by
  dsimp [s1668UnitValuationExponent]
  exact (WithZero.exp_log (s1668Unit_valued_ne_zero v u)).symm
theorem s1668Pi_pow_valued (m : Int) :
    (Valued.v (s1668Pi v ^ m) : WithZero (Multiplicative Int)) =
      WithZero.exp (-m) := by
  rw [map_zpow₀, s1668Pi_valued]
  rw [show WithZero.exp (-1 : Int) ^ m = WithZero.exp (m • (-1 : Int)) from
    (WithZero.exp_zsmul m (-1 : Int)).symm]
  congr 1
  simp
theorem s1668ExistsUniformizerDVRDecomposition (u : (A v)ˣ) :
    ∃ m : Int, ∃ u0 : (Valued.v.integer)ˣ,
      (u : A v) = s1668Pi v ^ m * ((u0.val).1 : A v) := by
  let k : Int := s1668UnitValuationExponent v u
  let x : A v := (u : A v) * s1668Pi v ^ k
  have hxval : (Valued.v x : WithZero (Multiplicative Int)) = 1 := by
    dsimp [x]
    rw [map_mul, s1668Unit_valued_eq_exp, s1668Pi_pow_valued]
    rw [← WithZero.exp_add]
    rw [show k + -k = 0 by ring, WithZero.exp_zero]
  have hxmem : x ∈ Valued.v.integer := by
    rw [Valuation.mem_integer_iff]
    exact le_of_eq hxval
  have hx0 : x ≠ 0 := mul_ne_zero (Units.ne_zero u)
    (zpow_ne_zero k (s1668Pi_ne_zero v))
  have hxinvval : (Valued.v x⁻¹ : WithZero (Multiplicative Int)) = 1 := by
    rw [map_inv₀, hxval, inv_one]
  have hxinvmem : x⁻¹ ∈ Valued.v.integer := by
    rw [Valuation.mem_integer_iff]
    exact le_of_eq hxinvval
  let u0 : (Valued.v.integer)ˣ :=
    { val := ⟨x, hxmem⟩
      inv := ⟨x⁻¹, hxinvmem⟩
      val_inv := by
        apply Subtype.ext
        change x * x⁻¹ = 1
        exact mul_inv_cancel₀ hx0
      inv_val := by
        apply Subtype.ext
        change x⁻¹ * x = 1
        exact inv_mul_cancel₀ hx0 }
  refine ⟨-k, u0, ?_⟩
  change (u : A v) = s1668Pi v ^ (-k) * ((u0.val).1 : A v)
  rw [show ((u0.val).1 : A v) = x from rfl]
  dsimp [x]
  rw [zpow_neg,
    mul_comm ((s1668Pi v ^ k)⁻¹)
      ((u : A v) * s1668Pi v ^ k),
    mul_assoc,
    mul_inv_cancel₀ (zpow_ne_zero k (s1668Pi_ne_zero v)),
    mul_one]
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
abbrev Ksection : Type _ := Completion (sectionKPlace T b)
noncomputable def s1668QUnit : (Ksection T b)ˣ :=
  Units.mk0 (sectionQ T b).q (sectionQ T b).q_ne_zero
theorem s1668QUnit_val : ((s1668QUnit T b : (Ksection T b)ˣ) : Ksection T b) =
    (sectionQ T b).q := rfl
noncomputable def s1668QExponent : ℤ :=
  Classical.choose (s1668ExistsUniformizerDVRDecomposition (sectionKPlace T b)
    (s1668QUnit T b))
noncomputable def s1668QUnitPart :
    ((Valued.v (R := Ksection T b) :
      Valuation (Ksection T b) (WithZero (Multiplicative Int))).integer)ˣ :=
  Classical.choose (Classical.choose_spec
    (s1668ExistsUniformizerDVRDecomposition (sectionKPlace T b)
      (s1668QUnit T b)))
theorem s1668Q_decomp :
    ((s1668QUnit T b : (Ksection T b)ˣ) : Ksection T b) =
      s1668Pi (sectionKPlace T b) ^ s1668QExponent T b *
        ((s1668QUnitPart T b).val.1 : Ksection T b) :=
  Classical.choose_spec (Classical.choose_spec
    (s1668ExistsUniformizerDVRDecomposition (sectionKPlace T b)
      (s1668QUnit T b)))
noncomputable def s1668QUnitPartField : (Ksection T b)ˣ :=
  Units.mk0 (((s1668QUnitPart T b).val).1 : Ksection T b) (by
    intro h
    have h0 : (s1668QUnitPart T b).val = 0 := Subtype.ext h
    exact (Units.ne_zero (s1668QUnitPart T b)) h0)
structure S1668UnitRootOnly where
  t : ℤ
  ht : s1668QExponent T b = (2 * (l.value : ℤ)) * t
  unit_root : (Ksection T b)ˣ
  unit_root_pow : unit_root ^ (2 * l.value) = s1668QUnitPartField T b
noncomputable def s1668RootFromUnitRoot (D : S1668UnitRootOnly (l := l) T b) :
    Ksection T b :=
  (D.unit_root : Ksection T b) * s1668Pi (sectionKPlace T b) ^ D.t
theorem s1668RootFromUnitRoot_ne_zero (D : S1668UnitRootOnly (l := l) T b) :
    s1668RootFromUnitRoot (l := l) T b D ≠ 0 := by
  unfold s1668RootFromUnitRoot
  exact mul_ne_zero (Units.ne_zero D.unit_root)
    (zpow_ne_zero D.t (s1668Pi_ne_zero (sectionKPlace T b)))
theorem s1668RootFromUnitRoot_pow (D : S1668UnitRootOnly (l := l) T b) :
    s1668RootFromUnitRoot (l := l) T b D ^ (2 * l.value) =
      (sectionQ T b).q := by
  unfold s1668RootFromUnitRoot
  have hroot : ((D.unit_root : Ksection T b) ^ (2 * l.value)) =
      ((s1668QUnitPartField T b : (Ksection T b)ˣ) : Ksection T b) := by
    exact_mod_cast D.unit_root_pow
  rw [mul_pow, hroot]
  change ((s1668QUnitPart T b).val.1 : Ksection T b) *
      (s1668Pi (sectionKPlace T b) ^ D.t) ^ (2 * l.value) =
        (sectionQ T b).q
  rw [← zpow_natCast, ← zpow_mul]
  have hexp : D.t * (↑(2 * l.value) : ℤ) = (2 * (l.value : ℤ)) * D.t := by
    push_cast
    ring
  rw [hexp, ← D.ht]
  rw [← s1668QUnit_val, s1668Q_decomp]
  ring
noncomputable def s1668RootCardFromUnitRoot (D : S1668UnitRootOnly (l := l) T b) :
    QParameterTwoLRootCard l (sectionKPlace T b) (sectionQ T b) :=
  QParameterTwoLRootCard.ofRoot (s1668RootFromUnitRoot (l := l) T b D)
    (s1668RootFromUnitRoot_ne_zero (l := l) T b D)
    (s1668RootFromUnitRoot_pow (l := l) T b D)
end LeanFormal.IUT.XiFPaper.S1668UnitRootDescentActual


end
