import tmp.sheaf.xif.paper.S2288UnitLiftActual

/-! # S2297: torsion retraction gives a quotient section

A multiplicative retraction of the integral-closure units onto their torsion
subgroup yields a canonical section of the torsion quotient `S2288QuotientSectionRequired`:
project `u` to `u * (r u)^-1`, which is independent of the representative and
multiplicative.  The retraction is the exact additional structure needed; no
retraction is fabricated. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2297QuotientSectionActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S2219PaperOUnitsCarrierActual
open LeanFormal.IUT.XiFPaper.S2222PaperOUnitsMuAttachmentActual
open LeanFormal.IUT.XiFPaper.S2288UnitLiftActual
open LeanFormal.IUT.XiFPaper.S2249LogKummerTransportActual
open LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Exact additional structure: a multiplicative retraction onto the torsion subgroup. -/
structure S2297TorsionRetractionRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  retraction : S2219PaperOUnits T b →* CommGroup.torsion (S2219PaperOUnits T b)
  retraction_torsion : ∀ t : CommGroup.torsion (S2219PaperOUnits T b),
    retraction t = t

noncomputable def s2297Proj
    (R : S2297TorsionRetractionRequired T b)
    (u : S2219PaperOUnits T b) : S2219PaperOUnits T b :=
  u * ((R.retraction u : S2219PaperOUnits T b)⁻¹)

theorem s2297Proj_quotient
    (R : S2297TorsionRetractionRequired T b)
    (u : S2219PaperOUnits T b) :
    s2219QuotientMap T b (s2297Proj T b R u) =
      s2219QuotientMap T b u := by
  rw [s2297Proj, map_mul, map_inv,
    s2222_torsion_quotient_trivial T b (R.retraction u) (R.retraction u).property,
    inv_one, mul_one]

theorem s2297Proj_torsion
    (R : S2297TorsionRetractionRequired T b)
    (t : S2219PaperOUnits T b)
    (ht : t ∈ CommGroup.torsion (S2219PaperOUnits T b)) :
    s2297Proj T b R t = 1 := by
  have hrt : R.retraction (⟨t, ht⟩ : CommGroup.torsion (S2219PaperOUnits T b)) = (⟨t, ht⟩ : CommGroup.torsion (S2219PaperOUnits T b)) := R.retraction_torsion (⟨t, ht⟩ : CommGroup.torsion (S2219PaperOUnits T b))
  have hval : (R.retraction (⟨t, ht⟩ : CommGroup.torsion (S2219PaperOUnits T b)) :
      S2219PaperOUnits T b) = t :=
    congrArg Subtype.val hrt
  rw [s2297Proj, hval, mul_inv_cancel]

theorem s2297Proj_mul
    (R : S2297TorsionRetractionRequired T b)
    (u v : S2219PaperOUnits T b) :
    s2297Proj T b R (u * v) =
      s2297Proj T b R u * s2297Proj T b R v := by
  have h1 : (R.retraction (u * v) : S2219PaperOUnits T b) =
      (R.retraction u : S2219PaperOUnits T b) *
        (R.retraction v : S2219PaperOUnits T b) := by
    have := congrArg Subtype.val (map_mul R.retraction u v)
    simpa using this
  rw [s2297Proj, s2297Proj, s2297Proj, h1, mul_inv_rev]
  ac_rfl

theorem s2297Proj_eq_of_quotient_eq
    (R : S2297TorsionRetractionRequired T b)
    {u v : S2219PaperOUnits T b}
    (h : s2219QuotientMap T b u = s2219QuotientMap T b v) :
    s2297Proj T b R u = s2297Proj T b R v := by
  have hp : s2219QuotientMap T b (u * v⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have ht : u * v⁻¹ ∈ CommGroup.torsion (S2219PaperOUnits T b) := by
    have hmem : u * v⁻¹ ∈ MonoidHom.ker (s2219QuotientMap T b) :=
      MonoidHom.mem_ker.mpr hp
    simpa [s2219QuotientMap_ker T b] using hmem
  have hu : u = (u * v⁻¹) * v := by group
  rw [hu, s2297Proj_mul, s2297Proj_torsion T b R _ ht, one_mul]

noncomputable def s2297Section
    (R : S2297TorsionRetractionRequired T b) :
    S2288QuotientSectionRequired T b where
  toUnit q :=
    s2297Proj T b R
      (Classical.choose (s2219QuotientMap_surjective T b q))
  toUnit_quotient q := by
    rw [s2297Proj_quotient]
    exact Classical.choose_spec (s2219QuotientMap_surjective T b q)
  toUnit_one := by
    have h1 : s2219QuotientMap T b
        (Classical.choose (s2219QuotientMap_surjective T b 1)) = 1 :=
      Classical.choose_spec (s2219QuotientMap_surjective T b 1)
    have ht : Classical.choose (s2219QuotientMap_surjective T b 1) ∈
        CommGroup.torsion (S2219PaperOUnits T b) := by
      have hmem : Classical.choose (s2219QuotientMap_surjective T b 1) ∈
          MonoidHom.ker (s2219QuotientMap T b) := MonoidHom.mem_ker.mpr h1
      simpa [s2219QuotientMap_ker T b] using hmem
    exact s2297Proj_torsion T b R _ ht
  toUnit_mul q₁ q₂ := by
    rw [← s2297Proj_mul]
    apply s2297Proj_eq_of_quotient_eq T b R
    rw [Classical.choose_spec (s2219QuotientMap_surjective T b (q₁ * q₂))]
    rw [map_mul]
    rw [Classical.choose_spec (s2219QuotientMap_surjective T b q₁)]
    rw [Classical.choose_spec (s2219QuotientMap_surjective T b q₂)]

def S2297TorsionRetractionRequiredProp
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Prop :=
  Nonempty (S2297TorsionRetractionRequired T b)

/-- S2135 plus a torsion retraction fills the full S2249 unit lift. -/
noncomputable def s2297LogKummerOnUnitsOfStripAndRetraction
    (h : S2135PrimeAlignmentRequired T b)
    (R : S2297TorsionRetractionRequired T b) :
    S2249LogKummerOnUnitsRequired T b :=
  s2288LogKummerOnUnitsOfStripAndSection T b h (s2297Section T b R)

/-- Remaining data: S2135 and a torsion retraction. -/
structure S2297RemainingRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  primeAlignment : S2135PrimeAlignmentRequired T b
  torsionRetraction : S2297TorsionRetractionRequired T b

#check s2297LogKummerOnUnitsOfStripAndRetraction
#check S2297RemainingRequired
#check S2297TorsionRetractionRequired
#check s2297Proj_quotient
#check s2297Proj_mul
#check s2297Section
#check S2297TorsionRetractionRequiredProp

end LeanFormal.IUT.XiFPaper.S2297QuotientSectionActual
end
