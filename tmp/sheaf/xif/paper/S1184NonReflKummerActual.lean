import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceEvaluationUnitPortionConjugation
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.IUTIII.Theorem311.SourceH1H2Construction
/-! # S1184: actual non-refl Kummer isomorphism from a strip equivalence
For an actual FPrimeStripEquiv φ : upper ≃ lower, the units equivalence
(φ.isoMon v).units induces a quotient equivalence
TimesMuQuotient (upper.Mon v)^x ≃* TimesMuQuotient (lower.Mon v)^x.
With source action = upper.unitsAction v and target action = lower.unitsAction v
transported along φ.isoPi v, the compatibility `compatAction` gives an actual
TimesMuKummer.Isomorphism.  No refl/conjugation. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S1184NonReflKummerActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.TimesMuKummer
universe u v uv umon upi
variable {V : Type uv} {G : Type u} [Group G] [TopologicalSpace G]
noncomputable def quotientUnitsEquiv {U W : Type*} [CommGroup U] [CommGroup W]
    (e : U ≃* W) :
    TimesMuQuotient U ≃* TimesMuQuotient W :=
  QuotientGroup.congr (CommGroup.torsion U) (CommGroup.torsion W) e e.map_torsion
@[simp] theorem quotientUnitsEquiv_quotientMap {U W : Type*} [CommGroup U] [CommGroup W]
    (e : U ≃* W) (u : U) :
    quotientUnitsEquiv e (TimesMuQuotient.quotientMap u) =
      TimesMuQuotient.quotientMap (e u) := rfl

variable {upper lower : FPrimeStrip.{uv, uv, uv} V}
variable (φ : FPrimeStripEquiv upper lower) (v : V)
variable [TopologicalSpace (upper.Pi v)]
noncomputable def stripEquivKummerIso :
    TimesMuKummer.Isomorphism (upper.unitsAction v)
      ((lower.unitsAction v).comp (φ.isoPi v)) where
  equiv := quotientUnitsEquiv (Units.mapEquiv (φ.isoMon v))
  equivariant := by
    intro g x
    obtain ⟨u, rfl⟩ := TimesMuQuotient.quotientMap_surjective x
    change quotientUnitsEquiv (Units.mapEquiv (φ.isoMon v))
        (TimesMuQuotient.quotientMap (upper.unitsAction v g u)) =
      TimesMuQuotient.quotientMap
        ((lower.unitsAction v) (φ.isoPi v g) (Units.mapEquiv (φ.isoMon v) u))
    rw [quotientUnitsEquiv_quotientMap]
    congr 1
    ext
    simpa [FPrimeStrip.unitsAction_val] using
      φ.compatAction v g (u : upper.Mon v)
  invariantImage := by
    intro H
    let eU : (upper.Mon v)ˣ ≃* (lower.Mon v)ˣ := Units.mapEquiv (φ.isoMon v)
    have hfixed :
        eU '' (TimesMuKummer.fixedSubgroup (upper.unitsAction v) H :
          Set (upper.Mon v)ˣ) =
        (TimesMuKummer.fixedSubgroup
          ((lower.unitsAction v).comp (φ.isoPi v)) H :
          Set (lower.Mon v)ˣ) := by
      ext y
      constructor
      · rintro ⟨u, hu, rfl⟩
        intro g
        change (lower.unitsAction v) (φ.isoPi v g) (eU u) = eU u
        conv_rhs => rw [← hu g]
        ext
        simpa [eU, FPrimeStrip.unitsAction_val] using
          (φ.compatAction v g (u : upper.Mon v)).symm
      · intro hy
        refine ⟨eU.symm y, ?_, eU.apply_symm_apply y⟩
        intro g
        apply eU.injective
        rw [eU.apply_symm_apply]
        have h := hy g
        have h' : ((lower.action v) ((φ.isoPi v) (g : upper.Pi v)))
            (y : lower.Mon v) = (y : lower.Mon v) := by
          simpa [FPrimeStrip.unitsAction_val] using congrArg Units.val h
        apply Units.ext
        have hc := φ.compatAction v g
          ((eU.symm y : (upper.Mon v)ˣ) : upper.Mon v)
        dsimp [eU] at hc ⊢
        simpa [Units.coe_mapEquiv, FPrimeStrip.unitsAction_val, h'] using hc
    have hmap : ∀ u : (upper.Mon v)ˣ,
        quotientUnitsEquiv eU (TimesMuQuotient.quotientMap u) =
          TimesMuQuotient.quotientMap (eU u) := by
      intro u; exact quotientUnitsEquiv_quotientMap eU u
    change quotientUnitsEquiv eU ''
        (TimesMuKummer.invariantImage (upper.unitsAction v) H) =
      TimesMuKummer.invariantImage ((lower.unitsAction v).comp (φ.isoPi v)) H
    rw [TimesMuKummer.invariantImage, TimesMuKummer.invariantImage]
    ext x
    constructor
    · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨eU u, hfixed ▸ ⟨u, hu, rfl⟩, hmap u⟩
    · rintro ⟨u, hu, rfl⟩
      refine ⟨TimesMuQuotient.quotientMap (eU.symm u), ?_, ?_⟩
      · refine ⟨eU.symm u, ?_, rfl⟩
        have hpre : eU ⁻¹'
            (TimesMuKummer.fixedSubgroup
              ((lower.unitsAction v).comp (φ.isoPi v)) H :
              Set (lower.Mon v)ˣ) =
            (TimesMuKummer.fixedSubgroup (upper.unitsAction v) H :
              Set (upper.Mon v)ˣ) := by
          rw [← hfixed, Set.preimage_image_eq _ eU.injective]
        rw [← hpre]
        simpa using hu
      · rw [hmap, eU.apply_symm_apply]
theorem stripEquivKummerIso_equiv :
    (stripEquivKummerIso (V := V) (φ := φ) (v := v)).equiv =
      quotientUnitsEquiv (Units.mapEquiv (φ.isoMon v)) := rfl
end LeanFormal.IUT.XiFPaper.S1184NonReflKummerActual