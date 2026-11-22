import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceEvaluationUnitPortionConjugation
import LeanFormal.IUT.IUTIII.Theorem311.SourceH1H2Construction
/-! # S1187: non-refl Kummer iso on the graph common group
G := (v : V) -> upper.Pi v, factorUpper = eval, factorLower = isoPi v o eval.
equiv induced by Units.mapEquiv (phi.isoMon v) via QuotientGroup.congr.
Source action = upper.unitsAction v o eval; target = lower.unitsAction v o
isoPi v o eval.  Equivariance uses phi.compatAction; invariantImage uses
fixedSubgroup mapping.  No refl/conjugation. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S1187NonReflKummerCommonGroupActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.TimesMuKummer
universe uv umon upi
variable {V : Type uv}
variable {upper lower : FPrimeStrip.{umon, uv, upi} V}
noncomputable def quotientUnitsEquiv {U W : Type*} [CommGroup U] [CommGroup W]
    (e : U ≃* W) : TimesMuQuotient U ≃* TimesMuQuotient W :=
  QuotientGroup.congr (CommGroup.torsion U) (CommGroup.torsion W) e e.map_torsion
@[simp] theorem quotientUnitsEquiv_quotientMap
    {U W : Type*} [CommGroup U] [CommGroup W] (e : U ≃* W) (u : U) :
    quotientUnitsEquiv e (TimesMuQuotient.quotientMap u) =
      TimesMuQuotient.quotientMap (e u) := rfl
variable [∀ v, TopologicalSpace (upper.Pi v)]
abbrev GraphGroup : Type _ := (v : V) → upper.Pi v
def factorUpper (v : V) :
    GraphGroup (upper := upper) →* upper.Pi v := Pi.evalMonoidHom _ v
def factorLower (φ : FPrimeStripEquiv upper lower) (v : V) :
    GraphGroup (upper := upper) →* lower.Pi v :=
  (φ.isoPi v).toMonoidHom.comp (Pi.evalMonoidHom _ v)
noncomputable def kummerIsoAt (φ : FPrimeStripEquiv upper lower) (v : V) :
    TimesMuKummer.Isomorphism
      ((upper.unitsAction v).comp (factorUpper v))
      ((lower.unitsAction v).comp (factorLower φ v)) where
  equiv := quotientUnitsEquiv (Units.mapEquiv (φ.isoMon v))
  equivariant := by
    intro g x
    obtain ⟨u, rfl⟩ := TimesMuQuotient.quotientMap_surjective x
    change quotientUnitsEquiv (Units.mapEquiv (φ.isoMon v))
        (TimesMuQuotient.quotientMap (upper.unitsAction v (g v) u)) =
      TimesMuQuotient.quotientMap
        ((lower.unitsAction v) (φ.isoPi v (g v))
          (Units.mapEquiv (φ.isoMon v) u))
    rw [quotientUnitsEquiv_quotientMap]
    congr 1
    ext
    simpa [FPrimeStrip.unitsAction_val] using
      φ.compatAction v ((g : (v : V) → upper.Pi v) v) (u : upper.Mon v)
  invariantImage := by
    intro H
    let eU : (upper.Mon v)ˣ ≃* (lower.Mon v)ˣ := Units.mapEquiv (φ.isoMon v)
    have hcomp_units : ∀ (g : GraphGroup (upper := upper)) (u : (upper.Mon v)ˣ),
        eU (upper.unitsAction v (g v) u) =
          lower.unitsAction v (φ.isoPi v (g v)) (eU u) := by
      intro g u
      ext
      simpa [eU, FPrimeStrip.unitsAction_val] using
        φ.compatAction v (g v) (u : upper.Mon v)
    have hfixed :
        eU '' (TimesMuKummer.fixedSubgroup
          ((upper.unitsAction v).comp (factorUpper v)) H :
          Set (upper.Mon v)ˣ) =
        (TimesMuKummer.fixedSubgroup
          ((lower.unitsAction v).comp (factorLower φ v)) H :
          Set (lower.Mon v)ˣ) := by
      ext y
      constructor
      · rintro ⟨u, hu, rfl⟩
        intro g
        change ((lower.unitsAction v) ((φ.isoPi v) ((g : GraphGroup (upper := upper)) v))) (eU u) = eU u
        rw [← hcomp_units (g : GraphGroup (upper := upper)) u]
        exact congrArg eU (hu g)
      · intro hy
        refine ⟨eU.symm y, ?_, eU.apply_symm_apply y⟩
        intro g
        apply eU.injective
        rw [eU.apply_symm_apply]
        change eU (((upper.unitsAction v) (((g : GraphGroup (upper := upper)) v))) (eU.symm y)) = y
        rw [hcomp_units]
        rw [eU.apply_symm_apply]
        simpa [factorLower, FPrimeStrip.unitsAction_val] using
          hy g
    have hmap : ∀ u : (upper.Mon v)ˣ,
        quotientUnitsEquiv eU (TimesMuQuotient.quotientMap u) =
          TimesMuQuotient.quotientMap (eU u) := by
      intro u; exact quotientUnitsEquiv_quotientMap eU u
    change quotientUnitsEquiv eU ''
        (TimesMuKummer.invariantImage
          ((upper.unitsAction v).comp (factorUpper v)) H) =
      TimesMuKummer.invariantImage
        ((lower.unitsAction v).comp (factorLower φ v)) H
    rw [TimesMuKummer.invariantImage, TimesMuKummer.invariantImage]
    ext x
    constructor
    · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨eU u, hfixed ▸ ⟨u, hu, rfl⟩, hmap u⟩
    · rintro ⟨u, hu, rfl⟩
      refine ⟨TimesMuQuotient.quotientMap (eU.symm u), ?_, ?_⟩
      · refine ⟨eU.symm u, ?_, rfl⟩
        have hmem : eU (eU.symm u) ∈
            eU '' (TimesMuKummer.fixedSubgroup
              ((upper.unitsAction v).comp (factorUpper v)) H :
              Set (upper.Mon v)ˣ) := by
          rw [hfixed]
          rw [eU.apply_symm_apply]
          exact hu
        rcases hmem with ⟨w, hw, hwe⟩
        have hw_eq : w = eU.symm u := eU.injective hwe
        rwa [hw_eq] at hw
      · rw [hmap, eU.apply_symm_apply]
theorem kummerIsoAt_equiv (φ : FPrimeStripEquiv upper lower) (v : V) :
    (kummerIsoAt φ v).equiv = quotientUnitsEquiv (Units.mapEquiv (φ.isoMon v)) := rfl

/-- The lifted Kummer layer on the graph common group: actual, non-refl as soon
as the underlying strip equivalence has nontrivial unit component. -/
noncomputable def nonreflKummerLayer (φ : FPrimeStripEquiv upper lower) :
    SourceTimesMuKummerLayer (GraphGroup (upper := upper)) upper lower where
  sourceAction := fun v => (upper.unitsAction v).comp (factorUpper v)
  targetAction := fun v => (lower.unitsAction v).comp (factorLower φ v)
  kummer := fun v => kummerIsoAt φ v
theorem nonreflKummerLayer_kummer (φ : FPrimeStripEquiv upper lower) (v : V) :
    (nonreflKummerLayer φ).kummer v = kummerIsoAt φ v := rfl
end LeanFormal.IUT.XiFPaper.S1187NonReflKummerCommonGroupActual