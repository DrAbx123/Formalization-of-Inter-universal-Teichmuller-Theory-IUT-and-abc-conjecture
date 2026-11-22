import LeanFormal.IUT.IUTIII.Theorem311.SourceFTimesMuPrimeStripPolyIsomorphism
import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P3GeneralArrowProducerActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

universe uv upi umon

variable {V : Type uv}

/-- Transport of invariant images along a torsion quotient equivalence. -/
theorem timesMuQuotient_congr_invariantImage {G U W : Type*} [Group G]
    [CommGroup U] [CommGroup W] (e : U ≃* W)
    (rhoU : G →* MulAut U) (rhoW : G →* MulAut W)
    (h : ∀ g u, e (rhoU g u) = rhoW g (e u)) (H : OpenSubgroup G) :
    TimesMuQuotient.congr e ''
        (TimesMuKummer.invariantImage rhoU H : Set (TimesMuQuotient U)) =
      (TimesMuKummer.invariantImage rhoW H : Set (TimesMuQuotient W)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [TimesMuKummer.mem_invariantImage_iff] at hy ⊢
    obtain ⟨u, hu, rfl⟩ := hy
    refine ⟨e u, ?_, ?_⟩
    · intro g
      rw [← h g u, hu g]
    · rw [TimesMuQuotient.congr_quotientMap]
  · intro hx
    rw [TimesMuKummer.mem_invariantImage_iff] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    refine ⟨TimesMuQuotient.quotientMap (e.symm w), ?_, ?_⟩
    · rw [TimesMuKummer.mem_invariantImage_iff]
      refine ⟨e.symm w, ?_, rfl⟩
      intro g
      apply e.injective
      rw [h g (e.symm w), e.apply_symm_apply]
      exact hw g
    · rw [TimesMuQuotient.congr_quotientMap, e.apply_symm_apply]

variable {F F' : FPrimeStrip V} (φ : FPrimeStripEquiv F F')

local notation "G" => (v : V) → F.toDPrimeStrip.Pi v

/-- The canonical times-mu isomorphism is a Kummer isomorphism for the
product-unit actions. -/
noncomputable def generalKummerIsomorphism (v : V) :
    TimesMuKummer.Isomorphism
      ((F.unitsAction v).comp (Pi.evalMonoidHom _ v))
      ((F'.unitsAction v).comp ((φ.isoPi v).toMonoidHom.comp (Pi.evalMonoidHom _ v))) where
  equiv := (SourceFTimesMuPrimeStripEquivalence.canonicalLift φ).isoTimesMu v
  equivariant g x := by
    simpa [SourceFTimesMuPrimeStrip.canonical] using
      (SourceFTimesMuPrimeStripEquivalence.canonicalLift φ).compatAction v (g v) x
  invariantImage H := by
    simpa [SourceFTimesMuPrimeStrip.canonical] using
      timesMuQuotient_congr_invariantImage
        (Units.mapEquiv (φ.isoMon v))
        ((F.unitsAction v).comp (Pi.evalMonoidHom _ v))
        ((F'.unitsAction v).comp ((φ.isoPi v).toMonoidHom.comp (Pi.evalMonoidHom _ v)))
        (fun g u => by
          simpa using FPrimeStripEquiv.unitsAction_compat φ v (g v) u)
        H

noncomputable def generalKummerLayer :
    SourceTimesMuKummerLayer (V := V) (G := (v : V) → F.toDPrimeStrip.Pi v)
      F F' where
  sourceAction v := (F.unitsAction v).comp (Pi.evalMonoidHom _ v)
  targetAction v :=
    (F'.unitsAction v).comp ((φ.isoPi v).toMonoidHom.comp (Pi.evalMonoidHom _ v))
  kummer v := generalKummerIsomorphism (φ := φ) v

noncomputable def generalKummerArrow :
    SourceKummerArrow ((v : V) → F.toDPrimeStrip.Pi v) F F' :=
  sourceKummerArrowOfLayer φ (generalKummerLayer (φ := φ))

#print axioms generalKummerIsomorphism
#print axioms generalKummerLayer
#print axioms generalKummerArrow
end LeanFormal.IUT.XiFPaper.Mzk1P3GeneralArrowProducerActual