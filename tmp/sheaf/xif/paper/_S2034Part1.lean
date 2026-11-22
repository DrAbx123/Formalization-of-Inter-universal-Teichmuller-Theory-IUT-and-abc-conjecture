import tmp.sheaf.xif.paper.S1978LocalFieldOCarrierActual
import tmp.sheaf.xif.paper.S1951KummerEvaluationSquareActual

/-! # S2034 Part 1: core operation-level Kummer construction on the actual local O^x carrier

Layer O.  Actual local carrier of S1978; core Kummer isomorphism and its
nontriviality.  No evaluation square/evaluation iso in this part; those stay
in the full S2034 file.  No sorry/axiom/placeholder. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2034OperationKummerActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1951KummerEvaluationSquareActual
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual
open General

abbrev LocV : Type := PaperV
abbrev LocG : Type := LocalOFieldGaloisProduct
abbrev actualOUnits (v : LocV) : Type := LocalOFieldUnitsAt v

noncomputable abbrev actualOUnitsAction (v : LocV) :
    LocG →* MulAut (actualOUnits v) :=
  (LocalOFieldUnitsActionAt v).comp (localOFieldFactorization v)

abbrev actualOUnitsMu (v : LocV) : Type := TimesMuQuotient (actualOUnits v)

noncomputable abbrev actualOUnitsMuAction (v : LocV) :
    LocG →* MulAut (actualOUnitsMu v) :=
  TimesMuQuotient.action (actualOUnitsAction v)

noncomputable abbrev actualStripUnitsAction (v : LocV) :
    LocG →* MulAut ((localOFieldStrip.Mon v)ˣ) :=
  (localOFieldStrip.unitsAction v).comp (localOFieldFactorization v)

@[simp] theorem actualOUnitsMuAction_quotientMap (v : LocV) (g : LocG)
    (u : actualOUnits v) :
    actualOUnitsMuAction v g (TimesMuQuotient.quotientMap u) =
      TimesMuQuotient.quotientMap (actualOUnitsAction v g u) := rfl

noncomputable abbrev actualUnit (v : LocV) : actualOUnits v :=
  @localOFieldUnit v.1 ⟨v.prime⟩

theorem actualUnit_quotient_ne_one (v : LocV) :
    TimesMuQuotient.quotientMap (actualUnit v) ≠ 1 :=
  @localOFieldUnit_quotient_ne_one v.1 ⟨v.prime⟩

theorem actualOUnitsMu_nontrivial (v : LocV) :
    (TimesMuQuotient.quotientMap (actualUnit v) : actualOUnitsMu v) ≠ 1 :=
  actualUnit_quotient_ne_one v

/-- A multiplicative equivalence preserves the torsion subgroup. -/
theorem mem_torsion_mapEquiv_iff {U W : Type*} [CommGroup U] [CommGroup W]
    (e : U ≃* W) (u : U) :
    e u ∈ CommGroup.torsion W ↔ u ∈ CommGroup.torsion U := by
  constructor
  · intro h
    obtain ⟨n, hn, hpow⟩ :=
      isOfFinOrder_iff_pow_eq_one.mp ((CommGroup.mem_torsion (e u)).mp h)
    exact (CommGroup.mem_torsion u).mpr (isOfFinOrder_iff_pow_eq_one.mpr
      ⟨n, hn, e.injective (by rw [map_pow, hpow, map_one])⟩)
  · intro h
    obtain ⟨n, hn, hpow⟩ :=
      isOfFinOrder_iff_pow_eq_one.mp ((CommGroup.mem_torsion u).mp h)
    exact (CommGroup.mem_torsion (e u)).mpr (isOfFinOrder_iff_pow_eq_one.mpr
      ⟨n, hn, by rw [← map_pow, hpow, map_one]⟩)

/-- A G-equivariant multiplicative equivalence carries invariant images. -/
theorem quotientUnitsEquiv_image_invariantImage
    {G : Type*} [Group G] [TopologicalSpace G]
    {U W : Type*} [CommGroup U] [CommGroup W]
    {source : G →* MulAut U} {target : G →* MulAut W}
    (e : U ≃* W) (he : ∀ (g : G) (u : U), e (source g u) = target g (e u))
    (H : OpenSubgroup G) :
    quotientUnitsEquiv e ''
        (TimesMuKummer.invariantImage source H : Set (TimesMuQuotient U)) =
      (TimesMuKummer.invariantImage target H : Set (TimesMuQuotient W)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨u, hu, rfl⟩ :=
      (TimesMuKummer.mem_invariantImage_iff source H y).mp hy
    refine (TimesMuKummer.mem_invariantImage_iff target H _).mpr
      ⟨e u, ?_, ?_⟩
    · intro g
      rw [← he, hu g]
    · rw [quotientUnitsEquiv_quotientMap]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨TimesMuQuotient.quotientMap (e.symm w), ?_, ?_⟩
    · refine (TimesMuKummer.mem_invariantImage_iff source H _).mpr
        ⟨e.symm w, ?_, rfl⟩
      intro g
      apply e.injective
      rw [he, MulEquiv.apply_symm_apply, hw g]
    · rw [quotientUnitsEquiv_quotientMap, MulEquiv.apply_symm_apply]

noncomputable def kummerMuEquiv (v : LocV) :
    actualOUnitsMu v ≃* TimesMuQuotient ((localOFieldStrip.Mon v)ˣ) :=
  quotientUnitsEquiv (groupUnitsEquiv (actualOUnits v))

theorem kummerMuEquiv_quotientMap (v : LocV) (u : actualOUnits v) :
    kummerMuEquiv v (TimesMuQuotient.quotientMap u) =
      TimesMuQuotient.quotientMap
        ((groupUnitsEquiv (actualOUnits v)) u : (localOFieldStrip.Mon v)ˣ) :=
  quotientUnitsEquiv_quotientMap _ u

noncomputable def actualKummerIso (v : LocV) :
    TimesMuKummer.Isomorphism (actualOUnitsAction v)
      (actualStripUnitsAction v) where
  equiv := kummerMuEquiv v
  equivariant := by
    intro g x
    obtain ⟨u, rfl⟩ := TimesMuQuotient.quotientMap_surjective x
    rw [TimesMuQuotient.action_quotientMap, kummerMuEquiv_quotientMap,
      TimesMuQuotient.action_quotientMap]
    congr 1
    simpa [actualOUnitsAction, actualStripUnitsAction, MonoidHom.comp_apply] using
      localOFieldStrip_unitsAction_groupUnitsEquiv v
        (localOFieldFactorization v g) u
  invariantImage := by
    intro H
    exact quotientUnitsEquiv_image_invariantImage (groupUnitsEquiv (actualOUnits v))
      (fun g u => by
        simpa [actualOUnitsAction, actualStripUnitsAction, MonoidHom.comp_apply] using
          localOFieldStrip_unitsAction_groupUnitsEquiv v
            (localOFieldFactorization v g) u) H

theorem actualKummerIso_class_ne_one (v : LocV) :
    (actualKummerIso v).equiv
      (TimesMuQuotient.quotientMap (actualUnit v)) ≠ 1 := by
  intro h
  have hq : kummerMuEquiv v (TimesMuQuotient.quotientMap (actualUnit v)) = 1 := h
  rw [kummerMuEquiv_quotientMap] at hq
  have hsrc : TimesMuQuotient.quotientMap (actualUnit v) = 1 := by
    apply (kummerMuEquiv v).injective
    simpa using hq
  exact actualUnit_quotient_ne_one v hsrc

noncomputable def actualKappaDatum :
    KappaOrbitUnitsActionDatum LocG localOFieldStrip where
  sourceUnits := actualOUnits
  commGroupSourceUnits := fun _ => inferInstance
  sourceAction := actualOUnitsAction
  factor := localOFieldFactorization
  kappa := actualKummerIso

#check actualKummerIso
#check actualKummerIso_class_ne_one
#check actualKappaDatum
#print axioms actualKummerIso
#print axioms actualKummerIso_class_ne_one
#print axioms actualKappaDatum

end LeanFormal.IUT.XiFPaper.S2034OperationKummerActual

end