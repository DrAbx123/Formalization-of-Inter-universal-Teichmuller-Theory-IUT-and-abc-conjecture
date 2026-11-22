import tmp.sheaf.xif.paper.S1824YonedaCoherenceActual

/-!
# S1840: unconditional proof of `UnitCoherence`

S1824 proves the two `StrongTrans` coherence fields `idCoherence` and
`compCoherence` for the strong transformation `ofObjFull x = ofObj x`, builds the
functors `toObjFunctor`, `ofObjFunctor` and the counit, and reduces the remaining
input for the bicategorical Yoneda comparison to the single proposition
`UnitCoherence S G`: the naturality in the site of the candidate unit components
`unitNat`.

This file proves `UnitCoherence S G` unconditionally.  The proof follows the S1802 /
S1824 component strategy:

* reduce the 2-cell equality in `Cat` to its component at a section `P` by
  `Cat.Hom₂.ext`, `NatTrans.ext` and `funext`;
* normalise the object indices with `a' = mk (op (unop a.as))` and
  `b' = mk (op (unop b.as))`;
* rewrite both `unitNat` components with `unitNat_hom_app` and the `ofNat`
  component with `ofNat_hom_app`;
* apply the strong naturality coherence `eta.naturality_comp` at the section
  `P.op.toLoc` and the morphism `f'`;
* identify the `Y S` comparison and the `Cat` associator components of the resulting
  equation with identities (they are `eqToHom`s between definitionally equal objects);
* merge the remaining `eqToHom`/identity bookkeeping and use the definitional equality
  of the section indices.

No `sorry`, no new axiom and no additional hypothesis are used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1840UnitCoherenceActual

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT.XiFPaper.S1802BicategoricalYonedaActual
open LeanFormal.IUT.XiFPaper.S1824YonedaCoherenceActual

universe u

variable {F : Type u} [Field F]

/-- The remaining unit coherence for the bicategorical Yoneda comparison, proved
unconditionally: `unitNat` is natural in the site. -/
theorem unitCoherence (S : Iut.SchemeOverField F) (G : Iut.EtaleStackPseudofunctor F) :
    UnitCoherence S G := by
  intro eta a b f
  let a' : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ :=
    LocallyDiscrete.mk (Opposite.op (Opposite.unop a.as))
  let b' : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ :=
    LocallyDiscrete.mk (Opposite.op (Opposite.unop b.as))
  let f' : a' ⟶ b' := f
  change (Y S).map f' ◁ (unitNat G eta b').hom ≫
      ((ofObjFull G (toObj G eta)).naturality f').hom =
    (eta.naturality f').hom ≫ (unitNat G eta a').hom ▷ G.map f'
  apply CategoryTheory.Cat.Hom₂.ext
  apply CategoryTheory.NatTrans.ext
  funext P
  obtain ⟨P⟩ := P
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerLeft_app,
    CategoryTheory.Cat.whiskerRight_app, ofNat_hom_app, ofObjFull_naturality,
    CategoryTheory.Cat.Hom.toNatIso_hom]
  rw [unitNat_hom_app]
  rw [unitNat_hom_app]
  simp only [toObj_def]
  simp
  change (eta.naturality (Quiver.Hom.toLoc P.op ≫ f')).hom.toNatTrans.app (Discrete.mk (𝟙 S)) ≫
      (G.mapComp (Quiver.Hom.toLoc P.op) f').hom.toNatTrans.app
        ((eta.app (site S)).toFunctor.obj (Discrete.mk (𝟙 S))) =
    (eta.naturality f').hom.toNatTrans.app (Discrete.mk P) ≫
      (G.map f').toFunctor.map
        ((eta.naturality (Quiver.Hom.toLoc P.op)).hom.toNatTrans.app (Discrete.mk (𝟙 S)))
  let Q0 : (Y S).obj a' :=
    ((Y S).map (Quiver.Hom.toLoc P.op)).toFunctor.obj (Discrete.mk (𝟙 S))
  let Xb : (G.obj b') := ((Y S).map f' ≫ eta.app b').toFunctor.obj Q0
  let Xa : (G.obj b') := (eta.app a' ≫ G.map f').toFunctor.obj Q0
  let Xc : (G.obj b') :=
    (G.map f').toFunctor.obj
      ((G.map (Quiver.Hom.toLoc P.op)).toFunctor.obj
        ((eta.app (site S)).toFunctor.obj (Discrete.mk (𝟙 S))))
  let natf : Xb ⟶ Xa := (eta.naturality f').hom.toNatTrans.app Q0
  let natP : (eta.app a').toFunctor.obj Q0 ⟶
      (G.map (Quiver.Hom.toLoc P.op)).toFunctor.obj
        ((eta.app (site S)).toFunctor.obj (Discrete.mk (𝟙 S))) :=
    (eta.naturality (Quiver.Hom.toLoc P.op)).hom.toNatTrans.app (Discrete.mk (𝟙 S))
  let mp : Xa ⟶ Xc := (G.map f').toFunctor.map natP
  have hYmap : (eta.app b').toFunctor.map
      (((Y S).mapComp (Quiver.Hom.toLoc P.op) f').hom.toNatTrans.app
        (Discrete.mk (𝟙 S))) = 𝟙 Xb := by
    rw [show ((Y S).mapComp (Quiver.Hom.toLoc P.op) f').hom.toNatTrans.app
          (Discrete.mk (𝟙 S)) =
        eqToHom (show ((Y S).map (Quiver.Hom.toLoc P.op ≫ f')).toFunctor.obj
              (Discrete.mk (𝟙 S)) =
            ((Y S).map (Quiver.Hom.toLoc P.op) ≫ (Y S).map f').toFunctor.obj
              (Discrete.mk (𝟙 S)) from rfl) from rfl]
    simp only [CategoryTheory.eqToHom_map, CategoryTheory.eqToHom_refl,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.comp_obj]
    rfl
  have hA1 : (α_ ((Y S).map (Quiver.Hom.toLoc P.op)) ((Y S).map f')
      (eta.app b')).hom.toNatTrans.app (Discrete.mk (𝟙 S)) = 𝟙 Xb := by
    rw [CategoryTheory.Cat.associator_hom_app]
    rfl
  have hA2 : (α_ ((Y S).map (Quiver.Hom.toLoc P.op)) (eta.app a')
      (G.map f')).inv.toNatTrans.app (Discrete.mk (𝟙 S)) = 𝟙 Xa := by
    rw [CategoryTheory.Cat.associator_inv_app]
    rfl
  have hA3 : (α_ (eta.app (site S)) (G.map (Quiver.Hom.toLoc P.op))
      (G.map f')).hom.toNatTrans.app (Discrete.mk (𝟙 S)) = 𝟙 Xc := by
    rw [CategoryTheory.Cat.associator_hom_app]
    rfl
  have hnorm :
      𝟙 Xb ≫ 𝟙 Xb ≫ natf ≫ 𝟙 Xa ≫ mp ≫ 𝟙 Xc =
        (eta.naturality f').hom.toNatTrans.app (Discrete.mk P) ≫ mp := by
    have h1 : 𝟙 Xb ≫ (𝟙 Xb ≫ (natf ≫ (𝟙 Xa ≫ (mp ≫ 𝟙 Xc)))) =
        𝟙 Xb ≫ (natf ≫ (𝟙 Xa ≫ (mp ≫ 𝟙 Xc))) := Category.id_comp _
    have h2 : 𝟙 Xb ≫ (natf ≫ (𝟙 Xa ≫ (mp ≫ 𝟙 Xc))) =
        natf ≫ (𝟙 Xa ≫ (mp ≫ 𝟙 Xc)) := Category.id_comp _
    have h3 : natf ≫ (𝟙 Xa ≫ (mp ≫ 𝟙 Xc)) = natf ≫ (mp ≫ 𝟙 Xc) :=
      congrArg (fun k => natf ≫ k) (Category.id_comp _)
    have h4 : natf ≫ (mp ≫ 𝟙 Xc) = natf ≫ mp :=
      congrArg (fun k => natf ≫ k) (Category.comp_id _)
    have h5 : natf ≫ mp =
        (eta.naturality f').hom.toNatTrans.app (Discrete.mk P) ≫ mp := rfl
    exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
  have h := congrArg (fun α => α.toNatTrans.app (Discrete.mk (𝟙 S)))
    (eta.naturality_comp (Quiver.Hom.toLoc P.op) f')
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerLeft_app,
    CategoryTheory.Cat.whiskerRight_app, CategoryTheory.Functor.map_comp,
    CategoryTheory.eqToHom_map, CategoryTheory.eqToHom_trans] at h
  rw [hYmap, hA1, hA2, hA3] at h
  rw [h]
  exact hnorm

/-- Conditional form of the reverse round trip, now unconditional. -/
noncomputable def unitIso (S : Iut.SchemeOverField F)
    (G : Iut.EtaleStackPseudofunctor F)
    (eta : Pseudofunctor.StrongTrans (Y S) G) :
    eta ≅ ofObjFull G (toObj G eta) :=
  unitIsoOf (S := S) (G := G) (unitCoherence S G) eta

/-! ## Naturality of the unit in the transformation variable and the full comparison -/

/-- Naturality in `eta` of the unit components.  This is the naturality square of the
modification `m` at the section `P.op.toLoc`; the `unitNat` transports are
definitional because `P.as ≫ 𝟙 S = P.as`. -/
theorem unitIso_naturality (S : Iut.SchemeOverField F)
    (G : Iut.EtaleStackPseudofunctor F) (h : UnitCoherence S G)
    {eta theta : Pseudofunctor.StrongTrans (Y S) G} (m : eta ⟶ theta) :
    m ≫ (unitIsoOf (S := S) (G := G) h theta).hom =
      (unitIsoOf (S := S) (G := G) h eta).hom ≫
        (toObjFunctor G ⋙ ofObjFunctor G).map m := by
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro a
  apply CategoryTheory.Cat.Hom₂.ext
  apply CategoryTheory.NatTrans.ext
  funext P
  obtain ⟨P⟩ := P
  change (m.as.app a).toNatTrans.app (Discrete.mk P) ≫
      (unitNat G theta a).hom.toNatTrans.app (Discrete.mk P) =
    (unitNat G eta a).hom.toNatTrans.app (Discrete.mk P) ≫
      (G.map (Quiver.Hom.toLoc P.op)).toFunctor.map
        ((m.as.app (site S)).toNatTrans.app (Discrete.mk (𝟙 S)))
  rw [unitNat_hom_app]
  rw [unitNat_hom_app]
  simp
  have hm := congrArg (fun α => α.toNatTrans.app (Discrete.mk (𝟙 S)))
    (m.as.naturality (Quiver.Hom.toLoc P.op))
  change (m.as.app a).toNatTrans.app
        (((Y S).map (Quiver.Hom.toLoc P.op)).toFunctor.obj (Discrete.mk (𝟙 S))) ≫
      (theta.naturality (Quiver.Hom.toLoc P.op)).hom.toNatTrans.app (Discrete.mk (𝟙 S)) =
    (eta.naturality (Quiver.Hom.toLoc P.op)).hom.toNatTrans.app (Discrete.mk (𝟙 S)) ≫
      (G.map (Quiver.Hom.toLoc P.op)).toFunctor.map
        ((m.as.app (site S)).toNatTrans.app (Discrete.mk (𝟙 S)))
  exact hm

/-- The unit natural isomorphism `𝟭 ≅ toObjFunctor ⋙ ofObjFunctor`, assembled from
`unitCoherence` and the naturality in `eta` proved above. -/
noncomputable def unitNatIso (S : Iut.SchemeOverField F)
    (G : Iut.EtaleStackPseudofunctor F) :
    𝟭 (Pseudofunctor.StrongTrans (Y S) G) ≅ toObjFunctor G ⋙ ofObjFunctor G :=
  NatIso.ofComponents
    (fun eta => unitIsoOf (S := S) (G := G) (unitCoherence S G) eta)
    (by
      intro eta theta m
      exact unitIso_naturality S G (unitCoherence S G) m)

/-- The full bicategorical Yoneda comparison: the category of strong transformations
out of the represented pseudofunctor is equivalent to the value of `G` at the
representing object. -/
theorem yonedaComparison (S : Iut.SchemeOverField F)
    (G : Iut.EtaleStackPseudofunctor F) : YonedaComparison S G :=
  yonedaComparisonOfUnitIso (S := S) (G := G) (unitNatIso S G)

/-- The same comparison in equivalence notation. -/
theorem yonedaEquivalence (S : Iut.SchemeOverField F)
    (G : Iut.EtaleStackPseudofunctor F) :
    Nonempty (Pseudofunctor.StrongTrans (Y S) G ≌ G.obj (site S)) :=
  yonedaComparison S G

end LeanFormal.IUT.XiFPaper.S1840UnitCoherenceActual
