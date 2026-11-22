import tmp.sheaf.xif.paper.S2482UnderlyingSquareActual

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2482SpecPhiActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482UnderlyingSquareActual
open CategoryTheory AlgebraicGeometry

theorem S2482AffineOver_left :
    S2482AffineOver.left = S2482AffineScheme := rfl

noncomputable def S2482UnderlyingLeft
    (η : S2482Orbicurve.Hom S2482Orbicurve) :
    S2482AffineScheme ⟶ S2482AffineScheme :=
  have hleft : S2482AffineOver.left = S2482AffineScheme := rfl
  by
    simpa [S2482AffineScheme, hleft] using (S2482Underlying η).left

noncomputable def S2482Phi
    (η : S2482Orbicurve.Hom S2482Orbicurve) :
    S2482CoordinateRing →+* S2482CoordinateRing :=
  (Spec.homEquiv (S := CommRingCat.of S2482CoordinateRing)
    (R := CommRingCat.of S2482CoordinateRing)
    (S2482UnderlyingLeft η)).hom

theorem S2482UnderlyingLeft_eq
    (η : S2482Orbicurve.Hom S2482Orbicurve) :
    S2482UnderlyingLeft η = (S2482Underlying η).left := rfl

theorem S2482Phi_spec (η : S2482Orbicurve.Hom S2482Orbicurve) :
    Spec.map (CommRingCat.ofHom (S2482Phi η)) =
      S2482UnderlyingLeft η := by
  change Spec.map (Spec.preimage (S2482UnderlyingLeft η)) = _
  rw [Spec.map_preimage]

theorem S2482Phi_commutes (η : S2482Orbicurve.Hom S2482Orbicurve) :
    (S2482Phi η).comp (algebraMap F S2482CoordinateRing) =
      algebraMap F S2482CoordinateRing := by
  have h := Over.w (S2482Underlying η)
  rw [← S2482UnderlyingLeft_eq] at h
  rw [← S2482Phi_spec] at h
  change Spec.map (CommRingCat.ofHom (S2482Phi η)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap F S2482CoordinateRing)) =
      Spec.map (CommRingCat.ofHom (algebraMap F S2482CoordinateRing)) at h
  rw [← Spec.map_comp, Spec.map_inj] at h
  have h' : ((CommRingCat.ofHom (algebraMap F S2482CoordinateRing)) ≫
      (CommRingCat.ofHom (S2482Phi η))).hom =
      (CommRingCat.ofHom (algebraMap F S2482CoordinateRing)).hom := by
    exact congrArg (fun f => f.hom) h
  simpa [CommRingCat.ofHom_comp, CommRingCat.hom_ofHom,
    CommRingCat.hom_comp] using h'

theorem S2482UnderlyingLeft_comp
    (η : S2482Orbicurve.Hom S2482Orbicurve)
    (h2 : Nonempty (Iso (Iut.HyperbolicOrbicurve.Hom.comp η η)
      (Iut.HyperbolicOrbicurve.Hom.id S2482Orbicurve))) :
    S2482UnderlyingLeft η ≫ S2482UnderlyingLeft η =
      𝟙 S2482AffineScheme := by
  have hg := S2482HomOfStrongTrans_square_of_iso η h2
  have hleft := congrArg
    (fun f : S2482AffineOver ⟶ S2482AffineOver => f.left) hg
  simp only [Over.comp_left, Over.id_left] at hleft
  simpa [S2482UnderlyingLeft, S2482AffineScheme] using hleft

theorem S2482Phi_comp
    (η : S2482Orbicurve.Hom S2482Orbicurve)
    (h2 : Nonempty (Iso (Iut.HyperbolicOrbicurve.Hom.comp η η)
      (Iut.HyperbolicOrbicurve.Hom.id S2482Orbicurve))) :
    (S2482Phi η).comp (S2482Phi η) = RingHom.id S2482CoordinateRing := by
  have hleft := S2482UnderlyingLeft_comp η h2
  rw [← S2482Phi_spec] at hleft
  rw [← Spec.map_comp] at hleft
  rw [show (𝟙 S2482AffineScheme) = Spec.map (𝟙 (CommRingCat.of S2482CoordinateRing)) from
    (Spec.map_id _).symm] at hleft
  rw [Spec.map_inj] at hleft
  have hring := congrArg
    (fun f : CommRingCat.of S2482CoordinateRing ⟶
      CommRingCat.of S2482CoordinateRing => f.hom) hleft
  simpa using hring


end LeanFormal.IUT.XiFPaper.S2482SpecPhiActual
end