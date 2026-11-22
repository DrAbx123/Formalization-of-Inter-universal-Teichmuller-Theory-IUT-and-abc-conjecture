import tmp.sheaf.xif.paper.S1348D6OrbicurveActual

noncomputable section
open CategoryTheory
open AlgebraicGeometry
open scoped SpecOfNotation
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1331OrbicurveClauseAudit
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual

namespace S1419Probe15Adapted

variable (l : PrimeGeFive)

noncomputable abbrev S1419AffineScheme : Scheme :=
  Spec (CommRingCat.of (S1348CoordinateRing l))

noncomputable abbrev S1419AffineOver : Iut.SchemeOverField (S1348K l) :=
  Over.mk (Spec.map (CommRingCat.ofHom
    (algebraMap (S1348K l) (S1348CoordinateRing l))))

noncomputable abbrev S1419Base : Iut.SchemeOverField (S1348K l) :=
  Over.mk (𝟙 (Spec (CommRingCat.of (S1348K l))))

noncomputable def S1419OverOfAlgHom
    (ψ : S1348CoordinateRing l →ₐ[S1348K l] S1348K l) :
    S1419Base l ⟶ S1419AffineOver l :=
  Over.homMk (Spec.map (CommRingCat.ofHom ψ.toRingHom)) (by
    dsimp [S1419Base, S1419AffineOver]
    erw [← Spec.map_comp]
    rw [← CommRingCat.ofHom_comp]
    have h : ψ.toRingHom.comp (algebraMap (S1348K l) (S1348CoordinateRing l)) =
        RingHom.id (S1348K l) := by
      ext x
      exact ψ.commutes x
    change Spec.map (CommRingCat.ofHom
      (ψ.toRingHom.comp (algebraMap (S1348K l) (S1348CoordinateRing l)))) =
      𝟙 (Spec (CommRingCat.of (S1348K l)))
    rw [h]
    change Spec.map (𝟙 (CommRingCat.of (S1348K l))) =
      𝟙 (Spec (CommRingCat.of (S1348K l)))
    rw [Spec.map_id])

theorem S1419OverOfAlgHom_injective :
    Function.Injective (S1419OverOfAlgHom l) := by
  intro ψ₁ ψ₂ h
  have hleft : (S1419OverOfAlgHom l ψ₁).left = (S1419OverOfAlgHom l ψ₂).left :=
    congrArg (fun f => f.left) h
  change Spec.map (CommRingCat.ofHom ψ₁.toRingHom) =
    Spec.map (CommRingCat.ofHom ψ₂.toRingHom) at hleft
  have hringCat := Spec.map_injective hleft
  have hring : ψ₁.toRingHom = ψ₂.toRingHom := congrArg CommRingCat.Hom.hom hringCat
  ext x
  exact congrArg (fun φ : S1348CoordinateRing l →+* S1348K l => φ x) hring

theorem S1419Nonterminal :
    ¬ Subsingleton (S1419Base l ⟶ S1419AffineOver l) := by
  intro hsub
  let P₁ : S1331ClausePuncturedCurve l := ⟨S1331Point l, S1331Point_ne_puncture l⟩
  let P₂ : S1331ClausePuncturedCurve l := ⟨S1331PointNeg l, S1331PointNeg_ne_puncture l⟩
  obtain ⟨ψ₁, h₁⟩ := S1348PointAlgHom_surjective l P₁
  obtain ⟨ψ₂, h₂⟩ := S1348PointAlgHom_surjective l P₂
  have hP : P₁ ≠ P₂ := by
    intro h
    exact S1331Point_ne_S1331PointNeg l (congrArg Subtype.val h)
  have hψ : ψ₁ ≠ ψ₂ := by
    intro h
    apply hP
    rw [← h₁, ← h₂, h]
  have hover : S1419OverOfAlgHom l ψ₁ ≠ S1419OverOfAlgHom l ψ₂ :=
    fun h => hψ (S1419OverOfAlgHom_injective l h)
  exact hover (Subsingleton.elim _ _)

end S1419Probe15Adapted

end
