import tmp.sheaf.xif.paper.S1843SourceAllPointsActual

noncomputable section
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Probe3b

open CategoryTheory
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual

abbrev S1844A : Type := S1726CoordinateRing × S1726CoordinateRing

def S1844delta : S1726K →+* S1844A :=
  (algebraMap S1726K S1726CoordinateRing).prod
    (algebraMap S1726K S1726CoordinateRing)

def S1844diag : S1726CoordinateRing →+* S1844A :=
  (RingHom.id _).prod (RingHom.id _)

def S1844pr1 : S1844A →+* S1726CoordinateRing := RingHom.fst _ _

def S1844swap : S1844A →+* S1844A := RingEquiv.prodComm.toRingHom

theorem S1844swap_delta : S1844swap.comp S1844delta = S1844delta := rfl
theorem S1844diag_delta :
    S1844diag.comp (algebraMap S1726K S1726CoordinateRing) = S1844delta := rfl
theorem S1844pr1_delta :
    S1844pr1.comp S1844delta = algebraMap S1726K S1726CoordinateRing := rfl
theorem S1844pr1_diag : S1844pr1.comp S1844diag = RingHom.id _ := rfl
theorem S1844swap_diag : S1844swap.comp S1844diag = S1844diag := rfl

#check @CommRingCat.ofHom_id
#check @CommRingCat.ofHom_comp
#check @CommRingCat.Hom.hom
#check @ConcreteCategory.hom

example {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) :
    (CommRingCat.ofHom f) ≫ (CommRingCat.ofHom g) = CommRingCat.ofHom (g.comp f) := rfl

example {R : Type} [CommRing R] : (CommRingCat.ofHom (RingHom.id R) : CommRingCat.of R ⟶ CommRingCat.of R) = 𝟙 _ := rfl

abbrev S1844Q : SchemeOverField S1726K :=
  Over.mk (Spec.map (CommRingCat.ofHom S1844delta))

noncomputable def S1844nabla : S1844Q ⟶ S1726AffineOver :=
  Over.homMk (Spec.map (CommRingCat.ofHom S1844diag)) (by
    change Spec.map (CommRingCat.ofHom S1844diag) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S1726K S1726CoordinateRing)) =
      Spec.map (CommRingCat.ofHom S1844delta)
    rw [← Spec.map_comp (CommRingCat.ofHom (algebraMap S1726K S1726CoordinateRing))
      (CommRingCat.ofHom S1844diag)]
    exact congrArg Spec.map (by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact congrArg (fun f => f a) S1844diag_delta))

noncomputable def S1844iota : S1726AffineOver ⟶ S1844Q :=
  Over.homMk (Spec.map (CommRingCat.ofHom S1844pr1)) (by
    change Spec.map (CommRingCat.ofHom S1844pr1) ≫
      Spec.map (CommRingCat.ofHom S1844delta) =
      Spec.map (CommRingCat.ofHom (algebraMap S1726K S1726CoordinateRing))
    rw [← Spec.map_comp (CommRingCat.ofHom S1844delta) (CommRingCat.ofHom S1844pr1)]
    exact congrArg Spec.map (by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact congrArg (fun f => f a) S1844pr1_delta))

noncomputable def S1844swapMap : S1844Q ⟶ S1844Q :=
  Over.homMk (Spec.map (CommRingCat.ofHom S1844swap)) (by
    change Spec.map (CommRingCat.ofHom S1844swap) ≫
      Spec.map (CommRingCat.ofHom S1844delta) =
      Spec.map (CommRingCat.ofHom S1844delta)
    rw [← Spec.map_comp (CommRingCat.ofHom S1844delta) (CommRingCat.ofHom S1844swap)]
    exact congrArg Spec.map (by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact congrArg (fun f => f a) S1844swap_delta))

theorem S1844iota_nabla : S1844iota ≫ S1844nabla = 𝟙 S1726AffineOver := by
  apply Over.OverMorphism.ext
  show Spec.map (CommRingCat.ofHom S1844pr1) ≫ Spec.map (CommRingCat.ofHom S1844diag) =
    𝟙 (Spec (CommRingCat.of S1726CoordinateRing))
  rw [← Spec.map_comp (CommRingCat.ofHom S1844diag) (CommRingCat.ofHom S1844pr1)]
  rw [show (CommRingCat.ofHom S1844diag) ≫ (CommRingCat.ofHom S1844pr1) =
      𝟙 (CommRingCat.of S1726CoordinateRing) from by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact congrArg (fun f => f a) S1844pr1_diag]
  exact Spec.map_id _

theorem S1844swap_nabla : S1844swapMap ≫ S1844nabla = S1844nabla := by
  apply Over.OverMorphism.ext
  show Spec.map (CommRingCat.ofHom S1844swap) ≫ Spec.map (CommRingCat.ofHom S1844diag) =
    Spec.map (CommRingCat.ofHom S1844diag)
  rw [← Spec.map_comp (CommRingCat.ofHom S1844diag) (CommRingCat.ofHom S1844swap)]
  exact congrArg Spec.map (by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact congrArg (fun f => f a) S1844swap_diag)

/-- R' is nontrivial: it has a K-rational point. -/
theorem S1844nontrivialRing : Nontrivial S1726CoordinateRing := by
  refine ⟨0, 1, ?_⟩
  intro h
  have h' : (S1726PointAlgHom (0 : S1726K) (0 : S1726K)) (1 : S1726CoordinateRing) =
      (S1726PointAlgHom (0 : S1726K) (0 : S1726K)) (0 : S1726CoordinateRing) := by rw [h]
  rw [map_one, map_zero] at h'
  exact zero_ne_one h'

instance S1844nontrivialRingInst : Nontrivial S1726CoordinateRing := S1844nontrivialRing

/-- The swap is not the identity. -/
theorem S1844swap_ne : (𝟙 S1844Q) ≠ S1844swapMap := by
  intro h
  have hleft : Over.Hom.left (𝟙 S1844Q) = Over.Hom.left S1844swapMap :=
    congrArg Over.Hom.left h
  have hspec : Spec.map (𝟙 (CommRingCat.of S1844A)) =
      Spec.map (CommRingCat.ofHom S1844swap) := hleft
  rw [Spec.map_id] at hspec
  have hring : (𝟙 (CommRingCat.of S1844A) : CommRingCat.of S1844A ⟶ CommRingCat.of S1844A) =
      CommRingCat.ofHom S1844swap := Spec.map_injective hspec
  have hR : (RingHom.id S1844A) = S1844swap := hring
  have hpt := congrArg (fun f : S1844A →+* S1844A => f ((1, 0))) hR
  simp [S1844swap] at hpt

end Probe3b
