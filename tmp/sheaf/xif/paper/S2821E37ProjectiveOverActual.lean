import tmp.sheaf.xif.paper.S2820E37TransitionActual
import Mathlib.AlgebraicGeometry.Gluing

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2821E37ProjectiveOverActual

open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual

universe u

variable (K : Type) [Field K]

/-- Chart structure maps, indexed by the glue-data index J = ULift Bool. -/
noncomputable def S2821ChartStructure (b : E37ProjJ) :
    E37ProjU K b.down ⟶ Spec (CommRingCat.of K) :=
  match b.down with
  | false => S2801E37StructureMap K
  | true => E37ChartYStructureMap K

theorem psi_algebraMap_K (a : K) :
    psi K (algebraMap K (A1 K) a) = algebraMap K (A0 K) a := by
  have h := RingHom.congr_fun (psi_comp_alphaPoly K) (MvPolynomial.C a)
  simpa [alphaPoly, gammaPoly, MvPolynomial.eval₂Hom_C] using h

theorem phi_algebraMap_K (a : K) :
    phi K (algebraMap K (A0 K) a) = algebraMap K (A1 K) a := by
  have h := RingHom.congr_fun (phi_comp_betaPoly K) (MvPolynomial.C a)
  simpa [betaPoly, deltaPoly, MvPolynomial.eval₂Hom_C] using h

/-- Structure morphism of the fixed E37 projective scheme over Spec K. -/
noncomputable def S2821StructureMap :
    S2820E37ProjectiveScheme K ⟶ Spec (CommRingCat.of K) := by
  classical
  let D := E37ProjGlueData K (S2820E37TransitionIso K)
  haveI : HasMulticoequalizer D.toGlueData.diagram :=
    Scheme.GlueData.instHasMulticoequalizerDiagram D
  refine Multicoequalizer.desc D.toGlueData.diagram (Spec (CommRingCat.of K))
    (S2821ChartStructure K) ?_
  rintro ⟨i, j⟩
  change D.toGlueData.f i j ≫ S2821ChartStructure K i =
    (D.toGlueData.t i j ≫ D.toGlueData.f j i) ≫ S2821ChartStructure K j
  cases i with
  | up i => cases j with
    | up j =>
      cases i <;> cases j <;>
        simp [D, E37ProjGlueData, E37ProjF, E37ProjT, E37ProjU, S2821ChartStructure,
          S2820E37TransitionIso, E37ChartZOverlapMap, E37ChartYOverlapMap,
          S2801E37StructureMap, E37ChartYStructureMap]
      · -- false, true
        rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
        congr 1
        ext a
        change (algebraMap (S2801E37CoordinateRing K) (E37ChartZOverlapRing K))
            ((algebraMap K (S2801E37CoordinateRing K)) a) =
          psi K ((algebraMap (E37ChartYRing K) (E37ChartYOverlapRing K))
            ((algebraMap K (E37ChartYRing K)) a))
        rw [← IsScalarTower.algebraMap_apply K (S2801E37CoordinateRing K) (E37ChartZOverlapRing K) a,
          ← IsScalarTower.algebraMap_apply K (E37ChartYRing K) (E37ChartYOverlapRing K) a,
          psi_algebraMap_K K]
      · -- true, false
        rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
        congr 1
        ext a
        change (algebraMap (E37ChartYRing K) (E37ChartYOverlapRing K))
            ((algebraMap K (E37ChartYRing K)) a) =
          phi K ((algebraMap (S2801E37CoordinateRing K) (E37ChartZOverlapRing K))
            ((algebraMap K (S2801E37CoordinateRing K)) a))
        rw [← IsScalarTower.algebraMap_apply K (S2801E37CoordinateRing K) (E37ChartZOverlapRing K) a,
          ← IsScalarTower.algebraMap_apply K (E37ChartYRing K) (E37ChartYOverlapRing K) a,
          phi_algebraMap_K K]

/-- The fixed E37 projective scheme as an object over Spec K. -/
noncomputable abbrev S2821AsOver : Over (Spec (CommRingCat.of K)) :=
  Over.mk (S2821StructureMap K)

/-- The chart-Z open immersion as an Over morphism. -/
theorem S2821ChartZ_structure :
    S2820E37ChartZMap K ≫ S2821StructureMap K = S2801E37StructureMap K := by
  classical
  let D := E37ProjGlueData K (S2820E37TransitionIso K)
  haveI : HasMulticoequalizer D.toGlueData.diagram :=
    Scheme.GlueData.instHasMulticoequalizerDiagram D
  exact Multicoequalizer.π_desc D.toGlueData.diagram (Spec (CommRingCat.of K))
    (S2821ChartStructure K) _ (ULift.up false)

/-- The chart-Y open immersion as an Over morphism. -/
theorem S2821ChartY_structure :
    S2820E37ChartYMap K ≫ S2821StructureMap K = E37ChartYStructureMap K := by
  classical
  let D := E37ProjGlueData K (S2820E37TransitionIso K)
  haveI : HasMulticoequalizer D.toGlueData.diagram :=
    Scheme.GlueData.instHasMulticoequalizerDiagram D
  exact Multicoequalizer.π_desc D.toGlueData.diagram (Spec (CommRingCat.of K))
    (S2821ChartStructure K) _ (ULift.up true)

noncomputable def S2821ChartZOver :
    Over.mk (S2801E37StructureMap K) ⟶ S2821AsOver K :=
  Over.homMk (S2820E37ChartZMap K) (S2821ChartZ_structure K)

noncomputable def S2821ChartYOver :
    Over.mk (E37ChartYStructureMap K) ⟶ S2821AsOver K :=
  Over.homMk (S2820E37ChartYMap K) (S2821ChartY_structure K)

#check S2821ChartZOver
#check S2821ChartYOver
#print axioms S2821AsOver
#print axioms S2821ChartZOver

end LeanFormal.IUT.XiFPaper.S2821E37ProjectiveOverActual
end
