/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import Mathlib.MeasureTheory.Group.Measure

/-! # A667 hull: product Haar is NULL on singletons (B1 blocker)

The local root-extension Haar measure is `Measure.addHaar` on a finite-dimensional
torsion-free normed `ℚ_p`-vector space; its punctured neighbourhoods at `0` are
nontrivial, hence `NullSingletonClass` holds: `μ_b {x} = 0`.  Therefore the finite
product Haar `rootExtensionProductHaar T = Measure.pi (rootExtensionHaar T ·)` is
zero on every singleton, and consequently on every image of a singleton under any
map (in particular `badInvScale`).

This is the measure-theoretic blocker B1: `s1902LogVolume`/`rootExtensionProductHaar`
assigns zero mass to points, so point-supported regions cannot witness positive
volume.  No canonical object changed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ProductHaarSingletonActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open MeasureTheory
open scoped Pointwise ENNReal BigOperators Topology

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [Nonempty (Bad (nativePlaceSelection T))]

/-- Local root-extension Haar is null on singletons. -/
theorem localHaar_singleton_zero (b : Bad (nativePlaceSelection T))
    (x : rootNormedExtension T b) :
    rootExtensionHaar T b ({x} : Set (rootNormedExtension T b)) = 0 := by
  haveI : Module.IsTorsionFree ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) :=
    (Module.finBasis ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)).isTorsionFree
  haveI : Filter.NeBot (𝓝[≠] (0 : rootNormedExtension T b)) :=
    NormedField.nhdsNE_neBot (0 : rootNormedExtension T b)
  haveI : NullSingletonClass (rootExtensionHaar T b) := by
    rw [show rootExtensionHaar T b = (Measure.addHaar : Measure (rootNormedExtension T b)) from rfl]
    exact MeasureTheory.Measure.IsAddHaarMeasure.nullSingletonClass _
  exact MeasureTheory.NullSingletonClass.measure_singleton x

/-- Singleton in the product carrier as a product of singletons. -/
theorem singleton_eq_pi (x : RootExtensionProductCarrier T) :
    ({x} : Set (RootExtensionProductCarrier T)) =
      Set.pi Set.univ (fun b => ({x b} : Set (rootNormedExtension T b))) := by
  ext y
  simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, forall_true_left,
    Set.mem_singleton_iff]
  constructor
  · intro h b
    rw [h]
  · intro h
    funext b
    exact h b

/-- **Product Haar is null on singletons** (B1). -/
theorem productHaar_singleton_zero (x : RootExtensionProductCarrier T) :
    rootExtensionProductHaar T ({x} : Set (RootExtensionProductCarrier T)) = 0 := by
  classical
  obtain ⟨b⟩ := (inferInstance : Nonempty (Bad (nativePlaceSelection T)))
  rw [singleton_eq_pi T x, rootExtensionProductHaar, Measure.pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ b)
    (localHaar_singleton_zero T b (x b))

/-- Any image of a singleton under a map is null for the product Haar. -/
theorem productHaar_image_singleton_zero (f : RootExtensionProductCarrier T →
    RootExtensionProductCarrier T) (x : RootExtensionProductCarrier T) :
    rootExtensionProductHaar T (f '' ({x} : Set (RootExtensionProductCarrier T))) = 0 := by
  rw [Set.image_singleton]
  exact productHaar_singleton_zero T (f x)

def b1Rows : List (String × String × String) :=
  [ ("local additive Haar singleton", "localHaar_singleton_zero", "PROVED (NullSingletonClass)"),
    ("product Haar singleton", "productHaar_singleton_zero", "PROVED (pi_pi + nonempty index)"),
    ("image singleton (badInvScale)", "productHaar_image_singleton_zero", "PROVED"),
    ("scope", "B1 blocker; point-supported regions have zero volume", "INTEGRITY") ]

theorem b1Rows_length : b1Rows.length = 4 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1ProductHaarSingletonActual.localHaar_singleton_zero
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ProductHaarSingletonActual.productHaar_singleton_zero
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ProductHaarSingletonActual.productHaar_image_singleton_zero

end LeanFormal.IUT.XiFPaper.Mzk1ProductHaarSingletonActual

end