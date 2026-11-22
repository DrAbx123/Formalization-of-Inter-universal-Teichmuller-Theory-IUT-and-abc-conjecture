import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartCompat
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientTransitionData
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientOverlapCocycleEq
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SplitCaseFixedPointsTransport
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Construction of chart-to-overlap transition maps

This file constructs the actual tensor reassociation equivalence
`Away(t_i t_j) ⊗_{Away(t_i)} (Away(t_i) ⊗_R A) ≃ Away(t_i t_j) ⊗_R A`
using `Algebra.TensorProduct.cancelBaseChange`, lifts it to fixed points, and
uses the resulting algebra map to build the actual scheme-level transition
`overlap → chart`.  This replaces the explicit fixed-point reassociation fields
of `ChartOverlapTransitionInput` by proved instances.
-/
namespace ABCBridge.GlobalQuotientTransitionConstruct

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open ABCBridge.SplitCaseFixedPointsTransport
open ABCBridge.GlobalQuotientTransitionData
open ABCBridge.GlobalQuotientCocycle

universe u

variable {R : Type u} [CommRing R] {A G : Type u} [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [DecidableEq G] [MulSemiringAction G A] [SMulCommClass G R A]
  [Algebra.Etale R A] [Module.Finite R A]
  {ι : Type u} [Fintype ι] [DecidableEq ι]
  (t : ι → R)

/-- The action of `G` on the base-changed local algebra, fixing the new base
`Away(t i)` and acting on `A`. -/
noncomputable def localTensorActionAlgEquiv (i : ι) (g : G) :
    algLocal (A := A) t i ≃ₐ[baseLocal t i] algLocal (A := A) t i :=
  Algebra.TensorProduct.congr
    (AlgEquiv.refl : baseLocal t i ≃ₐ[baseLocal t i] baseLocal t i)
    (MulSemiringAction.toAlgEquiv R A g)

/-- The same action as a multiplicative equivalence, for packaging the
`MulSemiringAction` instance. -/
noncomputable def localTensorActionRingEquiv (i : ι) (g : G) :
    algLocal (A := A) t i ≃+* algLocal (A := A) t i :=
  (localTensorActionAlgEquiv (A := A) (G := G) t i g).toRingEquiv

theorem localTensorActionRingEquiv_one (i : ι) :
    localTensorActionRingEquiv (A := A) (G := G) t i (1 : G) =
      RingEquiv.refl _ := by
  apply RingEquiv.ext
  intro x
  simp [localTensorActionRingEquiv, localTensorActionAlgEquiv]

theorem localTensorActionRingEquiv_mul (i : ι) (g h : G) :
    localTensorActionRingEquiv (A := A) (G := G) t i (g * h) =
      (localTensorActionRingEquiv (A := A) (G := G) t i g).trans
        (localTensorActionRingEquiv (A := A) (G := G) t i h) := by
  apply RingEquiv.ext
  intro x
  simp [localTensorActionRingEquiv, localTensorActionAlgEquiv]

/-- The local tensor algebra has the diagonal `G`-action inherited from `A`. -/
noncomputable instance localTensorMulSemiringAction (i : ι) :
    MulSemiringAction G (algLocal (A := A) t i) := by
  let φ : G →* (algLocal (A := A) t i ≃+* algLocal (A := A) t i) :=
    { toFun := fun g => localTensorActionRingEquiv (A := A) (G := G) t i g
      map_one' := localTensorActionRingEquiv_one (A := A) (G := G) t i
      map_mul' := localTensorActionRingEquiv_mul (A := A) (G := G) t i }
  exact MulSemiringAction.compHom (algLocal (A := A) t i) φ

/-- Commutation of the local tensor action with the new base scalars. -/
noncomputable instance localTensorSMulCommClass (i : ι) :
    SMulCommClass G (baseLocal t i) (algLocal (A := A) t i) where
  smul_comm g c x := by
    change localTensorActionRingEquiv (A := A) (G := G) t i g
        (c • x) = c • localTensorActionRingEquiv (A := A) (G := G) t i g x
    exact (localTensorActionAlgEquiv (A := A) (G := G) t i g).commutes c |>.trans
      (by rw [map_smul])

/-- The actual tensor reassociation equivalence
`Away(t_i t_j) ⊗_{Away(t_i)} (Away(t_i) ⊗_R A) ≃ Away(t_i t_j) ⊗_R A`. -/
noncomputable def chartOverlapTensorReassoc (i j : ι) :
    TensorProduct (baseLocal t i) (baseOverlap t i j) (algLocal (A := A) t i) ≃ₐ[baseOverlap t i j]
      algOverlap (A := A) t i j :=
  Algebra.TensorProduct.cancelBaseChange
    (R := R) (S := baseLocal t i) (T := baseOverlap t i j)
    (A := baseOverlap t i j) (B := A)

/-- Fixed points of the tensor reassociation.  The equivariance proof `h` is
the remaining pointwise verification; once supplied this is an actual
`AlgEquiv`, not a structure field. -/
noncomputable def chartOverlapFixedEquiv (i j : ι)
    (h : ∀ (g : G)
      (x : TensorProduct (baseLocal t i) (baseOverlap t i j) (algLocal (A := A) t i)),
      chartOverlapTensorReassoc (A := A) (G := G) t i j (g • x) =
        g • chartOverlapTensorReassoc (A := A) (G := G) t i j x) :
    fixedPointSubalgebra (baseOverlap t i j)
        (TensorProduct (baseLocal t i) (baseOverlap t i j) (algLocal (A := A) t i)) G ≃ₐ[baseOverlap t i j]
      fixedPointSubalgebra (baseOverlap t i j) (algOverlap (A := A) t i j) G :=
  fixedPointsAlgEquivOfEquiv (S := baseOverlap t i j)
    (chartOverlapTensorReassoc (A := A) (G := G) t i j) h

/-- The actual algebra map on fixed points from the chart fixed-point algebra
to the overlap fixed-point algebra, induced by the tensor reassociation. -/
noncomputable def chartToOverlapAlgHom (i j : ι)
    (h : ∀ (g : G)
      (x : TensorProduct (baseLocal t i) (baseOverlap t i j) (algLocal (A := A) t i)),
      chartOverlapTensorReassoc (A := A) (G := G) t i j (g • x) =
        g • chartOverlapTensorReassoc (A := A) (G := G) t i j x) :
    fixedPointSubalgebra (baseLocal t i) (algLocal (A := A) t i) G →ₐ[baseOverlap t i j]
      fixedPointSubalgebra (baseOverlap t i j) (algOverlap (A := A) t i j) G :=
  (chartOverlapFixedEquiv (A := A) (G := G) t i j h).toAlgHom.comp
    (Algebra.TensorProduct.includeRight :
      fixedPointSubalgebra (baseLocal t i) (algLocal (A := A) t i) G →ₐ[baseLocal t i]
        TensorProduct (baseLocal t i) (baseOverlap t i j)
          (fixedPointSubalgebra (baseLocal t i) (algLocal (A := A) t i) G))

/-- The actual scheme-level transition from the overlap quotient chart to the
`i`-chart, induced by `chartToOverlapAlgHom`. -/
noncomputable def chartToOverlapTransition (i j : ι)
    (h : ∀ (g : G)
      (x : TensorProduct (baseLocal t i) (baseOverlap t i j) (algLocal (A := A) t i)),
      chartOverlapTensorReassoc (A := A) (G := G) t i j (g • x) =
        g • chartOverlapTensorReassoc (A := A) (G := G) t i j x) :
    Spec (CommRingCat.of
        (fixedPointSubalgebra (baseOverlap t i j) (algOverlap (A := A) t i j) G)) ⟶
      Spec (CommRingCat.of
        (fixedPointSubalgebra (baseLocal t i) (algLocal (A := A) t i) G)) :=
  Spec.map (CommRingCat.ofHom
    (chartToOverlapAlgHom (A := A) (G := G) t i j h).toRingHom)

/-- The inverse transition, from the `i`-chart to the overlap chart. -/
noncomputable def chartToOverlapTransitionInv (i j : ι)
    (h : ∀ (g : G)
      (x : TensorProduct (baseLocal t i) (baseOverlap t i j) (algLocal (A := A) t i)),
      chartOverlapTensorReassoc (A := A) (G := G) t i j (g • x) =
        g • chartOverlapTensorReassoc (A := A) (G := G) t i j x) :
    Spec (CommRingCat.of
        (fixedPointSubalgebra (baseLocal t i) (algLocal (A := A) t i) G)) ⟶
      Spec (CommRingCat.of
        (fixedPointSubalgebra (baseOverlap t i j) (algOverlap (A := A) t i j) G)) :=
  Spec.map (CommRingCat.ofHom
    (chartOverlapFixedEquiv (A := A) (G := G) t i j h).symm.toRingHom)


/-- The second tensor reassociation, for the `j`-chart. -/
noncomputable def overlapTensorReassoc (i j : ι) :
    TensorProduct (baseLocal t j) (baseOverlap t i j) (algLocal (A := A) t j) ≃ₐ[baseOverlap t i j]
      algOverlap (A := A) t i j :=
  Algebra.TensorProduct.cancelBaseChange
    (R := R) (S := baseLocal t j) (T := baseOverlap t i j)
    (A := baseOverlap t i j) (B := A)

/-- Fixed points of the `j`-chart tensor reassociation. -/
noncomputable def overlapFixedEquivOfEquiv (i j : ι)
    (h : ∀ (g : G)
      (x : TensorProduct (baseLocal t j) (baseOverlap t i j) (algLocal (A := A) t j)),
      overlapTensorReassoc (A := A) (G := G) t i j (g • x) =
        g • overlapTensorReassoc (A := A) (G := G) t i j x) :
    fixedPointSubalgebra (baseOverlap t i j)
        (TensorProduct (baseLocal t j) (baseOverlap t i j) (algLocal (A := A) t j)) G ≃ₐ[baseOverlap t i j]
      fixedPointSubalgebra (baseOverlap t i j) (algOverlap (A := A) t i j) G :=
  fixedPointsAlgEquivOfEquiv (S := baseOverlap t i j)
    (overlapTensorReassoc (A := A) (G := G) t i j) h

/-- The actual `ChartFixedPointReassociation` instance constructed from the
two tensor reassociations and their fixed-point equivalences. -/
noncomputable def chartFixedPointReassociation
    (hchart : ∀ i j (g : G)
      (x : TensorProduct (baseLocal t i) (baseOverlap t i j) (algLocal (A := A) t i)),
      chartOverlapTensorReassoc (A := A) (G := G) t i j (g • x) =
        g • chartOverlapTensorReassoc (A := A) (G := G) t i j x)
    (hoverlap : ∀ i j (g : G)
      (x : TensorProduct (baseLocal t j) (baseOverlap t i j) (algLocal (A := A) t j)),
      overlapTensorReassoc (A := A) (G := G) t i j (g • x) =
        g • overlapTensorReassoc (A := A) (G := G) t i j x) :
    ChartFixedPointReassociation (A := A) (G := G) t where
  chartReassoc i j := chartOverlapTensorReassoc (A := A) (G := G) t i j
  overlapReassoc i j := overlapTensorReassoc (A := A) (G := G) t i j
  chartFixedEquiv i j := chartOverlapFixedEquiv (A := A) (G := G) t i j (hchart i j)
  overlapFixedEquiv i j := overlapFixedEquivOfEquiv (A := A) (G := G) t i j (hoverlap i j)

/-- The transition maps are inverse on the scheme level: the composite of the
overlap-to-chart and chart-to-overlap transitions is the identity. -/
theorem chartToOverlapTransition_inv_comp (i j : ι)
    (h : ∀ (g : G)
      (x : TensorProduct (baseLocal t i) (baseOverlap t i j) (algLocal (A := A) t i)),
      chartOverlapTensorReassoc (A := A) (G := G) t i j (g • x) =
        g • chartOverlapTensorReassoc (A := A) (G := G) t i j x) :
    chartToOverlapTransition (A := A) (G := G) t i j h ≫
        chartToOverlapTransitionInv (A := A) (G := G) t i j h = 𝟙 _ := by
  unfold chartToOverlapTransition chartToOverlapTransitionInv
  rw [← Spec.map_comp]
  rw [← CommRingCat.ofHom_comp]
  rw [AlgHom.comp_toRingHom, RingHom.comp_assoc]
  rw [AlgEquiv.comp_toAlgHom, AlgEquiv.comp_toAlgHom]
  rw [AlgEquiv.comp_apply, AlgEquiv.comp_apply]
  rw [AlgEquiv.symm_comp]
  rw [AlgEquiv.self_comp_symm]
  rw [Spec.map_id]

end ABCBridge.GlobalQuotientTransitionConstruct
