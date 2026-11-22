import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientTransitionConstruct
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientTransitionCocycleConstruct
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Equivariance of the chart-overlap tensor reassociation

This file proves the actual pointwise equivariance of the tensor reassociation
`Away(t_i t_j) ⊗_{Away(t_i)} (Away(t_i) ⊗_R A) ≃ Away(t_i t_j) ⊗_R A`
with respect to the diagonal action of `G`.  The proof is by tensor induction
and uses the explicit `cancelBaseChange_tmul` computation.  The resulting
equivariance closes the `hchart`/`hoverlap` parameters of
`GlobalQuotientTransitionConstruct`.
-/
namespace ABCBridge.GlobalQuotientTransitionEquivariance

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open ABCBridge.SplitCaseFixedPointsTransport
open ABCBridge.GlobalQuotientTransitionData
open ABCBridge.GlobalQuotientCocycle
open ABCBridge.GlobalQuotientTransitionConstruct

universe u

variable {R : Type u} [CommRing R] {A G : Type u} [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [DecidableEq G] [MulSemiringAction G A] [SMulCommClass G R A]
  [Algebra.Etale R A] [Module.Finite R A]
  {ι : Type u} [Fintype ι] [DecidableEq ι]
  (t : ι → R)

/-- The diagonal action on `Away(t_i t_j) ⊗_{Away(t_i)} (Away(t_i) ⊗_R A)`:
the new base factor is fixed and the second tensor factor is acted on through
the action on `A`. -/
noncomputable def chartOverlapSourceAction (i j : ι) (g : G) :
    TensorProduct (baseLocal t i) (baseOverlap t i j) (algLocal (A := A) t i) ≃ₐ[baseLocal t i]
      TensorProduct (baseLocal t i) (baseOverlap t i j) (algLocal (A := A) t i) :=
  Algebra.TensorProduct.congr
    (AlgEquiv.refl : baseOverlap t i j ≃ₐ[baseLocal t i] baseOverlap t i j)
    (localTensorActionAlgEquiv (A := A) (G := G) t i g)

/-- The action on the overlap algebra `Away(t_i t_j) ⊗_R A`: the new base is
fixed and `A` is acted on. -/
noncomputable def overlapTensorAction (i j : ι) (g : G) :
    algOverlap (A := A) t i j ≃ₐ[baseOverlap t i j] algOverlap (A := A) t i j :=
  Algebra.TensorProduct.congr
    (AlgEquiv.refl : baseOverlap t i j ≃ₐ[baseOverlap t i j] baseOverlap t i j)
    (MulSemiringAction.toAlgEquiv R A g)

@[simp] theorem chartOverlapSourceAction_tmul (i j : ι) (g : G)
    (m : baseOverlap t i j) (y : algLocal (A := A) t i) :
    chartOverlapSourceAction (A := A) (G := G) t i j g (m ⊗ₜ[baseLocal t i] y) =
      m ⊗ₜ[baseLocal t i] (localTensorActionAlgEquiv (A := A) (G := G) t i g y) := by
  simp [chartOverlapSourceAction, Algebra.TensorProduct.congr]

@[simp] theorem localTensorActionAlgEquiv_tmul (i : ι) (g : G)
    (s : baseLocal t i) (a : A) :
    localTensorActionAlgEquiv (A := A) (G := G) t i g (s ⊗ₜ[R] a) =
      s ⊗ₜ[R] (g • a) := by
  simp [localTensorActionAlgEquiv, Algebra.TensorProduct.congr,
    MulSemiringAction.toAlgEquiv]

@[simp] theorem overlapTensorAction_tmul (i j : ι) (g : G)
    (m : baseOverlap t i j) (a : A) :
    overlapTensorAction (A := A) (G := G) t i j g (m ⊗ₜ[R] a) =
      m ⊗ₜ[R] (g • a) := by
  simp [overlapTensorAction, Algebra.TensorProduct.congr,
    MulSemiringAction.toAlgEquiv]

/-- Pointwise equivariance of the tensor reassociation for the diagonal action. -/
theorem chartOverlapTensorReassoc_equivariant (i j : ι) (g : G)
    (x : TensorProduct (baseLocal t i) (baseOverlap t i j) (algLocal (A := A) t i)) :
    chartOverlapTensorReassoc (A := A) (G := G) t i j
        (chartOverlapSourceAction (A := A) (G := G) t i j g x) =
      overlapTensorAction (A := A) (G := G) t i j g
        (chartOverlapTensorReassoc (A := A) (G := G) t i j x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul s a =>
          simp [chartOverlapTensorReassoc,
            TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
      | add y z hy hz =>
          simp [hy, hz]
  | add x y hx hy =>
      simp [hx, hy]

/-- Pointwise equivariance of the `j`-chart tensor reassociation. -/
theorem overlapTensorReassoc_equivariant (i j : ι) (g : G)
    (x : TensorProduct (baseLocal t j) (baseOverlap t i j) (algLocal (A := A) t j)) :
    overlapTensorReassoc (A := A) (G := G) t i j
        (chartOverlapSourceAction (A := A) (G := G) t j i g x) =
      overlapTensorAction (A := A) (G := G) t i j g
        (overlapTensorReassoc (A := A) (G := G) t i j x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul s a =>
          simp [overlapTensorReassoc,
            TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
      | add y z hy hz =>
          simp [hy, hz]
  | add x y hx hy =>
      simp [hx, hy]

/-- The equivariance statement in the exact form consumed by
`chartOverlapFixedEquiv`; the action is the diagonal source action. -/
theorem chartOverlapFixedEquiv_hchart (i j : ι) (g : G)
    (x : TensorProduct (baseLocal t i) (baseOverlap t i j) (algLocal (A := A) t i)) :
    chartOverlapTensorReassoc (A := A) (G := G) t i j
        (chartOverlapSourceAction (A := A) (G := G) t i j g x) =
      overlapTensorAction (A := A) (G := G) t i j g
        (chartOverlapTensorReassoc (A := A) (G := G) t i j x) :=
  chartOverlapTensorReassoc_equivariant (A := A) (G := G) t i j g x

/-- The `j`-chart equivariance statement. -/
theorem overlapTensorReassoc_hoverlap (i j : ι) (g : G)
    (x : TensorProduct (baseLocal t j) (baseOverlap t i j) (algLocal (A := A) t j)) :
    overlapTensorReassoc (A := A) (G := G) t i j
        (chartOverlapSourceAction (A := A) (G := G) t j i g x) =
      overlapTensorAction (A := A) (G := G) t i j g
        (overlapTensorReassoc (A := A) (G := G) t i j x) :=
  overlapTensorReassoc_equivariant (A := A) (G := G) t i j g x


section ClosedParameters

/-- The source action as a ring equivalence. -/
noncomputable def chartOverlapSourceRingEquiv (i j : ι) (g : G) :
    TensorProduct (baseLocal t i) (baseOverlap t i j) (algLocal (A := A) t i) ≃+*
      TensorProduct (baseLocal t i) (baseOverlap t i j) (algLocal (A := A) t i) :=
  (chartOverlapSourceAction (A := A) (G := G) t i j g).toRingEquiv

theorem chartOverlapSourceRingEquiv_one (i j : ι) :
    chartOverlapSourceRingEquiv (A := A) (G := G) t i j (1 : G) = RingEquiv.refl _ := by
  apply RingEquiv.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul s a => simp [chartOverlapSourceRingEquiv, chartOverlapSourceAction]
      | add y z hy hz => simp [hy, hz]
  | add x y hx hy => simp [hx, hy]

theorem chartOverlapSourceRingEquiv_mul (i j : ι) (g h : G) :
    chartOverlapSourceRingEquiv (A := A) (G := G) t i j (g * h) =
      (chartOverlapSourceRingEquiv (A := A) (G := G) t i j g).trans
        (chartOverlapSourceRingEquiv (A := A) (G := G) t i j h) := by
  apply RingEquiv.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul s a => simp [chartOverlapSourceRingEquiv, chartOverlapSourceAction]
      | add y z hy hz => simp [hy, hz]
  | add x y hx hy => simp [hx, hy]

/-- The diagonal `G`-action on the source tensor algebra, packaged as a
`MulSemiringAction`. -/
noncomputable instance chartOverlapSourceMulSemiringAction (i j : ι) :
    MulSemiringAction G
      (TensorProduct (baseLocal t i) (baseOverlap t i j) (algLocal (A := A) t i)) := by
  let φ : G →* (TensorProduct (baseLocal t i) (baseOverlap t i j) (algLocal (A := A) t i) ≃+*
      TensorProduct (baseLocal t i) (baseOverlap t i j) (algLocal (A := A) t i)) :=
    { toFun := fun g => chartOverlapSourceRingEquiv (A := A) (G := G) t i j g
      map_one' := chartOverlapSourceRingEquiv_one (A := A) (G := G) t i j
      map_mul' := chartOverlapSourceRingEquiv_mul (A := A) (G := G) t i j }
  exact MulSemiringAction.compHom
    (TensorProduct (baseLocal t i) (baseOverlap t i j) (algLocal (A := A) t i)) φ

/-- Closed `hchart`: the tensor reassociation is equivariant for the packaged
diagonal action. -/
theorem chartOverlapTensorReassoc_equivariance_closed (i j : ι) :
    ∀ (g : G)
      (x : TensorProduct (baseLocal t i) (baseOverlap t i j) (algLocal (A := A) t i)),
      chartOverlapTensorReassoc (A := A) (G := G) t i j (g • x) =
        g • chartOverlapTensorReassoc (A := A) (G := G) t i j x := by
  intro g x
  change chartOverlapTensorReassoc (A := A) (G := G) t i j
      (chartOverlapSourceAction (A := A) (G := G) t i j g x) =
    overlapTensorAction (A := A) (G := G) t i j g
      (chartOverlapTensorReassoc (A := A) (G := G) t i j x)
  exact chartOverlapTensorReassoc_equivariant (A := A) (G := G) t i j g x

/-- Closed `hoverlap`: the second tensor reassociation is equivariant for the
packaged diagonal action. -/
theorem overlapTensorReassoc_equivariance_closed (i j : ι) :
    ∀ (g : G)
      (x : TensorProduct (baseLocal t j) (baseOverlap t i j) (algLocal (A := A) t j)),
      overlapTensorReassoc (A := A) (G := G) t i j (g • x) =
        g • overlapTensorReassoc (A := A) (G := G) t i j x := by
  intro g x
  change overlapTensorReassoc (A := A) (G := G) t i j
      (chartOverlapSourceAction (A := A) (G := G) t j i g x) =
    overlapTensorAction (A := A) (G := G) t i j g
      (overlapTensorReassoc (A := A) (G := G) t i j x)
  exact overlapTensorReassoc_equivariant (A := A) (G := G) t i j g x

/-- The fixed-point reassociation with the equivariance parameter closed. -/
noncomputable def chartFixedPointReassociationClosed :
    ChartFixedPointReassociation (A := A) (G := G) t :=
  chartFixedPointReassociation (A := A) (G := G) t
    (fun i j => chartOverlapTensorReassoc_equivariance_closed (A := A) (G := G) t i j)
    (fun i j => overlapTensorReassoc_equivariance_closed (A := A) (G := G) t i j)

/-- The cocycle input with the equivariance parameters closed.  The cocycle
proof remains the naturality proof of the previous file. -/
noncomputable def chartOverlapTransitionInputClosed :
    ChartOverlapTransitionInput (A := A) (G := G) t :=
  chartOverlapTransitionInputConstruct (A := A) (G := G) t
    (fun i j => chartOverlapTensorReassoc_equivariance_closed (A := A) (G := G) t i j)
    (fun i j => overlapTensorReassoc_equivariance_closed (A := A) (G := G) t i j)

end ClosedParameters

end ABCBridge.GlobalQuotientTransitionEquivariance
