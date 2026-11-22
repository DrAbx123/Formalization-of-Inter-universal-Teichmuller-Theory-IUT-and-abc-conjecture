import tmp.sheaf.xif.paper.S3135LogShellScalarSelfSimilarityActual
import tmp.sheaf.xif.paper.S3135PaperLambdaWiringActual
import tmp.sheaf.xif.paper.S3129IQHullLogVolumeSourceActual

/-!
# task-72 skeleton interface (parameterized): model hull point / Haar / unit-region data

**Model-construction interface, not a paper object.**  This is the parameterized
skeleton approved by the Lead: it compiles standalone over an arbitrary frozen
`I : OriginalInput l V`, and plugs into qpilot's `modelOriginalInput` once its
content lands (clauses/theta packet/theater).

Frozen names (qpilot export list):
* `S3135ModelHullPoint : Type := concreteLogShellField` (the actual concrete
  completion, NOT a model-local completion);
* `S3135ModelHullHaar : Measure S3135ModelHullPoint := sourceHullHaar` (the actual
  additive Haar on the actual completion; no custom measure);
* `structure S3135ModelUnitRegionHaarData` with the pair-record scaling:
  `valueUnit` (value-monoid unit), `baseUnit : Q_[5]^x` with norm one,
  `unitRegion`, `degreeBound`, `hull`/`hull_subset`, the model log-degree
  function and its bounds, and the completion scaling point;
* `S3135ModelHaar_scaling_image_eq`: for a `Z_5`-unit scalar pair `z, z'`
  (`z * z' = 1`), the actual Haar mass of the scaled integral log-shell equals that
  of the integral log-shell — proved from the citable
  `s3135_integralLogShell_scalarUnit_selfSimilarity` by set equality (this is the
  nontrivial procession-scaling instance; `z = 2`, `z' = 1/2`).
-/

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Measure
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual
open LeanFormal.IUT.XiFPaper.S3135LogShellScalarSelfSimilarityActual
open LeanFormal.IUT.XiFPaper.S3135PaperLambdaWiringActual

namespace LeanFormal.IUT.XiFPaper.S3135ModelSkeletonInterfaceActual

local instance measCSF14 : MeasurableSpace concreteLogShellField := borel _
local instance borelCSF14 : BorelSpace concreteLogShellField := ⟨rfl⟩

/-- Frozen model hull point: the actual concrete completion. -/
abbrev S3135ModelHullPoint : Type := concreteLogShellField

/-- Frozen model hull Haar: the actual additive Haar on the actual completion. -/
noncomputable def S3135ModelHullHaar : Measure S3135ModelHullPoint :=
  sourceHullHaar

/-- **Parameterized model unit-region/Haar data** (pair-record scaling).  Over any
frozen `I : OriginalInput l V`; qpilot's `modelOriginalInput` instantiates it. -/
structure S3135ModelUnitRegionHaarData
    {l : PrimeGeFive} {V : Type} (I : OriginalInput l V) (v : V) : Type where
  /-- Value-side unit of the scaling. -/
  valueUnit : (I.ValueMonoidAt 0 0 v)ˣ
  /-- Completion-side (base-field) unit of the scaling. -/
  baseUnit : ℚ_[concreteRationalPrime]ˣ
  /-- The completion-side unit has norm one (so it preserves the log-shell). -/
  baseUnit_norm_one : ‖(baseUnit : ℚ_[concreteRationalPrime])‖ = 1
  /-- The model hull (transported into the completion by the model construction). -/
  hull : Set S3135ModelHullPoint
  /-- The unit region of the model. -/
  unitRegion : Set S3135ModelHullPoint
  /-- The unit region is the actual integral log-shell. -/
  unitRegion_eq_logShell : unitRegion =
    ((integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime)) :
      Set S3135ModelHullPoint)
  /-- Model log-degree function on the hull point type. -/
  modelLogDegree : S3135ModelHullPoint → ℝ
  /-- Log-degree bound on the unit region. -/
  degreeBound : ℝ
  /-- The hull is contained in the unit region. -/
  hull_subset : hull ⊆ unitRegion
  /-- Every unit-region point has log-degree at most the bound. -/
  unitRegion_logDegree_le :
    ∀ y ∈ unitRegion, modelLogDegree y ≤ degreeBound
  /-- The completion scaling point of the scaling. -/
  scalingPoint : S3135ModelHullPoint
  /-- The completion scaling is the base unit scalar action on the unit. -/
  scalingPoint_eq : scalingPoint =
    algebraMap ℚ_[concreteRationalPrime] S3135ModelHullPoint (baseUnit : ℚ_[concreteRationalPrime]) *
      (1 : S3135ModelHullPoint)
  /-- The scaling has nonpositive log-degree (value-unit side). -/
  scaling_logDegree_nonpos : modelLogDegree scalingPoint ≤ 0

/-- **FROZEN μ-equality target**: for a `Z_5`-unit scalar pair `z, z'` with
`z * z' = 1`, the actual Haar mass of the scaled integral log-shell equals that of
the integral log-shell — the nontrivial procession-scaling instance
(`z = 2`, `z' = 1/2`).  Proved by set equality via the citable
`s3135_integralLogShell_scalarUnit_selfSimilarity`. -/
theorem S3135ModelHaar_scaling_image_eq
    (z z' : ℤ_[concreteRationalPrime]) (h : z * z' = 1) :
    S3135ModelHullHaar
        ((fun x : S3135ModelHullPoint =>
            algebraMap ℚ_[concreteRationalPrime] S3135ModelHullPoint
              (z : ℚ_[concreteRationalPrime]) * x) ''
          ((integralLogShell (K := concreteLogShellField)
            (p := concreteRationalPrime)) : Set S3135ModelHullPoint)) =
      S3135ModelHullHaar
        ((integralLogShell (K := concreteLogShellField)
          (p := concreteRationalPrime)) : Set S3135ModelHullPoint) := by
  have hset :
      (fun x : S3135ModelHullPoint =>
          algebraMap ℚ_[concreteRationalPrime] S3135ModelHullPoint
            (z : ℚ_[concreteRationalPrime]) * x) ''
        ((integralLogShell (K := concreteLogShellField)
          (p := concreteRationalPrime)) : Set S3135ModelHullPoint) =
      ((integralLogShell (K := concreteLogShellField)
        (p := concreteRationalPrime)) : Set S3135ModelHullPoint) :=
    s3135_integralLogShell_scalarUnit_selfSimilarity (K := concreteLogShellField)
      (p := concreteRationalPrime) z z' h
  rw [hset]

#check S3135ModelHullPoint
#check S3135ModelHullHaar
#check S3135ModelUnitRegionHaarData
#check S3135ModelHaar_scaling_image_eq

/-! ## Nontrivial model scaling witness (baseUnit := -1) -/

/-- The completion-side base unit `-1` of the model scaling: a genuine nontrivial
unit with `(-1)*(-1) = 1` and norm one. -/
noncomputable def s3135_modelBaseUnit : ℚ_[concreteRationalPrime]ˣ where
  val := (-1 : ℚ_[concreteRationalPrime])
  inv := (-1 : ℚ_[concreteRationalPrime])
  val_inv := by ring
  inv_val := by ring

/-- The base unit has norm one. -/
theorem s3135_modelBaseUnit_norm_one :
    ‖(s3135_modelBaseUnit : ℚ_[concreteRationalPrime])‖ = 1 := by
  show ‖(-1 : ℚ_[concreteRationalPrime])‖ = 1
  rw [norm_neg, norm_one]

/-- The corresponding `Z_p`-unit scalar pair `(-1, -1)` has product one. -/
theorem s3135_zp_negOne_mul :
    (-1 : ℤ_[concreteRationalPrime]) * (-1 : ℤ_[concreteRationalPrime]) = 1 := by
  ring

/-- **Nontrivial model scaling instance**: `mu((-1)*O) = mu(O)` for the actual Haar
readout on the integral log-shell (the unconditional nontrivial witness; baseUnit = 2
is a conditional special case). -/
theorem s3135_modelHaar_negOne_scaling_eq :
    S3135ModelHullHaar
        ((fun x : S3135ModelHullPoint =>
            algebraMap ℚ_[concreteRationalPrime] S3135ModelHullPoint
              ((-1 : ℤ_[concreteRationalPrime]) : ℚ_[concreteRationalPrime]) * x) ''
          ((integralLogShell (K := concreteLogShellField)
            (p := concreteRationalPrime)) : Set S3135ModelHullPoint)) =
      S3135ModelHullHaar
        ((integralLogShell (K := concreteLogShellField)
          (p := concreteRationalPrime)) : Set S3135ModelHullPoint) :=
  S3135ModelHaar_scaling_image_eq (-1) (-1) s3135_zp_negOne_mul

#check s3135_modelBaseUnit
#check s3135_modelBaseUnit_norm_one
#check s3135_modelHaar_negOne_scaling_eq

end LeanFormal.IUT.XiFPaper.S3135ModelSkeletonInterfaceActual
end
