import tmp.sheaf.xif.paper.S3135ModelValueDataActual

/-!
# task-72 (ii-b): model value data WITH a genuine unit factor (qpilot design adopted)

**Model-construction component, not a paper object.**  Design answer adopted from
qpilot: the from-scratch model's value monoid must contain a genuine unit factor,
because the single-generator normalized realified group has unit group = degree kernel
(unit iff r = 0), so a nontrivial unit z != 1 would have non-zero degree.  Proposed and
implemented here GENERICALLY:

`Mon_model := GlobalDivisorMonoid X x U` for a commutative group `U` (model
cusp/torsion unit factor; qpilot's suggested instance is `U := Multiplicative (ZMod 2)`,
any nontrivial `U` works — the file is generic so the paper-general case is not
specialized);

`degree_model (a, b) := globalDegree a` (the unit factor has degree `1`, so its
`toAdd` log-degree is `0`);

`posRealAction_model r := (normalizedRealifiedPrimePowerHom vp r, 1)`.

For any nontrivial `u : U` (`u ≠ 1`), the element `z := (1, u)` is a genuine
nontrivial unit of `Mon_model` with `degree z = 1` (i.e. log-degree `0`):
`s3135_modelValueData_withUnitFactor_nontrivial_unit`.  This is the value-level unit
the from-scratch model will use as the nontrivial procession scaling (with the
completion-scalar component supplied by the model theta-pilot data, per the interface
requirement).
-/

noncomputable section

open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalRealifiedFrobenioidActual
open LeanFormal.IUT.XiFPaper.S3133ValueGroupDegreeActual
open LeanFormal.IUT.XiFPaper.S3135ValueGroupDegreeUnconditionalActual
open LeanFormal.IUT.XiFPaper.S3135ModelValueDataActual
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput

namespace LeanFormal.IUT.XiFPaper.S3135ModelValueDataUnitFactorActual

/-- **Model value data with a genuine unit factor** (qpilot design): value monoid
`GlobalDivisorMonoid X x U`, degree reads the realified degree, action is the
normalized generator action on the first factor. -/
noncomputable def s3135_modelValueData_withUnitFactor
    {l : PrimeGeFive} (X : N8NativeInput l) (vp : GlobalPrimeIndex (X := X))
    (U : Type) [CommGroup U] : S3135ModelValueData where
  Mon := GlobalDivisorMonoid (X := X) × U
  commMonoid := inferInstance
  degree := (globalDegree (X := X)).comp (MonoidHom.fst _ _)
  posRealAction :=
    (normalizedRealifiedPrimePowerHom (X := X) vp).prod
      (1 : Multiplicative ℝ →* U)
  degree_posRealAction := by
    intro r
    exact normalizedRealifiedPrimePowerHom_degree (X := X) vp r

/-- **The model has a genuine nontrivial unit z with zero log-degree**: for any
nontrivial element `u` of the model unit factor `U`, `z := (1, u)` is a unit,
`z ≠ 1`, and `degree z = 1` (hence `toAdd (degree z) = 0`). -/
theorem s3135_modelValueData_withUnitFactor_nontrivial_unit
    {l : PrimeGeFive} (X : N8NativeInput l) (vp : GlobalPrimeIndex (X := X))
    (U : Type) [CommGroup U] (u : U) (hu : u ≠ 1) :
    let data := s3135_modelValueData_withUnitFactor X vp U
    let z : data.Mon := (1, u)
    z ≠ 1 ∧ data.degree z = 1 ∧ ∃ z' : data.Mon, z * z' = 1 := by
  intro data z
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h2 : u = 1 := congrArg Prod.snd h
    exact hu h2
  · show globalDegree (X := X) ((1 : GlobalDivisorMonoid (X := X))) = 1
    simp
  · refine ⟨(1, u⁻¹), ?_⟩
    show ((1 : GlobalDivisorMonoid (X := X)) * 1, u * u⁻¹) = (1, 1)
    simp

#check s3135_modelValueData_withUnitFactor
#check s3135_modelValueData_withUnitFactor_nontrivial_unit

end LeanFormal.IUT.XiFPaper.S3135ModelValueDataUnitFactorActual
end
