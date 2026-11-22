import tmp.sheaf.xif.paper.S3135ModelValueDataUnitFactorActual

noncomputable section

open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.GlobalRealifiedFrobenioidActual
open LeanFormal.IUT.XiFPaper.S3133ValueGroupDegreeActual
open LeanFormal.IUT.XiFPaper.S3135ValueGroupDegreeUnconditionalActual
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.S3135ModelValueDataActual
open LeanFormal.IUT.XiFPaper.S3135ModelValueDataUnitFactorActual

namespace LeanFormal.IUT.XiFPaper.S3135ModelValueUnitBatchActual

/-- **Value-side scaling log-degree lemma (model)**: a value-monoid element of degree
one has zero log-degree (the value side of the nontrivial procession scaling). -/
theorem s3135_model_valueUnit_logDegree_zero
    (data : S3135ModelValueData) (z : data.Mon) (hz : data.degree z = 1) :
    Multiplicative.toAdd (data.degree z) = 0 := by
  rw [hz]
  rfl

/-- The unit-factor model supplies such an element of degree one (nontrivial unit),
so its log-degree is zero. -/
theorem s3135_model_valueUnit_exists_logDegree_zero
    {l : PrimeGeFive} (X : N8NativeInput l) (vp : GlobalPrimeIndex (X := X))
    (U : Type) [CommGroup U] (u : U) (hu : u ≠ 1) :
    ∃ z : (s3135_modelValueData_withUnitFactor (X := X) vp U).Mon,
      (s3135_modelValueData_withUnitFactor (X := X) vp U).degree z = 1 ∧
        Multiplicative.toAdd
          ((s3135_modelValueData_withUnitFactor (X := X) vp U).degree z) = 0 := by
  classical
  have h := s3135_modelValueData_withUnitFactor_nontrivial_unit
    (X := X) (vp := vp) U u hu
  dsimp only at h
  obtain ⟨hz_ne, hz_deg, _⟩ := h
  exact ⟨_, hz_deg, s3135_model_valueUnit_logDegree_zero _ _ hz_deg⟩

#check s3135_model_valueUnit_logDegree_zero
#check s3135_model_valueUnit_exists_logDegree_zero

end LeanFormal.IUT.XiFPaper.S3135ModelValueUnitBatchActual