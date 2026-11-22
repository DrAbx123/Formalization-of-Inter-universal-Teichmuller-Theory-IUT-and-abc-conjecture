import tmp.sheaf.xif.paper.S3135ValueGroupIdentificationActual
import tmp.sheaf.xif.paper.S3135ValueGroupDegreeUnconditionalActual

/-! # INTERIM (F4.a reduction): necessary degree identity from S3135ValueMonoidIdentification

Background: S3135ValueMonoidIdentification (IUT II section 1; IUT III Remark 3.9.4;
[AbsTopIII] Proposition 5.8(ii)) is an existential psi with a degree-commutation and
a normalized-generator agreement field.  Here we extract the NECESSARY condition
on the actual source realization: the log-degree of posRealAction is the identity
of Multiplicative Real.  This is the reduced target for constructing the
identification (with the definitional psi). No sorry/axiom/True/PUnit. -/

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalRealifiedFrobenioidActual
open LeanFormal.IUT.XiFPaper.S3135ValueGroupIdentificationActual
open LeanFormal.IUT.XiFPaper.S3135ValueGroupDegreeUnconditionalActual
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput

namespace LeanFormal.IUT.XiFPaper.S3131F4aDegreeIdentityActualAdapted

universe uvL

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable {l' : PrimeGeFive} {V : Type uvL}
variable (I : OriginalInput.{0, uvL, 0, 0, 0} l' V)
variable (v : V) (R : I.SourceImageRealization v)
variable (vp : GlobalPrimeIndex (X := X))
variable (hweight : globalPrimeWeight (X := X) vp ≠ 0)

/-- **Reduced F4.a degree identity.**  The value-monoid identification implies that
the source realization's log-degree is the identity of `Multiplicative ℝ` on the
realified action.  (With the definitional psi on the normalized generator, this is
the only obstruction to constructing `S3135ValueMonoidIdentification`.) -/
theorem s3135_valueMonoidIdentification_implies_degreeIdentity
    (hid : S3135ValueMonoidIdentification X I v R vp hweight)
    (r : Multiplicative ℝ) :
    Multiplicative.ofAdd (I.logDegreeAt 0 0 v (R.posRealAction r)) = r := by
  obtain ⟨psi, hdeg, hagree⟩ := hid
  have h1 := hdeg (LeanFormal.IUT.XiFPaper.S3135ValueGroupIdentificationActual.normalizedRealifiedPrimePowerHom (X := X) vp hweight r)
  rw [LeanFormal.IUT.XiFPaper.S3135ValueGroupDegreeUnconditionalActual.normalizedRealifiedPrimePowerHom_degree (X := X)] at h1
  rwa [← hagree r] at h1

#check s3135_valueMonoidIdentification_implies_degreeIdentity

end LeanFormal.IUT.XiFPaper.S3131F4aDegreeIdentityActualAdapted
end