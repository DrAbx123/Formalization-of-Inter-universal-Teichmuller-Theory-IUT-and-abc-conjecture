import tmp.sheaf.xif.paper.S3135ValueGroupCompatibilityActual

noncomputable section

open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalRealifiedFrobenioidActual
open LeanFormal.IUT.XiFPaper.S3133ValueGroupDegreeActual
open LeanFormal.IUT.XiFPaper.S3135ValueGroupDegreeUnconditionalActual
open LeanFormal.IUT.XiFPaper.S3135ValueGroupCompatibilityActual
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput

namespace LeanFormal.IUT.XiFPaper.S3135RealifiedIdentActual

/-- **Corpus sub-lemma datum (B), III Rem 3.9.4 "elementary observations"**: the actual
source log-degree on the realization agrees with the actual realified degree
`globalDegree` on the normalized generator ray.  This is the only identification
needed to close F4.a; the actual degree-faithfulness
`globalDegree (normalizedRealifiedPrimePowerHom vp r) = r` is already citable. -/
def S3135ValueMonoidRealifiedIdentification
    {l : PrimeGeFive} (X : N8NativeInput l)
    {l' : PrimeGeFive} {V : Type} (I : OriginalInput l' V) (v : V)
    (R : I.SourceImageRealization v)
    (vp : GlobalPrimeIndex (X := X)) : Prop :=
  ∀ r : Multiplicative ℝ,
    I.logDegreeAt 0 0 v (R.posRealAction r) =
      Multiplicative.toAdd (globalDegree (X := X)
        (normalizedRealifiedPrimePowerHom (X := X) vp r))

/-- The realified identification closes F4.a's compatibility lemma. -/
theorem s3135_compatibility_of_realifiedIdentification
    {l : PrimeGeFive} (X : N8NativeInput l)
    {l' : PrimeGeFive} {V : Type} (I : OriginalInput l' V) (v : V)
    (R : I.SourceImageRealization v) (vp : GlobalPrimeIndex (X := X))
    (hid : S3135ValueMonoidRealifiedIdentification X I v R vp) :
    S3135ValueGroupDegreeCompatibility X I v R vp := by
  intro r
  rw [hid r, normalizedRealifiedPrimePowerHom_degree (X := X) vp]
  rfl

#check S3135ValueMonoidRealifiedIdentification
#check s3135_compatibility_of_realifiedIdentification
end LeanFormal.IUT.XiFPaper.S3135RealifiedIdentActual
end