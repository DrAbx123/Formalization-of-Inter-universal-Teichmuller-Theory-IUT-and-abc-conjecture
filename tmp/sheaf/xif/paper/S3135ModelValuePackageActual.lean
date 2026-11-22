import tmp.sheaf.xif.paper.S3135ValueGroupCompatibilityActual

/-!
# task-72 piece (ii)+(vi): from-scratch model value-monoid / degree / action package

**Model-construction component, not a paper object.**  Consumer: qpilot's task-72
from-scratch Example 3.6 model (placeToMod provenance absent, so the model is built
from basic data).

The package fixed here is the value-group side of the model, using the APPROVED route:
the value monoid `Mon v` is the actual global realified divisor group
(`GlobalDivisorMonoid (X := X)`, rank infinite over places), the degree is the actual
`globalDegree`, and the Real-indexed action is the actual normalized realified
generator action `normalizedRealifiedPrimePowerHom` (qpilot's citable
`S3133GlobalPrimeWeightActual`/`S3133ValueGroupDegreeActual`; unconditional version
in `S3135ValueGroupDegreeUnconditionalActual`).  Hence:

* `s3135_modelPosRealAction_degree`: the degree of the model action is the identity
  on `Multiplicative R` (the citable `normalizedRealifiedPrimePowerHom_degree`);
* rewriting the source realization's log-degree along this action makes F4.a's
  compatibility lemma `S3135ValueGroupDegreeCompatibility` hold BY CONSTRUCTION:
  in the model construction the realization's `posRealAction` is defined to be this
  action and `logDegreeAt` is defined from `globalDegree`, so the single
  construction obligation is the definitional equation
  `logDegreeAt (posRealAction r) = toAdd r` (recorded as a package field).

The package below is what qpilot's model assembly must instantiate; the F4.a closure
theorem then follows mechanically (via the citable
`s3135_pointFaithfulness_of_compatibility`).
-/

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

namespace LeanFormal.IUT.XiFPaper.S3135ModelValuePackageActual

/-- The model value monoid: the actual global realified divisor group. -/
abbrev S3135ModelValueMonoid {l : PrimeGeFive} (X : N8NativeInput l) : Type _ :=
  GlobalDivisorMonoid (X := X)

/-- The model Real-indexed action: the normalized realified generator action. -/
noncomputable abbrev s3135ModelPosRealAction
    {l : PrimeGeFive} (X : N8NativeInput l) (vp : GlobalPrimeIndex (X := X)) :
    Multiplicative ℝ →* S3135ModelValueMonoid X :=
  normalizedRealifiedPrimePowerHom (X := X) vp

/-- The model action's degree is the identity (citable degree identity of the
normalized realified generator action). -/
theorem s3135_modelPosRealAction_degree
    {l : PrimeGeFive} (X : N8NativeInput l) (vp : GlobalPrimeIndex (X := X))
    (r : Multiplicative ℝ) :
    globalDegree (X := X) (s3135ModelPosRealAction X vp r) = r :=
  normalizedRealifiedPrimePowerHom_degree (X := X) vp r

/-- **Construction package for the model's source realization** (field (vi)): the
model defines `posRealAction` to be the realified generator action and `logDegreeAt`
from `globalDegree`, so the only construction obligation is the definitional
log-degree equation below.  Supplying it yields F4.a's compatibility by construction. -/
structure S3135FromScratchValuePackage
    {l : PrimeGeFive} (X : N8NativeInput l)
    {l' : PrimeGeFive} {V : Type} (I : OriginalInput l' V) (v : V)
    (R : I.SourceImageRealization v) (vp : GlobalPrimeIndex (X := X)) : Prop where
  /-- The model's log-degree reads the realified degree (model definition): the
  source realization is degree-faithful on the generator action. -/
  logDegreeAt_eq : ∀ r : Multiplicative ℝ,
    I.logDegreeAt 0 0 v (R.posRealAction r) = Multiplicative.toAdd r

/-- **F4.a closure by construction** in the from-scratch model: the package yields the
compatibility lemma, hence F4 card (1) (and, with the scaling-zero card, the actual
F4 clause). -/
theorem s3135_compatibility_of_fromScratchValuePackage
    {l : PrimeGeFive} (X : N8NativeInput l)
    {l' : PrimeGeFive} {V : Type} (I : OriginalInput l' V) (v : V)
    (R : I.SourceImageRealization v) (vp : GlobalPrimeIndex (X := X))
    (hpkg : S3135FromScratchValuePackage X I v R vp) :
    S3135ValueGroupDegreeCompatibility X I v R vp := by
  intro r
  rw [hpkg.logDegreeAt_eq r]
  exact (normalizedRealifiedPrimePowerHom_degree (X := X) vp r).symm

/-- F4 card (1) reduced form, from the from-scratch package. -/
theorem s3135_pointFaithfulness_of_fromScratchValuePackage
    {l : PrimeGeFive} (X : N8NativeInput l)
    {l' : PrimeGeFive} {V : Type} (I : OriginalInput l' V) (v : V)
    (R : I.SourceImageRealization v) (vp : GlobalPrimeIndex (X := X))
    (hpkg : S3135FromScratchValuePackage X I v R vp) :
    S3135PointLogShellFaithfulness I v R :=
  s3135_pointFaithfulness_of_compatibility X I v R vp
    (s3135_compatibility_of_fromScratchValuePackage X I v R vp hpkg)

/-- The actual F4 clause by construction (package + scaling-zero card). -/
theorem s3135_actualF4_of_fromScratchValuePackage
    {l : PrimeGeFive} (X : N8NativeInput l)
    {l' : PrimeGeFive} {V : Type} (I : OriginalInput l' V) (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l')
    (D : I.SourceUnitRegionHaarData v R n) (vp : GlobalPrimeIndex (X := X))
    (hpkg : S3135FromScratchValuePackage X I v R vp)
    (hzero : S3135ScalingLogDegreeZero I v R n D) :
    FrontierHeightComparisonClause (I.sourceUnitRegionHaarInterface v R n D)
      (fun _ _ a b c => abcSourcePoint I v R a b c) :=
  s3135_actualF4_of_compatibility X I v R n D vp
    (s3135_compatibility_of_fromScratchValuePackage X I v R vp hpkg) hzero

#check S3135ModelValueMonoid
#check s3135ModelPosRealAction
#check s3135_modelPosRealAction_degree
#check S3135FromScratchValuePackage
#check s3135_actualF4_of_fromScratchValuePackage

end LeanFormal.IUT.XiFPaper.S3135ModelValuePackageActual
end
