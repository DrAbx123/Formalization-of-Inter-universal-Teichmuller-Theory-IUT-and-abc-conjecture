import tmp.sheaf.xif.paper.S3135ValueGroupDegreeActualActual

/-!
# task-39 (1): the value-monoid identification, reduced to ONE explicit structure

**COMPONENT / exact-Missing record, not a paper object.**  Consumer: task-33 F4
residual (a) `S3135ValueGroupDegreeSection`; final consumer: the F4 height
comparison (task-17/22/25 chain).

Task-33 constructed the actual Real-indexed degree-faithful monoid action on the
actual realified divisor group (`normalizedRealifiedPrimePowerHom` with degree the
identity, qpilot's `GlobalRealifiedFrobenioidActual`).  The only remaining piece of
residual (a) is the identification with the source value monoid.  This file records
that identification as ONE structure with exact fields and proves that it closes the
residual:

`S3135ValueMonoidIdentification X I v R vp hweight`:

* `psi : GlobalDivisorMonoid X ->* I.ValueMonoidAt 0 0 v` — a monoid homomorphism
  from the actual realified divisor group of `X` to the source value monoid of the
  input `I` at place `v`;
* `degree_comm` — `ofAdd (logDegreeAt (psi z)) = globalDegree z` for all `z`
  (degree commutation; the value-monoid degree is the global realified degree);
* `agrees` — on the normalized generator action,
  `psi ([vp]^(r/weight)) = R.posRealAction (ofAdd r)` for all `r`
  (the actual q-pilot/theta value realization agrees with the realified action;
  IUT III Remark 3.9.4; IUT II section 1; [AbsTopIII] Proposition 5.8(ii)).

From the structure we prove the actual value-group degree section
(`s3135_valueGroupDegreeSection_of_identification`) and full faithfulness of the
actual source realization (`s3135_valueGroupFaithfulness_of_identification`), hence
the F4 card (1) reduced form `S3135PointLogShellFaithfulness`
(`s3135_pointFaithfulness_of_identification`).

## Why this is the minimal missing (and not derivable today)

Neither the tree's source value monoids nor qpilot's realified divisor group carry a
constructed degree-commuting hom between them: qpilot supplies only the actual
divisor group and its `globalDegree` readout, and the prime-strip value monoid is an
abstract field of `OriginalInput` (`FPrimeStrip.Mon`) with no recorded map to the
global realified Frobenioid.  The missing source datum is exactly the identification
of the value group of the global realified Frobenioid with the value monoid of the
prime-strip (IUT II section 1; IUT III Remark 3.9.4; paper-faithful coefficient
normalization).  Owner: abc; construction plan: use qpilot's actual
`GlobalRealifiedFrobenioidActual` plus a prime index `vp` with nonzero weight
(candidate: mainline S3131 weight normalization data), then a degree-commuting hom
into the source `Mon v` — to be attempted once mainline/qpilot confirm whether any
such map is recorded.

## task-39 (2)/(3) status

(2) the additive-Haar modulus law `mu(c * S) = ||c|| * mu(S)` on the actual
`concreteLogShellField` is SPLIT OFF to the hull stream (owner: hull; hull has the
actual `sourceHullHaar` addHaar and unit-reference mass 1; exact statement and
Mathlib toolkit sent by message 2026-11-10).  abc does not duplicate it.
(3) the paper `lambda` with log-degree 0 plus procession-normalization
identification remains the named input `S3135ScalingLogDegreeZero`
(IUT III Proposition 3.9(i) p.115; Remark 3.9.5(i) pp.158-159); the Haar modulus law
(2) supplies the normalized-volume side, the paper choice of lambda supplies the
degree side.
-/

noncomputable section

open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalRealifiedFrobenioidActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalObjectActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT.XiFPaper.S3133ValueGroupDegreeActual
open LeanFormal.IUT.XiFPaper.S3135ValueGroupDegreeActualActual
open LeanFormal.IUT.XiFPaper.S3135ResidualNarrowingActual
open LeanFormal.IUT.XiFPaper.S3135ActualF4LogShellDegreeActual
open LeanFormal.IUT.XiFPaper.S3135F4ActualHullResidualActual
open LeanFormal.IUT.XiFPaper.S3135LogShellValueGroupActual
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput

namespace LeanFormal.IUT.XiFPaper.S3135ValueGroupIdentificationActual

universe uvL

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable {l' : PrimeGeFive} {V : Type uvL}
variable (I : OriginalInput.{0, uvL, 0, 0, 0} l' V)
variable (v : V) (R : I.SourceImageRealization v)
variable (vp : GlobalPrimeIndex (X := X))
variable (hweight : globalPrimeWeight (X := X) vp ≠ 0)

/-- **Exact missing (task-39 (1))**: the degree-commuting identification of the
actual realified divisor group with the source value monoid, agreeing with the actual
source realization on the normalized generator action. -/
def S3135ValueMonoidIdentification : Prop :=
  ∃ psi : GlobalDivisorMonoid (X := X) →* I.ValueMonoidAt 0 0 v,
    (∀ z : GlobalDivisorMonoid (X := X),
        Multiplicative.ofAdd (I.logDegreeAt 0 0 v (psi z)) = globalDegree (X := X) z) ∧
      (∀ r : Multiplicative ℝ,
        psi (normalizedRealifiedPrimePowerHom (X := X) vp hweight r) = R.posRealAction r)

/-- From the identification: the actual value-group degree section exists. -/
theorem s3135_valueGroupDegreeSection_of_identification
    (hid : S3135ValueMonoidIdentification X I v R vp hweight) :
    S3135ValueGroupDegreeSection (I := I) (v := v) := by
  obtain ⟨psi, hdeg, _hagree⟩ := hid
  refine ⟨psi.comp (normalizedRealifiedPrimePowerHom (X := X) vp hweight), ?_⟩
  intro x
  have h := hdeg
    (normalizedRealifiedPrimePowerHom (X := X) vp hweight (Multiplicative.ofAdd x))
  rw [normalizedRealifiedPrimePowerHom_degree (X := X) vp hweight] at h
  have h' := congrArg Multiplicative.toAdd h
  simpa using h'

/-- From the identification: the actual source realization is degree-faithful. -/
theorem s3135_valueGroupFaithfulness_of_identification
    (hid : S3135ValueMonoidIdentification X I v R vp hweight) :
    S3135ValueGroupDegreeFaithfulness I v R := by
  obtain ⟨psi, hdeg, hagree⟩ := hid
  intro x
  have hag := hagree (Multiplicative.ofAdd x)
  rw [← hag]
  have h := hdeg
    (normalizedRealifiedPrimePowerHom (X := X) vp hweight (Multiplicative.ofAdd x))
  rw [normalizedRealifiedPrimePowerHom_degree (X := X) vp hweight] at h
  have h' := congrArg Multiplicative.toAdd h
  simpa using h'

/-- From the identification: the F4 residual card (1) reduced form holds. -/
theorem s3135_pointFaithfulness_of_identification
    (hid : S3135ValueMonoidIdentification X I v R vp hweight) :
    S3135PointLogShellFaithfulness I v R :=
  s3135_pointFaithfulness_of_valueGroupFaithfulness I v R
    (s3135_valueGroupFaithfulness_of_identification X I v R vp hweight hid)

/-- **task-39 (1) report**: the missing identification is one explicit structure;
(2) additive-Haar modulus is owned by hull; (3) paper lambda data remains. -/
def s3135ValueMonoidIdentificationReport : Audit.Obligation :=
  { id := "IUT-II.value-group-identification-realified-to-primestrip"
    source :=
      "IUT II section 1 (value groups / global realified Frobenioid); IUT III " ++
        "Remark 3.9.4; [AbsTopIII] Proposition 5.8(ii); IUT III Proposition 3.9(i) " ++
        "p.115; IUT III Remark 3.9.5(i) pp.158-159"
    status := Audit.VerificationStatus.interface
    note :=
      "REDUCED: the last piece of F4 residual (a) is the single structure " ++
        "S3135ValueMonoidIdentification: a degree-commuting monoid hom from the " ++
        "actual realified divisor group (qpilot GlobalRealifiedFrobenioidActual) to " ++
        "the source value monoid, agreeing with R.posRealAction on the normalized " ++
        "generator action.  From it the actual value-group degree section, full " ++
        "faithfulness and the F4 card (1) reduced form follow (proved).  NOT " ++
        "constructible today: no recorded map from FPrimeStrip.Mon to the global " ++
        "realified Frobenioid and no prime index v with nonzero weight pinned as an " ++
        "actual object in this stream; candidate data: mainline S3131 weight " ++
        "normalization + qpilot realified divisor group.  Owner: abc; plan: obtain " ++
        "the degree-commuting hom once the value-group/prime-strip identification is " ++
        "supplied (paper: IUT II section 1).  (2) additive-Haar modulus law " ++
        "mu(c*S)=||c||*mu(S) on actual concreteLogShellField: SPLIT OFF to hull " ++
        "(owner hull; actual addHaar + unit mass 1 there; exact statement sent). " ++
        "(3) paper lambda with log-degree 0 + procession-normalization " ++
        "identification: remains S3135ScalingLogDegreeZero (III Prop 3.9(i) p.115; " ++
        "Rem 3.9.5(i) pp.158-159)."
    dependsOn := [ "IUT-III.cor312-to-ABC-conditional-interface" ]
    sorryItems :=
      [ "S3135ValueMonoidIdentification (realified divisor group -> source value monoid, degree-commuting)",
        "S3135AdditiveHaarModulusLaw (hull-owned)",
        "S3135ScalingLogDegreeZero (paper lambda log-degree 0 + procession normalization)" ] }

#check S3135ValueMonoidIdentification
#check s3135_valueGroupDegreeSection_of_identification
#check s3135_valueGroupFaithfulness_of_identification
#check s3135_pointFaithfulness_of_identification

end LeanFormal.IUT.XiFPaper.S3135ValueGroupIdentificationActual
end
