import tmp.sheaf.xif.paper.S3129IQHullLogVolumeSourceActual

/-!
# task-47 (1): the additive-Haar modulus law — exact statement, proved unit case, exact missing

**COMPONENT / exact-Missing record, not a paper object.**  Consumer: F4 (b)
`S3135ScalingLogDegreeZero` (paper `lambda·O` normalization).

Hull's actual Haar layer (`S3129IQHullLogVolumeSourceActual`, EXIT=0):
`sourceHullHaar : Measure concreteLogShellField := Measure.addHaarMeasure
sourceHullUnitCompact` (addHaar on the actual integral log-shell), with
`sourceHullHaar_integralLogShell_eq_one` (unit-reference mass exactly 1),
`sourceHullUnitRegion` compact, and the actual source image inside it.

The required modulus law is recorded here as the named Prop
`S3135AdditiveHaarModulusLaw`: there is a nonnegative modulus function `k` on the
actual completion such that for every `c ≠ 0` and measurable `S`,
`sourceHullHaar ((fun x => c * x) '' S) = ofReal (k c) * sourceHullHaar S`.
The paper-normalized consequence used by F4 (b) is proved below for the unit case and
for any `c` with `k c = 1`:

* `s3135_haar_unit_scaling`: `sourceHullHaar ((fun x => 1 * x) '' S) =
  sourceHullHaar S` (unit modulus is 1),
* `s3135_haar_normalized_of_modulus_one`: if `k c = 1` then the scaled region has
  the same normalized Haar mass as `S` — the `mu(lambda·O) = mu(O)` conclusion
  needed once the paper `lambda` with `k lambda = 1` (log-degree 0) is supplied
  (IUT III Proposition 3.9(i) p.115; Remark 3.9.5(i) pp.158-159).

Exact missing: (i) the modulus law itself (Mathlib plan: multiplication by `c` is an
additive group automorphism, `Measure.isAddHaarMeasure_map` yields addHaar image,
`Measure.addHaarScalarFactor` identifies the scalar, and the modulus of the
multiplier in the normalized completion evaluates the scalar; hull declined
duplication, owner abc); (ii) the paper `lambda` in the source scaling units with
log-degree 0 / modulus 1 (proc. normalization, same refs).  Not proved here beyond
the unit case; no inequality is assumed.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual

namespace LeanFormal.IUT.XiFPaper.S3135HaarModulusActual

local instance measCSF : MeasurableSpace concreteLogShellField := borel _
local instance borelCSF : BorelSpace concreteLogShellField := ⟨rfl⟩

/-- **The additive-Haar modulus law** on the actual concrete completion, with the
scalar factor identified by a nonnegative modulus function `k`. -/
def S3135AdditiveHaarModulusLaw : Prop :=
  ∃ k : concreteLogShellField → ℝ,
    (∀ c, 0 ≤ k c) ∧
      ∀ (c : concreteLogShellField), c ≠ 0 → ∀ S : Set concreteLogShellField,
        MeasurableSet S →
          sourceHullHaar ((fun x => c * x) '' S) =
            ENNReal.ofReal (k c) * sourceHullHaar S

/-- Unit case: scaling by `1` preserves the actual Haar mass. -/
theorem s3135_haar_unit_scaling (S : Set concreteLogShellField) :
    sourceHullHaar ((fun x => (1 : concreteLogShellField) * x) '' S) =
      sourceHullHaar S := by
  simp

/-- The paper-normalized conclusion for a scaling whose modulus is `1`: the scaled
region has the same actual Haar mass as the region (the `mu(lambda·O) = mu(O)`
conclusion of the procession normalization). -/
theorem s3135_haar_normalized_of_modulus_one
    (k : concreteLogShellField → ℝ) (_hk : ∀ c, 0 ≤ k c)
    (hlaw : ∀ (c : concreteLogShellField), c ≠ 0 → ∀ S : Set concreteLogShellField,
      MeasurableSet S →
        sourceHullHaar ((fun x => c * x) '' S) =
          ENNReal.ofReal (k c) * sourceHullHaar S)
    (c : concreteLogShellField) (hc : c ≠ 0)
    (S : Set concreteLogShellField) (hS : MeasurableSet S)
    (hmod : k c = 1) :
    sourceHullHaar ((fun x => c * x) '' S) = sourceHullHaar S := by
  rw [hlaw c hc S hS, hmod, ENNReal.ofReal_one, one_mul]

/-- Exact-missing / status record for task-47 (1). -/
def s3135HaarModulusReport : Audit.Obligation :=
  { id := "IUT-III.additive-haar-modulus-law-concrete-log-shell"
    source :=
      "IUT III Definition 1.1 and Remark 1.2.2 (log-shell); IUT III Proposition " ++
        "1.2 (log-shell / Haar log-volume); IUT III Proposition 3.9(i) p.115; " ++
        "IUT III Remark 3.9.5(i) pp.158-159; IUT III Cor 3.12 :10324-10353"
    status := Audit.VerificationStatus.interface
    note :=
      "REDUCED + EXACT MISSING: the modulus law mu(c*S) = ofReal(k c)*mu(S) on the " ++
        "actual sourceHullHaar (addHaar on the actual integral log-shell, " ++
        "unit-reference mass 1) is stated as S3135AdditiveHaarModulusLaw; the unit " ++
        "case and the normalized conclusion for k c = 1 are PROVED on the actual " ++
        "objects (s3135_haar_unit_scaling, s3135_haar_normalized_of_modulus_one).  " ++
        "NOT PROVED: the general modulus law; Mathlib plan " ++
        "Measure.isAddHaarMeasure_map + Measure.addHaarScalarFactor + modulus of the " ++
        "multiplier in the normalized completion.  Owner: abc (Lead-assigned; hull " ++
        "declined duplication).  Second missing: the paper lambda in the source " ++
        "scaling units with log-degree 0 / modulus 1 (procession normalization; " ++
        "refs above) — this is the F4 (b) paper datum S3135ScalingLogDegreeZero."
    dependsOn := [ "IUT-III.cor312-to-ABC-conditional-interface" ]
    sorryItems :=
      [ "S3135AdditiveHaarModulusLaw (general modulus law)",
        "paper lambda log-degree 0 / modulus 1 (S3135ScalingLogDegreeZero)" ] }

#check S3135AdditiveHaarModulusLaw
#check s3135_haar_unit_scaling
#check s3135_haar_normalized_of_modulus_one
#check s3135HaarModulusReport

end LeanFormal.IUT.XiFPaper.S3135HaarModulusActual
end
