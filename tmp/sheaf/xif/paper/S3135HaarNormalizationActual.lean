import tmp.sheaf.xif.paper.S3135HaarModulusActual

/-!
# task-50: the paper `lambda` normalized Haar equality from the general modulus law + log-shell self-similarity

**COMPONENT / exact-Missing record.**  Consumer: F4 (b) `S3135ScalingLogDegreeZero`
(paper `lambda·O` procession normalization, IUT III Proposition 3.9(i) p.115;
Remark 3.9.5(i) pp.158-159; Corollary 3.12:10324-10353).

This file reduces the paper normalized-Haar equality to **two** concrete facts:

1. the general additive-Haar modulus law on the actual concrete completion, with the
   actual unit compact `integralLogShell` of hull's `sourceHullHaar`
   (`S3135AdditiveHaarModulusLaw`, task-47; general case still the named exact
   missing, Mathlib plan `Measure.isAddHaarMeasure_map` + `addHaarScalarFactor`);
2. **self-similarity of the actual integral log-shell under the paper scaling**
   `c`: `(fun x => c * x) '' integralLogShell = integralLogShell` — the
   unit-scaling invariance of the log-shell (paper: the procession-normalized
   scaling `lambda` is a unit, i.e. has log-degree 0, so it preserves the normalized
   log-shell; IUT III Proposition 3.9(i) p.115; Remark 3.9.5(i)).

Under these two facts the modulus of `c` is forced to `1` by evaluating the modulus
law on the unit compact, whose Haar mass is exactly `1`
(`sourceHullHaar_integralLogShell_eq_one`), and consequently the scaled unit region
has the same normalized Haar mass as the unit region:

`s3135_haar_normalized_of_unitScaling`:
`sourceHullHaar ((fun x => c * x) '' sourceHullUnitRegion) =
 sourceHullHaar sourceHullUnitRegion`.

This is the `mu(lambda·O) = mu(O)` conclusion of the procession normalization on the
actual objects, with the paper `lambda` supplied as the actual scaling `c`
satisfying the two facts above.  Neither fact is proved in the tree today: the
general modulus law is the named missing (`S3135AdditiveHaarModulusLaw`) and the
integral-log-shell self-similarity under the paper scaling is the second missing
(it is the log-shell/unit normalization of IUT III Proposition 3.9(i), not recorded
in `S3129`; hull confirmed).  Owner: abc.

Proved here (pure algebra on the actual Haar readouts, no inequality assumed):
the modulus-`1` forcing and the normalized equality.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual
open LeanFormal.IUT.XiFPaper.S3135HaarModulusActual

namespace LeanFormal.IUT.XiFPaper.S3135HaarNormalizationActual

local instance measCSF2 : MeasurableSpace concreteLogShellField := borel _
local instance borelCSF2 : BorelSpace concreteLogShellField := ⟨rfl⟩

/-- **The paper scaling is a Haar-unit.**  If the paper scaling `c ≠ 0` preserves
the actual integral log-shell and satisfies the additive modulus law with modulus
`k`, then `k c = 1`: evaluate the modulus law on the unit compact, whose Haar mass
is exactly `1`. -/
theorem s3135_haar_modulus_eq_one_of_unitScaling
    (k : concreteLogShellField → ℝ) (_hk : ∀ c, 0 ≤ k c)
    (hlaw : ∀ (c : concreteLogShellField), c ≠ 0 → ∀ S : Set concreteLogShellField,
      MeasurableSet S →
        sourceHullHaar ((fun x => c * x) '' S) =
          ENNReal.ofReal (k c) * sourceHullHaar S)
    (c : concreteLogShellField) (hc : c ≠ 0)
    (hU : (fun x => c * x) '' (integralLogShell (K := concreteLogShellField)
      (p := concreteRationalPrime)) =
      (integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime)))
    (hmeas : MeasurableSet ((integralLogShell (K := concreteLogShellField)
      (p := concreteRationalPrime)) : Set concreteLogShellField)) :
    k c = 1 := by
  have hU1 : sourceHullHaar ((fun x => c * x) '' (integralLogShell
      (K := concreteLogShellField) (p := concreteRationalPrime))) = 1 := by
    rw [hU, sourceHullHaar_integralLogShell_eq_one]
  have hlawU := hlaw c hc _ hmeas
  rw [hU1, sourceHullHaar_integralLogShell_eq_one, mul_one] at hlawU
  have h := hlawU.symm
  rwa [ENNReal.ofReal_eq_one] at h

/-- **The paper normalized-Haar equality from the modulus law and log-shell
self-similarity**: the paper scaling `c` preserves the actual unit region's Haar
mass, i.e. `mu(lambda·O) = mu(O)` (procession normalization). -/
theorem s3135_haar_normalized_of_unitScaling
    (k : concreteLogShellField → ℝ) (hk : ∀ c, 0 ≤ k c)
    (hlaw : ∀ (c : concreteLogShellField), c ≠ 0 → ∀ S : Set concreteLogShellField,
      MeasurableSet S →
        sourceHullHaar ((fun x => c * x) '' S) =
          ENNReal.ofReal (k c) * sourceHullHaar S)
    (c : concreteLogShellField) (hc : c ≠ 0)
    (hU : (fun x => c * x) '' (integralLogShell (K := concreteLogShellField)
      (p := concreteRationalPrime)) =
      (integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime)))
    (hmeas : MeasurableSet ((integralLogShell (K := concreteLogShellField)
      (p := concreteRationalPrime)) : Set concreteLogShellField)) :
    sourceHullHaar ((fun x => c * x) '' (integralLogShell
        (K := concreteLogShellField) (p := concreteRationalPrime))) =
      sourceHullHaar (integralLogShell (K := concreteLogShellField)
        (p := concreteRationalPrime)) := by
  have hk1 := s3135_haar_modulus_eq_one_of_unitScaling k hk hlaw c hc hU hmeas
  rw [hlaw c hc _ hmeas, hk1, ENNReal.ofReal_one, one_mul]

/-- Task-50 residual record: the paper normalized-Haar equality is reduced to the
general modulus law (`S3135AdditiveHaarModulusLaw`) and the integral-log-shell
self-similarity under the paper scaling. -/
def s3135HaarNormalizationReport : Audit.Obligation :=
  { id := "IUT-III.paper-lambda-normalized-haar-reduction"
    source :=
      "IUT III Definition 1.1 / Remark 1.2.2 (log-shell); IUT III Proposition " ++
        "1.2; IUT III Proposition 3.9(i) p.115; IUT III Remark 3.9.5(i) " ++
        "pp.158-159; IUT III Corollary 3.12 :10324-10353; IUT IV section 1 " ++
        "Proposition 1.4 iut4.txt:671-760"
    status := Audit.VerificationStatus.interface
    note :=
      "REDUCED: the paper mu(lambda·O)=mu(O) normalized-Haar equality follows from " ++
        "(i) the general additive-Haar modulus law on the actual completion " ++
        "(S3135AdditiveHaarModulusLaw; general case named missing, Mathlib plan " ++
        "isAddHaarMeasure_map + addHaarScalarFactor) and (ii) the actual " ++
        "integralLogShell self-similarity under the paper scaling " ++
        "(fun x => c * x) '' integralLogShell = integralLogShell (unit-scaling / " ++
        "log-degree-0 normalization of III Prop 3.9(i), not recorded in S3129).  " ++
        "PROVED: under (i)+(ii) the modulus of c is forced to 1 (evaluating the law " ++
        "on the unit compact with Haar mass 1) and the scaled unit region has the " ++
        "same normalized Haar mass (s3135_haar_modulus_eq_one_of_unitScaling, " ++
        "s3135_haar_normalized_of_unitScaling).  Second F4 (b) datum remains " ++
        "S3135ScalingLogDegreeZero (paper lambda log-degree 0).  Owner: abc."
    dependsOn := [ "IUT-III.cor312-to-ABC-conditional-interface" ]
    sorryItems :=
      [ "S3135AdditiveHaarModulusLaw (general modulus law)",
        "integralLogShell self-similarity under the paper scaling",
        "S3135ScalingLogDegreeZero (paper lambda log-degree 0)" ] }

#check s3135_haar_modulus_eq_one_of_unitScaling
#check s3135_haar_normalized_of_unitScaling
#check s3135HaarNormalizationReport

end LeanFormal.IUT.XiFPaper.S3135HaarNormalizationActual
end
