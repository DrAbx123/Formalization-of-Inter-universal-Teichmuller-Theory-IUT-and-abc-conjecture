import tmp.sheaf.xif.paper.S3129IQHullLogVolumeSourceActual

/-!
# task-54 (2) exact missing: unit self-similarity of the actual integral log-shell

**COMPONENT / exact-Missing record, not a paper object.**  Consumer: F4 (b2), the
`integralLogShell` self-similarity under the paper scaling `lambda`.

The paper `lambda` with log-degree 0 is a unit of the integral structure, and a unit
of `Integers K` must preserve the actual integral log-shell lattice:

`S3135LogShellUnitSelfSimilarity : (fun x => (u : K) * x) '' integralLogShell =
 integralLogShell` for every unit `u` of `Integers K`.

Attempt via the repo lattice-closure lemma `integralLogShell_padicInt_mul_mem` blocked
by a cast: that lemma takes scalars of type `ℤ_[p]`, whereas
`Integers concreteLogShellField` appears as its own subtype; the needed identification
(`Integers K` with `ℤ_[p]` / the concrete place integers from
`Example36SourceLogKummerIdentification`) must be supplied first (or the closure
reproved directly from the open-compact lattice).  Source: IUT III Proposition 3.9(i)
p.115; Remark 3.9.5(i) pp.158-159.  Owner: abc.
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

namespace LeanFormal.IUT.XiFPaper.S3135LogShellUnitSelfSimilarityMissingActual

/-- **Exact missing (task-54 (2))**: integral units preserve the actual integral
log-shell. -/
def S3135LogShellUnitSelfSimilarity : Prop :=
  ∀ u : (Integers (K := concreteLogShellField))ˣ,
    (fun x => ((u : Integers (K := concreteLogShellField)) :
        concreteLogShellField) * x) '' ((integralLogShell
          (K := concreteLogShellField) (p := concreteRationalPrime)) :
            Set concreteLogShellField) =
      ((integralLogShell (K := concreteLogShellField)
        (p := concreteRationalPrime)) : Set concreteLogShellField)

/-- The missing unit self-similarity implies the log-shell self-similarity hypothesis
consumed by the task-50 normalized-Haar reduction (for the paper `lambda`, once it is
identified with an integral unit). -/
theorem s3135_logShellSelfSimilarity_of_unit (u : (Integers (K := concreteLogShellField))ˣ) :
    S3135LogShellUnitSelfSimilarity →
    (fun x => ((u : Integers (K := concreteLogShellField)) :
        concreteLogShellField) * x) '' ((integralLogShell
          (K := concreteLogShellField) (p := concreteRationalPrime)) :
            Set concreteLogShellField) =
      ((integralLogShell (K := concreteLogShellField)
        (p := concreteRationalPrime)) : Set concreteLogShellField) :=
  fun h => h u

/-- Task-54 (2) status record. -/
def s3135UnitSelfSimilarityReport : Audit.Obligation :=
  { id := "IUT-III.integral-log-shell-unit-self-similarity"
    source :=
      "IUT III Proposition 3.9(i) p.115; IUT III Remark 3.9.5(i) pp.158-159; " ++
        "IUT III Corollary 3.12 :10324-10353"
    status := Audit.VerificationStatus.interface
    note :=
      "EXACT MISSING: S3135LogShellUnitSelfSimilarity (integral units preserve the " ++
        "actual integral log-shell image).  Attempt via " ++
        "integralLogShell_padicInt_mul_mem blocked on the cast between " ++
        "Integers concreteLogShellField and Z_[p]; need the Example36 integers " ++
        "identification or a direct open-compact lattice proof.  Once proved, with " ++
        "the paper lambda = integral unit (log-degree 0) this supplies the " ++
        "self-similarity hypothesis of s3135_haar_normalized_of_unitScaling, and with " ++
        "the modulus law (S3135HaarIndexActual + S3135HaarPushforwardActual scalar " ++
        "factor) gives mu(lambda·O) = mu(O).  Owner: abc."
    dependsOn := [ "IUT-III.cor312-to-ABC-conditional-interface" ]
    sorryItems :=
      [ "S3135LogShellUnitSelfSimilarity",
        "S3135LogShellScalingIndex",
        "S3135AdditiveHaarModulusLaw" ] }

#check S3135LogShellUnitSelfSimilarity
#check s3135_logShellSelfSimilarity_of_unit

end LeanFormal.IUT.XiFPaper.S3135LogShellUnitSelfSimilarityMissingActual
end
