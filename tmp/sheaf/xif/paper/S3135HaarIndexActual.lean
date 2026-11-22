import tmp.sheaf.xif.paper.S3129IQHullLogVolumeSourceActual

/-!
# task-54 (1): actual integral-log-shell index computation on the actual Haar readout

**COMPONENT, not a paper object.**  Consumer: `S3135AdditiveHaarModulusLaw` (F4 (b1)).

Uses the repo's actual integral-log-shell Haar index lemma
`measure_integralLogShell_eq_index_mul` (`IntegralLogShellHaarIndex.lean:51`) on
hull's actual `sourceHullHaar` (addHaar on the actual `integralLogShell`, unit
reference), giving the actual index relation
`sourceHullHaar integralLogShell = logShellIntegerIndex * sourceHullHaar Integers`
with positive finite masses (`measure_localIntegers_pos_lt_top`), plus hull's unit
reference mass `sourceHullHaar_integralLogShell_eq_one`.  This is the lattice side of
the modulus computation: for a scaling `c`, the scalar factor is
`sourceHullHaar (c • Integers) / sourceHullHaar Integers`, and the lattice index of
`Integers` in its `c`-scaled version is `p ^ v(c)` (exact missing
`S3135LogShellScalingIndex`).
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

namespace LeanFormal.IUT.XiFPaper.S3135HaarIndexActual

local instance measCSF4 : MeasurableSpace concreteLogShellField := borel _
local instance borelCSF4 : BorelSpace concreteLogShellField := ⟨rfl⟩

/-- **Actual index relation for the source Haar readout**:
`mu(integralLogShell) = logShellIntegerIndex * mu(Integers)`. -/
theorem s3135_sourceHullHaar_integralLogShell_index :
    sourceHullHaar ((integralLogShell (K := concreteLogShellField)
        (p := concreteRationalPrime)) : Set concreteLogShellField) =
      (logShellIntegerIndex (K := concreteLogShellField)
          (p := concreteRationalPrime) : ENNReal) *
        sourceHullHaar ((Integers (K := concreteLogShellField)) :
          Set concreteLogShellField) := by
  haveI : Measure.IsAddHaarMeasure sourceHullHaar := sourceHullHaar_isAddHaar
  exact measure_integralLogShell_eq_index_mul
    (K := concreteLogShellField) (p := concreteRationalPrime) sourceHullHaar

/-- The actual `Integers`-lattice has positive finite Haar mass. -/
theorem s3135_sourceHullHaar_integers_pos_lt_top :
    0 < sourceHullHaar ((Integers (K := concreteLogShellField)) :
        Set concreteLogShellField) ∧
      sourceHullHaar ((Integers (K := concreteLogShellField)) :
        Set concreteLogShellField) < ⊤ := by
  haveI : Measure.IsAddHaarMeasure sourceHullHaar := sourceHullHaar_isAddHaar
  exact measure_localIntegers_pos_lt_top (K := concreteLogShellField) sourceHullHaar

/-- **Exact missing (task-54 (1)): the scaling index of the actual lattice.**  The
`c`-scaled unit lattice has Haar mass `p ^ (-v(c))` times the unit lattice's mass,
where `v(c)` is the normalized valuation of the scaling (IUT III Proposition 3.9(i)
p.115; Remark 3.9.5(i) pp.158-159). -/
def S3135LogShellScalingIndex : Prop :=
  ∀ (c : concreteLogShellField), c ≠ 0 →
    ∃ v : ℤ, sourceHullHaar
        ((fun x => c * x) '' ((Integers (K := concreteLogShellField)) :
          Set concreteLogShellField)) =
      ENNReal.ofReal ((concreteRationalPrime : ℝ) ^ (-(v : ℝ))) *
        sourceHullHaar ((Integers (K := concreteLogShellField)) :
          Set concreteLogShellField)

/-- Task-54 (1) status record. -/
def s3135HaarIndexReport : Audit.Obligation :=
  { id := "IUT-III.log-shell-scaling-index-modulus"
    source :=
      "IUT III Proposition 1.2; IUT III Proposition 3.9(i) p.115; IUT III Remark " ++
        "3.9.5(i) pp.158-159; IUT III Cor 3.12 :10324-10353"
    status := Audit.VerificationStatus.interface
    note :=
      "HAAR-INDEX SIDE DONE: actual index relation " ++
        "mu(integralLogShell) = logShellIntegerIndex * mu(Integers) proved on " ++
        "hull's sourceHullHaar (repo lemma measure_integralLogShell_eq_index_mul), " ++
        "Integers mass positive finite (measure_localIntegers_pos_lt_top), unit " ++
        "reference mass 1 (hull).  EXACT MISSING: the scaling index computation " ++
        "S3135LogShellScalingIndex (mu(c * Integers) = p^(-v(c)) * mu(Integers)), " ++
        "then Haar uniqueness via Mathlib Measure.isAddHaarMeasure_map + " ++
        "addHaarScalarFactor gives the general modulus law S3135AdditiveHaarModulusLaw " ++
        "(k c = ||c||).  Owner: abc."
    dependsOn := [ "IUT-III.cor312-to-ABC-conditional-interface" ]
    sorryItems :=
      [ "S3135LogShellScalingIndex (scaling index p^(-v c))",
        "S3135AdditiveHaarModulusLaw (general modulus law)" ] }

#check s3135_sourceHullHaar_integralLogShell_index
#check s3135_sourceHullHaar_integers_pos_lt_top
#check S3135LogShellScalingIndex

end LeanFormal.IUT.XiFPaper.S3135HaarIndexActual
end
