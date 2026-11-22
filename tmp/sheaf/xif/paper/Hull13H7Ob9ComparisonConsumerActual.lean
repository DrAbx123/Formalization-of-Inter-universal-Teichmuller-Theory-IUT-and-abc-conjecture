import tmp.sheaf.xif.paper.Hull10H7Ob9ConsumerActual
import tmp.sheaf.xif.paper.Hull12Ob9BoundTransferActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: H7/Ob9|comparison|upper bound|Ind3 iterate|Hull10 consumer|Hull12 transfer -> hits Hull10H7Ob9ConsumerActual:35-83 (HullH7Ob9ConsumerInputs/hull10_h7ob9_consumer), Hull12Ob9BoundTransferActual (hull12_upperBound_transfer), Indet06H7Ob9WiringActual, S3182Cor312HullDetAssemblyActual -> REUSE (class A downstream consumer: hull+det conclusion AND one-sided bound transfer together; no closure).

# [Hull] 13: H7/Ob9 one-sided comparison consumer (class A)

Corpus: IUT III Remark 3.9.4 (~7151); Step (xi) 10750-10987; conclusion 10897.
CONTENT: given the hull+det assembly inputs, the authoritative H7Ob9 wiring (Indet06),
a base source choice, and an upper bound B holding on the possible-image readout at
an (Ind3) iterate, derive BOTH the Cor 3.12 hull+det conclusion AND the transfer of
the upper bound to the base representative (the one-sided direction needed by the
comparison).  Every input field is consumed.
HONESTY: the deep arbitrary-iterate Ob9 invariance stays class-B named.  Registry
frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Hull13H7Ob9ComparisonConsumerActual

universe ua uv upi umon ui u

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open LeanFormal.IUT.XiFPaper.S3136ModelSourceClauseActual
open LeanFormal.IUT.XiFPaper.S3136ModelNativeDataWithHaarActual
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCoreActual
open LeanFormal.IUT.XiFPaper.S3139SourceMultiradialQuotientActual
open LeanFormal.IUT.XiFPaper.Indet05RouteMultiradialClassActual
open LeanFormal.IUT.XiFPaper.Indet06H7Ob9WiringActual
open LeanFormal.IUT.XiFPaper.Hull10H7Ob9ConsumerActual
open LeanFormal.IUT.XiFPaper.Hull12Ob9BoundTransferActual
open LeanFormal.IUT.XiFPaper.S3182Cor312HullDetAssemblyActual

variable {l : PrimeGeFive} {V : Type uv}

variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- H7/Ob9 comparison consumer inputs: the Hull10 consumer inputs plus an (Ind3)
iterate index and an upper bound B on the possible-image readout at that iterate. -/
structure HullH7Ob9ComparisonInputs
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  consumer : HullH7Ob9ConsumerInputs (l := l) M I
  iterate : Nat
  bound : ℝ
  bound_at_iterate : ∀ w,
    w ∈ sourceMultiradialPossibleImage I
      (sourceMultiradialMap I ((sourceStepXICore I).ind3 iterate consumer.base)) →
      w ≤ bound

/-- **H7/Ob9 one-sided comparison consumer:** from the assembly inputs, the H7Ob9
wiring, a base choice and an iterate bound, get the Cor 3.12 hull+det conclusion AND
the base possible-image upper bound (class A).  Every field is consumed. -/
theorem hull13_h7ob9_comparison
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullH7Ob9ComparisonInputs (l := l) M I) :
    Cor312HullDetConclusion M In.consumer.hull.theta ∧
      (∀ z, z ∈ sourceMultiradialPossibleImage I
        (sourceMultiradialMap I In.consumer.base) → z ≤ In.bound) :=
  ⟨cor312_hullDet_conditional M In.consumer.hull,
   hull12_upperBound_transfer I In.iterate In.consumer.base In.bound
     In.bound_at_iterate⟩

/-- The comparison consumer rows (class A proved vs class B named). -/
def hull13Rows : List (String × String × String) :=
  [ ("Cor 3.12 hull+det conclusion", "A", "CONSUMED S3182 cor312_hullDet_conditional")
  , ("(Ind1)/(Ind2) invariance + (Ind3) one-sided via H7Ob9 wiring", "A", "CONSUMED Hull10 hull10_h7ob9_consumer (Indet06 fields)")
  , ("upper-bound transfer from (Ind3) iterate to base", "A", "PROVED hull12_upperBound_transfer (Hull12)")
  , ("arbitrary log-link iterate independence of the comparison (deep Ob9)", "B", "NAMED; not formalized") ]

/-- The comparison consumer row record has four rows. -/
theorem hull13Rows_length : hull13Rows.length = 4 := rfl

#check HullH7Ob9ComparisonInputs
#check hull13_h7ob9_comparison
#check hull13Rows_length

end LeanFormal.IUT.XiFPaper.Hull13H7Ob9ComparisonConsumerActual
end