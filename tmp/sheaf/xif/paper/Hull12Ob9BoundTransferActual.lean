import tmp.sheaf.xif.paper.Indet06H7Ob9WiringActual
import tmp.sheaf.xif.paper.S3182Cor312HullDetAssemblyActual
import tmp.sheaf.xif.paper.S3136ModelSourceClauseActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: Ob9|comparison|possible image|upper bound|Ind3 one-sided|log-link iterate -> hits Indet05RouteMultiradialClassActual:40-113 (routeMultiradial_ind3_possibleImage_upper), Indet06H7Ob9WiringActual:47-106 (H7Ob9IndetWiring), S3182Cor312HullDetAssemblyActual -> REUSE (class A: one-sided transfer of possible-image upper bounds from (Ind3) iterates back to the base class representative; no re-proof).

# [Hull] 12: H7/Ob9 one-sided upper-bound transfer (class A consequence)

Corpus: IUT III Remark 3.9.4 (~7151); Step (xi) 10750-10987; conclusion 10897.
CONTENT (class A): (Ind3) is one-sided: every point z of the base possible-image
is dominated by some point w of an (Ind3)-iterate possible-image.  Hence an UPPER
bound at an (Ind3) iterate transfers back to the base representative (the direction
that matters for the Cor 3.12 comparison, which is an upper bound).  Combined with
the hull+det assembly this gives the one-sided compatibility statement.
HONESTY: the deep statement that ARBITRARY log-link iterates do not affect the
comparison remains class-B named (as in Hull08/Hull10); only this proved one-sided
transfer is class A.  Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Hull12Ob9BoundTransferActual

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
open LeanFormal.IUT.XiFPaper.S3182Cor312HullDetAssemblyActual

variable {l : PrimeGeFive} {V : Type uv}

/-- **One-sided upper-bound transfer:** if the possible-image readout is bounded by B
at an (Ind3) n-iterate of c, then it is bounded by B at c (class A). -/
theorem hull12_upperBound_transfer
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (n : Nat) (c : SourceStepXIChoice I) (B : ℝ)
    (hB : ∀ w, w ∈ sourceMultiradialPossibleImage I
      (sourceMultiradialMap I ((sourceStepXICore I).ind3 n c)) → w ≤ B) :
    ∀ z, z ∈ sourceMultiradialPossibleImage I (sourceMultiradialMap I c) → z ≤ B := by
  intro z hz
  obtain ⟨w, hw, hzw⟩ :=
    routeMultiradial_ind3_possibleImage_upper I n c z hz
  exact le_trans hzw (hB w hw)

/-- The transfer packaged for a chosen base representative. -/
theorem hull12_upperBound_transfer_base
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (n : Nat) (rep : RouteMultiradialUpTo I) (B : ℝ)
    (hB : ∀ w, w ∈ sourceMultiradialPossibleImage I
      (sourceMultiradialMap I ((sourceStepXICore I).ind3 n rep.representative)) → w ≤ B) :
    ∀ z, z ∈ sourceMultiradialPossibleImage I
      (sourceMultiradialMap I rep.representative) → z ≤ B :=
  hull12_upperBound_transfer I n rep.representative B hB

/-- H7/Ob9 one-sided row record. -/
def hull12Rows : List (String × String × String) :=
  [ ("(Ind3) possible-image upper-semi", "A", "REUSED Indet05 routeMultiradial_ind3_possibleImage_upper")
  , ("upper-bound transfer from (Ind3) iterate to base", "A", "PROVED hull12_upperBound_transfer (class A)")
  , ("base-representative package", "A", "PROVED hull12_upperBound_transfer_base (class A)")
  , ("arbitrary log-link iterate independence of the comparison (deep Ob9)", "B", "NAMED; not formalized (only one-sided laws class A)") ]

/-- The one-sided transfer row record has four rows. -/
theorem hull12Rows_length : hull12Rows.length = 4 := rfl

#check hull12_upperBound_transfer
#check hull12_upperBound_transfer_base
#check hull12Rows_length

end LeanFormal.IUT.XiFPaper.Hull12Ob9BoundTransferActual
end