import tmp.sheaf.xif.paper.Indet06H7Ob9WiringActual
import tmp.sheaf.xif.paper.S3182Cor312HullDetAssemblyActual
import tmp.sheaf.xif.paper.S3136ModelSourceClauseActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: H7/Ob9|log-link iterate|Indet chain|H7Ob9IndetWiring|comparison invariance -> hits Indet06H7Ob9WiringActual:47-106 (H7Ob9IndetWiring, h7Ob9IndetWiring, h7Ob9_comparison_ind1_invariant/ind2_invariant/ind3_one_sided, h7Ob9ConsumerInterface), Indet05RouteMultiradialClassActual, S3182Cor312HullDetAssemblyActual -> REUSE (hull-side consumer of the authoritative H7/Ob9 wiring interface; no re-proof).

# [Hull] 10: H7/Ob9 hull-side consumer of the Indet chain wiring (class A consumer)

Corpus: IUT III Remark 3.9.4 (corpus ~7151: elementary log-link compatibility);
Step (xi) corpus 10750-10987; Cor 3.12 statement corpus 10324-10353; conclusion 10897.
CONTENT: consumes stepxi's authoritative H7/Ob9 wiring (Indet06) together with the
hull+det assembly (S3182): gives the Cor 3.12 hull+det conclusion AND (Ind1)/(Ind2)
invariance AND (Ind3) one-sided upper-semi behavior of the comparison readout at
the chosen base choice and at its permissible log-link iterates.
Every input field is consumed.  HONESTY: the deep statement that ARBITRARY
log-link iterates do not affect the comparison remains class-B named; only the
PROVED Indet-chain invariance/one-sidedness laws are class A here.  Registry
frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Hull10H7Ob9ConsumerActual

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

variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- Hull-side H7/Ob9 consumer inputs: the hull+det assembly inputs, the
authoritative H7Ob9 wiring (Indet06), and a chosen base source choice. -/
structure HullH7Ob9ConsumerInputs
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  hull : HullDetAssemblyInputs M
  wiring : H7Ob9IndetWiring I
  base : SourceStepXIChoice I

/-- **H7/Ob9 hull-side consumer:** from the assembly inputs, the H7Ob9 wiring and a
base choice, get the Cor 3.12 hull+det conclusion AND the (Ind1)/(Ind2)
invariance AND the (Ind3) one-sided upper-semi statement at the base choice.
Every field is consumed. -/
theorem hull10_h7ob9_consumer
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullH7Ob9ConsumerInputs (l := l) M I)
    (g : SourceStepXILabel) (n : Nat) (z : ℝ)
    (hz : z ∈ sourceMultiradialPossibleImage I
      (sourceMultiradialMap I In.base)) :
    Cor312HullDetConclusion M In.hull.theta ∧
      sourceMultiradialMap I ((sourceStepXICore I).ind1 g In.base) =
        sourceMultiradialMap I In.base ∧
      sourceMultiradialMap I ((sourceStepXICore I).ind2 g In.base) =
        sourceMultiradialMap I In.base ∧
      (∃ w, w ∈ sourceMultiradialPossibleImage I
        (sourceMultiradialMap I ((sourceStepXICore I).ind3 n In.base)) ∧ z ≤ w) :=
  ⟨cor312_hullDet_conditional M In.hull,
   In.wiring.ind1_invariant g In.base,
   In.wiring.ind2_invariant g In.base,
   In.wiring.ind3_one_sided n In.base z hz⟩

/-- The H7Ob9 wiring also exposes the permissible log-link iterate family, which is
the (Ind3) vertical iterate of the source base choice (class A consumer row). -/
theorem hull10_logLinkIterate_eq
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Nat) :
    (h7Ob9IndetWiring I).logLinkIterate n =
      (sourceStepXICore I).ind3 n (SourceStepXIBase I) :=
  rfl

/-- Hull-side H7/Ob9 consumer rows (class A proved vs class B named). -/
def hull10H7Ob9Rows : List (String × String) :=
  [ ("(Ind1) invariance of comparison readout", "CONSUMED via H7Ob9IndetWiring.ind1_invariant (PROVED)")
  , ("(Ind2) invariance of comparison readout", "CONSUMED via H7Ob9IndetWiring.ind2_invariant (PROVED)")
  , ("(Ind3) one-sided upper-semi possible image", "CONSUMED via H7Ob9IndetWiring.ind3_one_sided (PROVED)")
  , ("permissible log-link iterate family", "CONSUMED via H7Ob9IndetWiring.logLinkIterate (PROVED definition)")
  , ("Cor 3.12 hull+det conclusion", "CONSUMED via S3182 cor312_hullDet_conditional")
  , ("arbitrary log-link iterate independence of the comparison (deep Ob9)", "CLASS-B NAMED; only class-level/one-sided laws formalized")
  , ("corpus", "Rem 3.9.4 ~7151; Step (xi) 10750-10987; conclusion 10897") ]

/-- The H7/Ob9 consumer row record has seven rows. -/
theorem hull10H7Ob9Rows_length : hull10H7Ob9Rows.length = 7 := rfl

#check HullH7Ob9ConsumerInputs
#check hull10_h7ob9_consumer
#check hull10_logLinkIterate_eq
#check hull10H7Ob9Rows_length

end LeanFormal.IUT.XiFPaper.Hull10H7Ob9ConsumerActual
end