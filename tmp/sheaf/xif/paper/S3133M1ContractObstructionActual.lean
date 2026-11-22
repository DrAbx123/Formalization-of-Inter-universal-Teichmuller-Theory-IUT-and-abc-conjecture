import tmp.sheaf.xif.paper.S3133M1InjectionReductionActual

/-!
# M1 contract-separated obstruction record (component, not a paper object)

COMPONENT, not a paper object.  Named consumers: mainline task-20 M1, lattice
S3137 R1, hull bad/all-place compatibility, stage4 LGP family.

Source: IUT I, Definition 3.1, (b), (e) (source place selection and bad-moduli
place data); IUT III, Theorem 3.11, pp. 160-162; IUT IV, Theorem 1.10 proof,
pp. 26-27.

M1 attempt result.  The bad->all-place INJECTION is constructible from the two
index bijections (S3133M1InjectionReductionActual, PROVED).  What is NOT
constructible from the current actual data is the bad-only tensor index
equivalence e : Bad (nativePlaceSelection T) ~= C3.tensorIndex together with the
place-compatible transport FinitePlace T.arithmetic.F ~= FinitePlace
I.initial.arithmetic.Fmod.  Reason (contract-separated): the frozen OriginalInput
contract does not expose the source place-to-moduli provenance (placeToMod);
the assembled S1280 Definition 3.1 data is conditional on the paper D5-D9
clauses, and C3.tensorIndex is donor-chosen, so no canonical map Bad -> V or
Bad -> C3.tensorIndex exists.  No contract change is made.

This file records the exact contract-separated missing datum and the proved
conditional reduction.  No field is inhabited; no sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3133M1ContractObstructionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S3133S3131PlaceIndexComparisonActual
open LeanFormal.IUT.XiFPaper.S3133M1InjectionReductionActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The exact contract-separated M1 missing datum: the bad-only tensor index
equivalence together with the place-compatible all-place transport (the genuine
source placeToMod provenance that OriginalInput does not expose). -/
structure S3133M1ContractSeparatedMissing
    (placeTransport : NumberField.FinitePlace T.arithmetic.F ≃
      NumberField.FinitePlace I.initial.arithmetic.Fmod) where
  /-- the missing bad-only tensor index equivalence -/
  indexEquivalence : Bad (nativePlaceSelection T) ≃ C3.tensorIndex
  /-- exact place compatibility with the all-place transport -/
  place_agree : ∀ b : Bad (nativePlaceSelection T),
    placeTransport (nativeBadToFPlace T b) =
      (C3.tensorPlaces (indexEquivalence b) (C3.tensorTuple (indexEquivalence b))).val

/-- The contract-separated M1 datum maps to S3133M1Remaining. -/
theorem S3133M1ContractSeparatedMissing_to_M1Remaining
    (placeTransport : NumberField.FinitePlace T.arithmetic.F ≃
      NumberField.FinitePlace I.initial.arithmetic.Fmod)
    (h : Nonempty (S3133M1ContractSeparatedMissing T C3 placeTransport)) :
    S3133M1Remaining T C3 placeTransport := by
  obtain ⟨D⟩ := h
  exact ⟨⟨D.indexEquivalence, D.place_agree⟩⟩

/-- S3133M1Remaining gives the contract-separated M1 datum. -/
theorem S3133M1Remaining_to_contractSeparatedMissing
    (placeTransport : NumberField.FinitePlace T.arithmetic.F ≃
      NumberField.FinitePlace I.initial.arithmetic.Fmod)
    (h : S3133M1Remaining T C3 placeTransport) :
    Nonempty (S3133M1ContractSeparatedMissing T C3 placeTransport) := by
  obtain ⟨⟨e, hagree⟩⟩ := h
  exact ⟨{ indexEquivalence := e, place_agree := hagree }⟩

/-- The contract-separated M1 datum is equivalent to S3133M1Remaining. -/
theorem S3133M1ContractSeparatedMissing_iff_M1Remaining
    (placeTransport : NumberField.FinitePlace T.arithmetic.F ≃
      NumberField.FinitePlace I.initial.arithmetic.Fmod) :
    Nonempty (S3133M1ContractSeparatedMissing T C3 placeTransport) ↔
      S3133M1Remaining T C3 placeTransport :=
  ⟨S3133M1ContractSeparatedMissing_to_M1Remaining T C3 placeTransport,
    S3133M1Remaining_to_contractSeparatedMissing T C3 placeTransport⟩

end LeanFormal.IUT.XiFPaper.S3133M1ContractObstructionActual
