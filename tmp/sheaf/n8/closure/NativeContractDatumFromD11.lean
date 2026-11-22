import tmp.sheaf.n8.closure.C1BridgeProof
import tmp.sheaf.n8.closure.NativeC3
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31PlacePartition

/-! # Native contract datum from the d11 entry data

The explicit d11 source-input package (place selection, bad-place reduction cards, torsion/orbicurve/section/cusp clauses and compatibility proofs) assembles a SourceDefinition31Data over the native arithmetic root, hence NativeContractDatumExists X.

SEMANTIC NOTE: nativeD11PlaceSelection is the singleton selection at nativeBadBasePlace, not the full native V_mod_bad selection. It satisfies only the weak NativeContractDatumExists interface (arithmetic root equality); it is not the paper-level native contract. See coord/C1-SINGLETON-SEMANTICS.md.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.InitialThetaSource.Definition31PlacePartition
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C1BridgeProof

variable {l : PrimeGeFive} (X : N8NativeInput l)

theorem nativeContractDatumExists_of_d11Entry
    (P : SourcePlaceSelection X.S.arithmetic)
    [Fintype (Bad P)]
    (C : BadPlaceReductionCards P)
    (T : Theorem311Source.SourceTorsionClause.{0, 0, 0} l)
    (O : Theorem311Source.SourceOrbicurveClause.{0, 0, 0})
    (Se : Theorem311Source.SourceSectionClause.{0, 0, 0})
    (Cu : Theorem311Source.SourceCuspClause)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    NativeContractDatumExists X :=
  ⟨d11EntryData P C T O Se Cu redCompat hredCompat torCompat htorCompat
    orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat, rfl⟩

/-- Actual singleton d11 place selection from the native bad base place. -/
noncomputable def nativeD11PlaceSelection : SourcePlaceSelection X.S.arithmetic :=
  SourcePlaceSelection.singleton X.S.arithmetic (nativeBadBasePlace X)
    (X.S.tuple.source.V_mod_bad_odd_residue_characteristic
      (nativeBadBasePlace X) (nativeBadBasePlace_mem X))

/-- Contract datum from the actual native bad-place selection plus the remaining d11 data. -/
theorem nativeContractDatumExists_of_nativePlaceSelection
    [Fintype (Bad (nativeD11PlaceSelection X))]
    (C : BadPlaceReductionCards (nativeD11PlaceSelection X))
    (T : Theorem311Source.SourceTorsionClause.{0, 0, 0} l)
    (O : Theorem311Source.SourceOrbicurveClause.{0, 0, 0})
    (Se : Theorem311Source.SourceSectionClause.{0, 0, 0})
    (Cu : Theorem311Source.SourceCuspClause)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    NativeContractDatumExists X :=
  nativeContractDatumExists_of_d11Entry X (nativeD11PlaceSelection X) C T O Se Cu
    redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat

/-- The bad set of the singleton native selection is a singleton subtype. -/
noncomputable def badNativeD11PlaceEquiv : Bad (nativeD11PlaceSelection X) ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨nativeBadBasePlace X, by
    simp [nativeD11PlaceSelection, SourcePlaceSelection.singleton]⟩
  left_inv q := by
    apply Subtype.ext
    have hmem : (↑q : NumberField.FinitePlace X.S.arithmetic.Fmod) ∈
        ({nativeBadBasePlace X} : Set (NumberField.FinitePlace X.S.arithmetic.Fmod)) := by
      simpa [nativeD11PlaceSelection, SourcePlaceSelection.singleton] using q.2
    exact (Set.mem_singleton_iff.mp hmem).symm
  right_inv _ := rfl

/-- Fintype instance for the bad set of the singleton native selection. -/
@[reducible] noncomputable def badNativeD11Fintype : Fintype (Bad (nativeD11PlaceSelection X)) :=
  Fintype.ofEquiv Unit (badNativeD11PlaceEquiv X).symm

/-- Contract datum from the singleton native place selection, with its bad-set Fintype now constructed. -/
theorem nativeContractDatumExists_of_nativeD11Data
    (C : BadPlaceReductionCards (nativeD11PlaceSelection X))
    (T : Theorem311Source.SourceTorsionClause.{0, 0, 0} l)
    (O : Theorem311Source.SourceOrbicurveClause.{0, 0, 0})
    (Se : Theorem311Source.SourceSectionClause.{0, 0, 0})
    (Cu : Theorem311Source.SourceCuspClause)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    NativeContractDatumExists X := by
  letI := badNativeD11Fintype X
  exact nativeContractDatumExists_of_nativePlaceSelection X C T O Se Cu
    redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat

/-- Contract datum from a split-multiplicative reduction card; the remaining reduction cards are derived. -/
theorem nativeContractDatumExists_of_nativeD11Split
    (split : ∀ w : NumberField.FinitePlace X.S.arithmetic.F,
      NumberFieldFinitePlace.comap (k := X.S.arithmetic.Fmod) w ∈
        (nativeD11PlaceSelection X).V_mod_bad →
      X.S.arithmetic.curve.HasSplitMultiplicativeReductionAt w)
    (T : Theorem311Source.SourceTorsionClause.{0, 0, 0} l)
    (O : Theorem311Source.SourceOrbicurveClause.{0, 0, 0})
    (Se : Theorem311Source.SourceSectionClause.{0, 0, 0})
    (Cu : Theorem311Source.SourceCuspClause)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    NativeContractDatumExists X :=
  nativeContractDatumExists_of_nativeD11Data X
    (BadPlaceReductionCards.ofSplitMultiplicative split) T O Se Cu
    redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat

end LeanFormal.IUT.N8Closure.C1Actual
end