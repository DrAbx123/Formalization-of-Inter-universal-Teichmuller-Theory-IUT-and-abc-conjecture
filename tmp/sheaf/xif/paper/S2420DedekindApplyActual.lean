import tmp.sheaf.xif.paper.S2408FiberSizesActual
noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2397RootFactorMapActual
open LeanFormal.IUT.XiFPaper.S2408FiberSizesActual
namespace LeanFormal.IUT.XiFPaper.S2420DedekindApplyActual
attribute [local instance] Ideal.Quotient.field
variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
variable (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
  (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
  (hmonic : f.Monic) (hsep : (fbar f p).Separable)
  (hsplit : (Polynomial.map (algebraMap (RingOfIntegers K) L) f).Splits)
local instance : DecidableEq ((RingOfIntegers K) ⧸ p) := Classical.decEq _
include hp hP hPover in
theorem s2420_minpoly_frobBar
    (y : (RingOfIntegers L) ⧸ P) :
    minpoly ((RingOfIntegers K) ⧸ p) (frobBar p P y) =
      minpoly ((RingOfIntegers K) ⧸ p) y := by
  haveI : P.IsMaximal := P_isMaximal p P
  haveI : Fintype ((RingOfIntegers K) ⧸ p) := Fintype.ofFinite _
  haveI : Fintype ((RingOfIntegers L) ⧸ P) := Fintype.ofFinite _
  have hfrob : frobBar p P y =
      FiniteField.frobeniusAlgHom ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P) y := by
    rw [frobBar, FiniteField.coe_frobeniusAlgHom, Nat.card_eq_fintype_card]
  rw [hfrob]
  exact minpoly.algHom_eq _ (RingHom.injective _) y
include hp hP hPover hmonic hsep in
/-- The root-to-normalized-factor map on residue roots. -/
noncomputable def s2420RootFactor (hsep' : (fbar f p).Separable)
    (y : (fbar f p).rootSet ((RingOfIntegers L) ⧸ P)) :
    {g : ((RingOfIntegers K) ⧸ p)[X] //
      g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)} :=
  ⟨minpoly ((RingOfIntegers K) ⧸ p) y.1,
    s2397_minpoly_mem_normalizedFactors (K := K) (L := L) f p P hmonic hsep' y.2⟩
include hp hP hPover hmonic hsep in
theorem s2420RootFactor_permBar
    (hsep' : (fbar f p).Separable)
    (y : (fbar f p).rootSet ((RingOfIntegers L) ⧸ P)) :
    s2420RootFactor f p P hmonic hsep'
      (permBar (f := f) p P y) =
      s2420RootFactor f p P hmonic hsep' y := by
  apply Subtype.ext
  change minpoly ((RingOfIntegers K) ⧸ p) (frobBar p P y.1) =
    minpoly ((RingOfIntegers K) ⧸ p) y.1
  exact s2420_minpoly_frobBar (K := K) (L := L) (p := p) (P := P) y.1
#print axioms s2420_minpoly_frobBar
#print axioms s2420RootFactor_permBar
end LeanFormal.IUT.XiFPaper.S2420DedekindApplyActual
end
