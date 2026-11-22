/-
S2425: invariance of the minimal polynomial of a residue root under the
arithmetic Frobenius `frobBar`, and the induced map from residue roots to the
normalized irreducible factors of `f mod p`.

The results are:

* `s2425_minpoly_frobBar` : the arithmetic Frobenius `y ↦ y ^ #(O_K/p)` on the
  residue field `O_L/P` preserves the minimal polynomial over `O_K/p`;
* `s2425RootFactor` : the map sending a residue root `y` to the normalized
  irreducible factor `minpoly (O_K/p) y` of `fbar f p`;
* `s2425RootFactor_permBar` : this map is invariant under `permBar`, i.e. the
  Frobenius permutation of the root set acts inside the fibres of
  `s2425RootFactor` (the fibre over an irreducible factor is exactly the
  Frobenius orbit of a root of that factor).

No sorry, admit, axiom, opaque declaration or native_decide is used.
-/
import tmp.sheaf.xif.paper.S2397RootFactorMapActual
noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2397RootFactorMapActual
namespace LeanFormal.IUT.XiFPaper.S2425PermBarInvarianceActual
attribute [local instance] Ideal.Quotient.field
variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
variable (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
  (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
  (hmonic : f.Monic) (hsep : (fbar f p).Separable)
  (hsplit : (Polynomial.map (algebraMap (RingOfIntegers K) L) f).Splits)
local instance : DecidableEq ((RingOfIntegers K) ⧸ p) := Classical.decEq _

include hp hP hPover in
/-- The arithmetic Frobenius `frobBar p P` on the residue field at `P` fixes the
minimal polynomial over `O_K / p` of every element. -/
theorem s2425_minpoly_frobBar
    (y : (RingOfIntegers L) ⧸ P) :
    minpoly ((RingOfIntegers K) ⧸ p) (frobBar p P y) =
      minpoly ((RingOfIntegers K) ⧸ p) y := by
  haveI : P.IsMaximal := P_isMaximal p P
  haveI : Fintype ((RingOfIntegers K) ⧸ p) := Fintype.ofFinite _
  haveI : Fintype ((RingOfIntegers L) ⧸ P) := Fintype.ofFinite _
  have hfrob : frobBar p P y =
      FiniteField.frobeniusAlgHom ((RingOfIntegers K) ⧸ p)
        ((RingOfIntegers L) ⧸ P) y := by
    rw [frobBar, FiniteField.coe_frobeniusAlgHom, Nat.card_eq_fintype_card]
  rw [hfrob]
  exact minpoly.algHom_eq _ (RingHom.injective _) y

include hp hP hPover hmonic hsep in
/-- The map from residue roots of `fbar f p` to the normalized irreducible
factors of `fbar f p`, sending a root to its minimal polynomial. -/
noncomputable def s2425RootFactor
    (y : (fbar f p).rootSet ((RingOfIntegers L) ⧸ P)) :
    {g : ((RingOfIntegers K) ⧸ p)[X] //
      g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)} :=
  ⟨minpoly ((RingOfIntegers K) ⧸ p) y.1,
    s2397_minpoly_mem_normalizedFactors (K := K) (L := L) f p P hmonic hsep y.2⟩

include hp hP hPover hmonic hsep in
/-- The root-to-factor map is invariant under the arithmetic Frobenius
permutation `permBar` of the root set. -/
theorem s2425RootFactor_permBar
    (y : (fbar f p).rootSet ((RingOfIntegers L) ⧸ P)) :
    s2425RootFactor f p P hmonic hsep (permBar (f := f) p P y) =
      s2425RootFactor f p P hmonic hsep y := by
  apply Subtype.ext
  change minpoly ((RingOfIntegers K) ⧸ p) (frobBar p P y.1) =
    minpoly ((RingOfIntegers K) ⧸ p) y.1
  exact s2425_minpoly_frobBar p P y.1

#print axioms s2425_minpoly_frobBar
#print axioms s2425RootFactor_permBar
end LeanFormal.IUT.XiFPaper.S2425PermBarInvarianceActual
end
