/-
S2470: the fibre of the root-to-factor map over a normalized irreducible factor
of `f mod p` is in bijection with the set of residue roots of that factor, hence
its cardinality is the degree of the factor.

The main results are:

* `s2470FiberEquiv` : for a normalized irreducible factor `b` of `fbar f p`, the
  fibre of `s2425RootFactor` over `b` is equivalent to the set of `y` in the
  residue field `O_L / P` with `minpoly (O_K / p) y = b`;
* `s2470Fiber_card` : this fibre has `b.natDegree` elements.

No sorry, admit, axiom, opaque declaration or native_decide is used.
-/
import tmp.sheaf.xif.paper.S2425PermBarInvarianceActual
import tmp.sheaf.xif.paper.S2408FiberSizesActual
import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual

noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2339FbarFactorsActual
open LeanFormal.IUT.XiFPaper.S2397RootFactorMapActual
open LeanFormal.IUT.XiFPaper.S2408FiberSizesActual
open LeanFormal.IUT.XiFPaper.S2425PermBarInvarianceActual
namespace LeanFormal.IUT.XiFPaper.S2470FiberEquivActual
attribute [local instance] Ideal.Quotient.field
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
variable (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
  (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
  (hmonic : f.Monic) (hsep : (fbar f p).Separable)
  (hsplit : (Polynomial.map (algebraMap (RingOfIntegers K) L) f).Splits)
local instance : DecidableEq ((RingOfIntegers K) ⧸ p) := Classical.decEq _

include hp hP hPover hmonic hsep in
/-- The fibre of the root-to-factor map `s2425RootFactor` over a normalized
irreducible factor `b` of `fbar f p` is equivalent to the set of residue
elements whose minimal polynomial is `b`. -/
noncomputable def s2470FiberEquiv
    (b : {g : ((RingOfIntegers K) ⧸ p)[X] //
      g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)}) :
    {x : (fbar f p).rootSet ((RingOfIntegers L) ⧸ P) //
      s2425RootFactor f p P hmonic hsep x = b} ≃
    {y : (RingOfIntegers L) ⧸ P //
      minpoly ((RingOfIntegers K) ⧸ p) y = b.1} where
  toFun x := ⟨x.1.1, by
    have h := congrArg Subtype.val x.2
    simpa [s2425RootFactor] using h⟩
  invFun y :=
    let rootproof : y.1 ∈ (fbar f p).rootSet ((RingOfIntegers L) ⧸ P) := by
      rw [Polynomial.mem_rootSet']
      have hb := (Polynomial.mem_normalizedFactors_iff (p := b.1) (q := fbar f p)
        (s2397Fbar_ne_zero f p P hmonic)).mp b.2
      have hroot : (Polynomial.aeval y.1) b.1 = 0 := by
        rw [← y.2]
        exact minpoly.aeval _ _
      have hyeval :
          (b.1.map (algebraMap ((RingOfIntegers K) ⧸ p)
            ((RingOfIntegers L) ⧸ P))).eval y.1 = 0 := by
        rw [Polynomial.eval_map]
        rwa [Polynomial.aeval_def] at hroot
      have hdvd :
          b.1.map (algebraMap ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P)) ∣
            (fbar f p).map (algebraMap ((RingOfIntegers K) ⧸ p)
              ((RingOfIntegers L) ⧸ P)) :=
        Polynomial.map_dvd _ hb.2.2
      obtain ⟨q, hq⟩ := hdvd
      exact ⟨(s2397Fbar_monic f p P hmonic).map _ |>.ne_zero, by
        rw [Polynomial.aeval_def, ← Polynomial.eval_map, hq, Polynomial.eval_mul,
          hyeval, zero_mul]⟩
    ⟨⟨y.1, rootproof⟩, by
      apply Subtype.ext
      exact y.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv y := by
    apply Subtype.ext
    rfl

include hp hP hPover hmonic hsep hsplit in
/-- The fibre of the root-to-factor map over a normalized irreducible factor has
as many elements as the degree of that factor. -/
theorem s2470Fiber_card
    (b : {g : ((RingOfIntegers K) ⧸ p)[X] //
      g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)}) :
    Fintype.card {x : (fbar f p).rootSet ((RingOfIntegers L) ⧸ P) //
      s2425RootFactor f p P hmonic hsep x = b} = b.1.natDegree := by
  classical
  rw [← Nat.card_eq_fintype_card]
  rw [Nat.card_congr (s2470FiberEquiv (K := K) (L := L) f p P hmonic hsep b)]
  have hset : Nat.card {y : (RingOfIntegers L) ⧸ P //
      minpoly ((RingOfIntegers K) ⧸ p) y = b.1} =
      (s2408FiberSet (K := K) (L := L) (p := p) (P := P) b.1).ncard :=
    Nat.card_coe_set_eq _
  rw [hset]
  exact s2408FiberSet_ncard (K := K) (L := L) (f := f) (hmonic := hmonic)
    (hsep := hsep) (hsplit := hsplit) (p := p) (P := P) (hg := b.2)

#print axioms s2470FiberEquiv
#print axioms s2470Fiber_card
end LeanFormal.IUT.XiFPaper.S2470FiberEquivActual
end
