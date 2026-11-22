import tmp.sheaf.xif.paper.S2425PermBarInvarianceActual
import tmp.sheaf.xif.paper.S2408FiberSizesActual
import tmp.sheaf.xif.paper.S2428FilterBridgeActual
import tmp.sheaf.xif.paper.S2440RootPermCycleCleanActual
noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2397RootFactorMapActual
open LeanFormal.IUT.XiFPaper.S2408FiberSizesActual
open LeanFormal.IUT.XiFPaper.S2425PermBarInvarianceActual
open LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual
namespace LeanFormal.IUT.XiFPaper.S2446D5FinalActual
attribute [local instance] Ideal.Quotient.field
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
variable (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
  (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
  (hmonic : f.Monic) (hsep : (fbar f p).Separable)
  (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)
local instance : DecidableEq ((RingOfIntegers K) ⧸ p) := Classical.decEq _
include hp hP hPover hmonic hsep in
noncomputable def s2446FiberEquiv
    (b : {g : ((RingOfIntegers K) ⧸ p)[X] //
      g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)}) :
    {x : (fbar f p).rootSet ((RingOfIntegers L) ⧸ P) //
      s2425RootFactor f p P hmonic hsep x = b} ≃
    {y : (RingOfIntegers L) ⧸ P //
      minpoly ((RingOfIntegers K) ⧸ p) y = b.1} := by
  classical
  haveI : P.IsMaximal := P_isMaximal p P
  have hb := (Polynomial.mem_normalizedFactors_iff (s2397Fbar_ne_zero f p P hmonic)).mp b.2
  obtain ⟨hb_irr, hb_monic, hb_dvd⟩ := hb
  have hroot : ∀ y : (RingOfIntegers L) ⧸ P,
      minpoly ((RingOfIntegers K) ⧸ p) y = b.1 →
      y ∈ (fbar f p).rootSet ((RingOfIntegers L) ⧸ P) := by
    intro y hy
    have haeval : (Polynomial.aeval y) b.1 = 0 := by
      rw [← hy]
      exact minpoly.aeval _ _
    have hfb : (Polynomial.aeval y) (fbar f p) = 0 := by
      rcases hb_dvd with ⟨q, hq⟩
      rw [hq, Polynomial.aeval_mul, haeval, zero_mul]
    rw [Polynomial.mem_rootSet']
    exact ⟨(s2397Fbar_monic f p P hmonic).map
      (algebraMap ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P)) |>.ne_zero, hfb⟩
  refine ⟨fun x => ⟨x.1.1, ?_⟩, fun y => ⟨⟨y.1, hroot y y.2⟩, ?_⟩, ?_, ?_⟩
  · exact (congrArg Subtype.val x.2)
  · apply Subtype.ext
    exact y.2
  · intro x
    apply Subtype.ext
    rfl
  · intro y
    apply Subtype.ext
    rfl
include hp hP hPover hmonic hsep hsplit in
theorem s2446Fiber_card
    (b : {g : ((RingOfIntegers K) ⧸ p)[X] //
      g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)}) :
    Fintype.card {x : (fbar f p).rootSet ((RingOfIntegers L) ⧸ P) //
      s2425RootFactor f p P hmonic hsep x = b} = b.1.natDegree := by
  classical
  haveI : P.IsMaximal := P_isMaximal p P
  rw [← Nat.card_eq_fintype_card]
  rw [Nat.card_congr (s2446FiberEquiv K L f p P hmonic hsep b)]
  change (s2408FiberSet (K := K) (L := L) (p := p) (P := P) b.1).ncard = b.1.natDegree
  exact s2408FiberSet_ncard K L f p P hmonic hsep hsplit b.2
#print axioms s2446FiberEquiv
#print axioms s2446Fiber_card
end LeanFormal.IUT.XiFPaper.S2446D5FinalActual
end
