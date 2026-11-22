import tmp.sheaf.xif.paper.S2454D5FinalIntegrationActual
import tmp.sheaf.xif.paper.S2428FilterBridgeActual
noncomputable section
set_option maxHeartbeats 4000000
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2397RootFactorMapActual
open LeanFormal.IUT.XiFPaper.S2425PermBarInvarianceActual
open LeanFormal.IUT.XiFPaper.S2446D5FinalActual
open LeanFormal.IUT.XiFPaper.S2453BetaTransitiveActual
open LeanFormal.IUT.XiFPaper.S2454D5FinalIntegrationActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2408FiberSizesActual
open LeanFormal.IUT.XiFPaper.S2428FilterBridgeActual
open LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual
namespace LeanFormal.IUT.XiFPaper.S2456D5FinalActual
attribute [local instance] Ideal.Quotient.field
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
variable (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
  (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
  (hmonic : f.Monic) (hsep : (fbar f p).Separable)
  (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)
local instance : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
  IsIntegralClosure.MulSemiringAction (RingOfIntegers K) K L (RingOfIntegers L)
local instance : SMulCommClass Gal(L/K) (RingOfIntegers K) (RingOfIntegers L) :=
  LeanFormal.IUT.XiFPaper.S2381SmulCommActual.S2381_smulCommClass
local instance : DecidableEq ((RingOfIntegers K) ⧸ p) := Classical.decEq _
abbrev s2456M : Multiset ((RingOfIntegers K) ⧸ p)[X] :=
  UniqueFactorizationMonoid.normalizedFactors (fbar f p)
abbrev s2456S : Finset ((RingOfIntegers K) ⧸ p)[X] := (s2456M K f p).toFinset
abbrev s2456Beta : Type := {g : ((RingOfIntegers K) ⧸ p)[X] // g ∈ s2456S K f p}
include hp hP hPover hmonic in
noncomputable def s2456BetaFintype : Fintype (s2456Beta K f p) :=
  Fintype.ofFinset (s2456S K f p) (p := {x | x ∈ s2456S K f p}) (by intro x; simp)
include hp hP hPover hmonic in
theorem s2456Beta_univ : (Finset.univ : Finset (s2456Beta K f p)) = (s2456S K f p).attach := rfl
include hp hP hPover hmonic hsep in
theorem s2456M_nodup : (s2456M K f p).Nodup :=
  (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors (s2397Fbar_ne_zero f p P hmonic)).mp hsep.squarefree
include hp hP hPover hmonic hsep in
theorem s2456S_val : (s2456S K f p).val = s2456M K f p := by
  have hnodup : (s2456M K f p).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
      (s2397Fbar_ne_zero f p P hmonic)).mp hsep.squarefree
  rw [s2456S, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
include hp hP hPover hmonic hsep in
theorem s2456_normalization :
    ((Finset.univ.filter (fun b : s2456Beta K f p => 2 ≤ b.1.natDegree)).val.map
      (fun b => b.1.natDegree)) =
      ((s2456M K f p).map Polynomial.natDegree).filter (fun n => 2 ≤ n) := by
  classical
  change ((s2456S K f p).attach.filter (fun b => 2 ≤ b.1.natDegree)).val.map
      (fun b => b.1.natDegree) =
    ((s2456M K f p).map Polynomial.natDegree).filter (fun n => 2 ≤ n)
  rw [Finset.filter_val]
  have hnodup : (s2456M K f p).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
      (s2397Fbar_ne_zero f p P hmonic)).mp hsep.squarefree
  have hsval : (s2456S K f p).val = s2456M K f p := by
    rw [s2456S, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
  change Multiset.map (fun b : s2456Beta K f p => b.1.natDegree)
      (Multiset.filter ((fun n : Nat => 2 ≤ n) ∘ (fun b : s2456Beta K f p => b.1.natDegree))
        ((s2456S K f p).attach.val)) = _
  rw [← Multiset.filter_map (s := (s2456S K f p).attach.val)
    (f := fun b => b.1.natDegree) (p := fun n => 2 ≤ n)]
  change Multiset.filter (fun n : Nat => 2 ≤ n)
      (Multiset.map (Polynomial.natDegree ∘ Subtype.val) ((s2456S K f p).attach.val)) = _
  rw [← Multiset.map_map]
  change Multiset.filter (fun n : Nat => 2 ≤ n)
      (Multiset.map Polynomial.natDegree
        (Multiset.map (fun x : {x // x ∈ (s2456S K f p).val} => x.1)
          (Multiset.attach (s2456S K f p).val))) = _
  rw [Multiset.attach_map_val]
  rw [hsval]

include hp hP hPover hmonic hsep in
noncomputable def s2456Map (x : (fbar f p).rootSet ((RingOfIntegers L) ⧸ P)) :
    s2456Beta K f p :=
  ⟨(s2425RootFactor f p P hmonic hsep x).1, by
    rw [s2456S, Multiset.mem_toFinset]
    exact (s2425RootFactor f p P hmonic hsep x).2⟩

include hp hP hPover hmonic hsep in
noncomputable def s2456BM (b : s2456Beta K f p) :
    {g : ((RingOfIntegers K) ⧸ p)[X] //
      g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)} :=
  ⟨b.1, by
    rw [← Multiset.mem_toFinset]
    exact b.2⟩

include hp hP hPover hmonic hsep hsplit in
theorem s2456Fiber_card (b : s2456Beta K f p) :
    Fintype.card {x : (fbar f p).rootSet ((RingOfIntegers L) ⧸ P) //
      s2456Map K L f p P hmonic hsep x = b} = b.1.natDegree := by
  classical
  haveI : P.IsMaximal := P_isMaximal p P
  have he : {x : (fbar f p).rootSet ((RingOfIntegers L) ⧸ P) //
      s2456Map K L f p P hmonic hsep x = b} ≃
      {x : (fbar f p).rootSet ((RingOfIntegers L) ⧸ P) //
        s2425RootFactor f p P hmonic hsep x = (s2456BM K f p b)} := by
    refine Equiv.subtypeEquivRight ?_
    intro x
    constructor
    · intro hx
      apply Subtype.ext
      simpa [s2456Map, s2456BM] using congrArg Subtype.val hx
    · intro hx
      apply Subtype.ext
      simpa [s2456Map, s2456BM] using congrArg Subtype.val hx
  rw [Fintype.card_congr he]
  exact s2446Fiber_card K L f p P hmonic hsep hsplit (s2456BM K f p b)

include hp hP hPover hmonic hsep hsplit in
theorem s2456Fibre_transitive (b : s2456Beta K f p)
    (x y : (fbar f p).rootSet ((RingOfIntegers L) ⧸ P))
    (hx : s2456Map K L f p P hmonic hsep x = b)
    (hy : s2456Map K L f p P hmonic hsep y = b) :
    (permBar (f := f) p P).SameCycle x y := by
  apply s2453Fibre_transitive K L f p P hmonic hsep hsplit
    (s2456BM K f p b) x y
  · apply Subtype.ext; simpa [s2456Map, s2456BM] using congrArg Subtype.val hx
  · apply Subtype.ext; simpa [s2456Map, s2456BM] using congrArg Subtype.val hy

include hp hP hPover hmonic hsep hsplit in
theorem s2456PermBar_cycleType :
    (permBar (f := f) p P).cycleType =
      ((s2456M K f p).map Polynomial.natDegree).filter (fun n => 2 ≤ n) := by
  classical
  haveI : P.IsMaximal := P_isMaximal p P
  have hcyc := cycleType_eq_fiber_sizes (permBar (f := f) p P)
    (s2456Map K L f p P hmonic hsep) (fun b : s2456Beta K f p => b.1.natDegree)
    (by intro x; apply Subtype.ext; simpa [s2456Map] using congrArg Subtype.val (s2425RootFactor_permBar f p P hmonic hsep x))
    (by intro b; exact s2456Fiber_card K L f p P hmonic hsep hsplit b)
    (by intro b x y hx hy; exact s2456Fibre_transitive K L f p P hmonic hsep hsplit b x y hx hy)
  rw [hcyc]
  exact s2456_normalization K L f p P hmonic hsep
end LeanFormal.IUT.XiFPaper.S2456D5FinalActual
end
