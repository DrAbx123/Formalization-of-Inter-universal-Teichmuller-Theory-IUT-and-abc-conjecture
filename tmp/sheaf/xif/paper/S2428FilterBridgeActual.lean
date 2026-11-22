import tmp.sheaf.xif.paper.S2408FiberSizesActual
import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
noncomputable section
set_option maxHeartbeats 4000000
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2408FiberSizesActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2397RootFactorMapActual
namespace LeanFormal.IUT.XiFPaper.S2428FilterBridgeActual
attribute [local instance] Ideal.Quotient.field
variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
theorem s2428_filter_two_le_map
    {α : Type*} (M : Multiset α) (d : α → Nat)
    (hd : ∀ a ∈ M, 1 ≤ d a) :
    (M.map d).filter (fun n => 2 ≤ n) = (M.filter (fun a => d a ≠ 1)).map d := by
  rw [Multiset.filter_map]
  congr 1
  apply Multiset.filter_congr
  intro a ha
  simp only [Function.comp_apply]
  have hda := hd a ha
  constructor <;> omega
variable (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
  (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
  (hmonic : f.Monic) (hsep : (fbar f p).Separable)
  (hsplit : (Polynomial.map (algebraMap (RingOfIntegers K) L) f).Splits)
local instance : DecidableEq ((RingOfIntegers K) ⧸ p) := Classical.decEq _
include hp hP hPover hmonic hsep hsplit in
theorem s2428_filter_fiberSizes_eq_factorDegrees_filter :
    ((UniqueFactorizationMonoid.normalizedFactors (fbar f p)).map
        (fun g => (s2408FiberSet (K := K) (L := L) (p := p) (P := P) g).ncard)).filter
        (fun n => 2 ≤ n) =
      (factorDegrees (fbar f p)).filter (fun n => n ≠ 1) := by
  classical
  rw [s2408FiberSizes_eq_factorDegrees (K := K) (L := L) (f := f) (hmonic := hmonic)
    (hsep := hsep) (hsplit := hsplit) (p := p) (P := P)]
  unfold factorDegrees
  have hd : ∀ g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p), 1 ≤ g.natDegree := by
    intro g hg
    have hirr : Irreducible g :=
      (Polynomial.mem_normalizedFactors_iff (s2397Fbar_ne_zero f p P hmonic)).mp hg |>.1
    have hpos : 0 < g.natDegree :=
      @Irreducible.natDegree_pos ((RingOfIntegers K) ⧸ p) _ g hirr
    omega
  rw [Multiset.filter_map, Multiset.filter_map]
  congr 1
  apply Multiset.filter_congr
  intro a ha
  simp only [Function.comp_apply]
  have := hd a ha
  constructor <;> omega
#print axioms s2428_filter_two_le_map
#print axioms s2428_filter_fiberSizes_eq_factorDegrees_filter
end LeanFormal.IUT.XiFPaper.S2428FilterBridgeActual
end
