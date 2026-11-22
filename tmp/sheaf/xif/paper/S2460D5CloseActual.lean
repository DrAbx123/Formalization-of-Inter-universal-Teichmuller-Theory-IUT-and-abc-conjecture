import tmp.sheaf.xif.paper.S2456D5FinalActual
import tmp.sheaf.xif.paper.S2428FilterBridgeActual
import tmp.sheaf.xif.paper.S2440RootPermCycleCleanActual
import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
noncomputable section
set_option maxHeartbeats 4000000
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2397RootFactorMapActual
open LeanFormal.IUT.XiFPaper.S2408FiberSizesActual
open LeanFormal.IUT.XiFPaper.S2428FilterBridgeActual
open LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual
open LeanFormal.IUT.XiFPaper.S2456D5FinalActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
namespace LeanFormal.IUT.XiFPaper.S2460D5CloseActual
attribute [local instance] Ideal.Quotient.field
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
variable (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
  (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
  (hmonic : f.Monic) (hsep : (fbar f p).Separable)
  (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)
local instance : DecidableEq ((RingOfIntegers K) ⧸ p) := Classical.decEq _
include hp hP hPover hmonic hsep hsplit in
theorem s2460PermBar_cycleType_factorDegrees :
    (permBar (f := f) p P).cycleType =
      (factorDegrees (fbar f p)).filter (fun n => n ≠ 1) := by
  classical
  rw [s2456PermBar_cycleType K L f p P hmonic hsep hsplit]
  have hmap : (s2456M K f p).map Polynomial.natDegree =
      (s2456M K f p).map (fun g => (s2408FiberSet (K := K) (L := L) (p := p) (P := P) g).ncard) := by
    apply Multiset.map_congr rfl
    intro g hg
    exact (s2408FiberSet_ncard K L f p P hmonic hsep hsplit hg).symm
  rw [hmap]
  exact s2428_filter_fiberSizes_eq_factorDegrees_filter (K := K) (L := L)
    (f := f) (p := p) (P := P) hmonic hsep hsplit

include hp hP hPover hmonic hsep hsplit in
theorem s2460RootCycleType_factorDegrees
    (sigma : Gal(L/K))
    (H : @IsArithFrobAt (RingOfIntegers K) (RingOfIntegers L) _ _ _
      Gal(L/K) _ 
      (LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual.instMulSemiringActionAlgEquivRingOfIntegers_tmp K L)
      (LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual.instSMulCommClassAlgEquivRingOfIntegers_tmp K L)
      sigma P) :
    rootCycleType K L f hsplit sigma =
      (factorDegrees (fbar f p)).filter (fun n => n ≠ 1) := by
  have hperm : @Equiv.Perm.cycleType
      ((fbar f p).rootSet ((RingOfIntegers L) ⧸ P))
      ((fbar f p).rootSetFintype ((RingOfIntegers L) ⧸ P))
      (LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual.instDecidableEqElemQuotientRingOfIntegersIdealRootSetFbar K L f p P)
      (permBar (f := f) p P) =
      (factorDegrees (fbar f p)).filter (fun n => n ≠ 1) := by
    convert s2460PermBar_cycleType_factorDegrees K L f p P hmonic hsep hsplit using 2
  rw [← s2440_permBar_cycleType_eq_rootCycleType (K:=K) (L:=L) (f:=f) (p:=p) (P:=P)
    (hsplit:=hsplit) (hmonic:=hmonic) (hsep:=hsep) (σ:=sigma) (H:=H)]
  exact hperm
#print axioms s2460RootCycleType_factorDegrees
end LeanFormal.IUT.XiFPaper.S2460D5CloseActual
end
