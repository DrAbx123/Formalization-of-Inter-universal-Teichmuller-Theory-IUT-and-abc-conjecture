import tmp.sheaf.xif.paper.S2460D5CloseActual
import tmp.sheaf.xif.paper.S2440RootPermCycleCleanActual
noncomputable section
set_option maxHeartbeats 4000000
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2494bRootCycleTypeMod29Actual
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2460D5CloseActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual
attribute [local instance] Ideal.Quotient.field
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
variable (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
  (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
  (hmonic : f.Monic) (hsep : (fbar f p).Separable)
  (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)
local instance : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
  LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual.instMulSemiringActionAlgEquivRingOfIntegers_tmp K L
local instance : SMulCommClass Gal(L/K) (RingOfIntegers K) (RingOfIntegers L) :=
  LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual.instSMulCommClassAlgEquivRingOfIntegers_tmp K L
local instance : DecidableEq ((RingOfIntegers K) ⧸ p) := Classical.decEq _
include hp hP hPover hmonic hsep hsplit in
theorem S2494b_rootCycleType_eq_filter (sigma : Gal(L/K))
    (H : @IsArithFrobAt (RingOfIntegers K) (RingOfIntegers L) _ _ _
      Gal(L/K) _
      (LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual.instMulSemiringActionAlgEquivRingOfIntegers_tmp K L)
      (LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual.instSMulCommClassAlgEquivRingOfIntegers_tmp K L)
      sigma P) :
    rootCycleType K L f hsplit sigma =
      (factorDegrees (fbar f p)).filter (fun n => n ≠ 1) :=
  s2460RootCycleType_factorDegrees K L f p P hmonic hsep hsplit sigma H
include hp hP hPover hmonic hsep hsplit in
theorem S2494b_rootCycleType_2_10 (sigma : Gal(L/K))
    (H : @IsArithFrobAt (RingOfIntegers K) (RingOfIntegers L) _ _ _
      Gal(L/K) _
      (LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual.instMulSemiringActionAlgEquivRingOfIntegers_tmp K L)
      (LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual.instSMulCommClassAlgEquivRingOfIntegers_tmp K L)
      sigma P)
    (hfac : factorDegrees (fbar f p) = ({2, 10} : Multiset ℕ)) :
    rootCycleType K L f hsplit sigma = ({2, 10} : Multiset ℕ) := by
  rw [S2494b_rootCycleType_eq_filter K L f p P hmonic hsep hsplit sigma H, hfac]
  decide
#print axioms S2494b_rootCycleType_eq_filter
#print axioms S2494b_rootCycleType_2_10
end LeanFormal.IUT.XiFPaper.S2494bRootCycleTypeMod29Actual
end
