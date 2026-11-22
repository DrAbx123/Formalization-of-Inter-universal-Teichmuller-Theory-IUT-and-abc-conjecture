import tmp.sheaf.xif.paper.S2460D5CloseActual
import tmp.sheaf.xif.paper.S2463ActionTransportActual
import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
noncomputable section
set_option maxHeartbeats 4000000
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2460D5CloseActual
open LeanFormal.IUT.XiFPaper.S2463ActionTransportActual
namespace LeanFormal.IUT.XiFPaper.S2464D5CorrectedActual
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
include hp hP hPover hmonic hsep hsplit in
theorem s2464CorrectedCycleType :
    DedekindFrobeniusCycleTypeStatementCorrected (K:=K) (L:=L) f p P hmonic hsep hsplit := by
  classical
  haveI : P.IsMaximal := P_isMaximal p P
  haveI : Finite ((RingOfIntegers L) ⧸ P) := inferInstance
  unfold DedekindFrobeniusCycleTypeStatementCorrected
  obtain ⟨sigma, Hglobal⟩ := S2167FrobeniusExists K L P
  have H2440 : IsArithFrobAt (RingOfIntegers K) sigma P := by
    intro x
    have h := Hglobal x
    have hphi : (MulSemiringAction.toAlgHom (RingOfIntegers K) (RingOfIntegers L) sigma) x =
        (letI : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
           RingOfIntegers.instMulSemiringAction L
         letI : SMulCommClass Gal(L/K) (RingOfIntegers K) (RingOfIntegers L) := inferInstance
         MulSemiringAction.toAlgHom (RingOfIntegers K) (RingOfIntegers L) sigma x) := by
      rw [s2463_toAlgHom_eq (K:=K) (L:=L) sigma]
    rw [hphi]
    exact h
  exact ⟨sigma, Hglobal, s2460RootCycleType_factorDegrees K L f p P hmonic hsep hsplit sigma H2440⟩
#print axioms s2464CorrectedCycleType
end LeanFormal.IUT.XiFPaper.S2464D5CorrectedActual
end
