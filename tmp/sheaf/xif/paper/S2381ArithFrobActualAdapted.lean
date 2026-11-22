import tmp.sheaf.xif.paper.S2368RootGaloisDoneActual
import tmp.sheaf.xif.paper.S2361SmulActual
import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual
noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2345RootSetEquivActual
open LeanFormal.IUT.XiFPaper.S2361SmulActual
open LeanFormal.IUT.XiFPaper.S2368RootGaloisDoneActual
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
namespace LeanFormal.IUT.XiFPaper.S2381ArithFrobActualAdapted
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
section
local instance : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
  IsIntegralClosure.MulSemiringAction (RingOfIntegers K) K L (RingOfIntegers L)
local instance : SMulCommClass Gal(L/K) (RingOfIntegers K) (RingOfIntegers L) where
  smul_comm g a b := by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
    have hfix : g • (algebraMap (RingOfIntegers K) (RingOfIntegers L) a) =
        algebraMap (RingOfIntegers K) (RingOfIntegers L) a := by
      rw [S2361_smul_eq_galRestrict]
      exact (galRestrict (RingOfIntegers K) K L (RingOfIntegers L) g).commutes a
    rw [hfix]
/-- Arithmetic Frobenius acting on O_L reduces to q-Frobenius on residue field. -/
theorem s2381_arithFrobAt_reduction
    (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
    (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
    (sigma : Gal(L/K)) (H : IsArithFrobAt (RingOfIntegers K) sigma P)
    (a : RingOfIntegers L) :
    Ideal.Quotient.mk P (sigma • a) =
      frobBar p P (Ideal.Quotient.mk P a) := by
  have h := AlgHom.IsArithFrobAt.mk_apply H a
  rw [frobBar]
  rw [show Nat.card ((RingOfIntegers K) ⧸ P.under (RingOfIntegers K)) =
      Nat.card ((RingOfIntegers K) ⧸ p) by rw [Ideal.over_def P p]]
  exact h
end
#print axioms s2381_arithFrobAt_reduction
end LeanFormal.IUT.XiFPaper.S2381ArithFrobActualAdapted
end
