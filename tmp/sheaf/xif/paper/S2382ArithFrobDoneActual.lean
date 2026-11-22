import tmp.sheaf.xif.paper.S2368RootGaloisDoneActual
import tmp.sheaf.xif.paper.S2381SmulCommActual
import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual
noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2361SmulActual
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2381SmulCommActual
namespace LeanFormal.IUT.XiFPaper.S2382ArithFrobDoneActual
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
section
local instance : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
  IsIntegralClosure.MulSemiringAction (RingOfIntegers K) K L (RingOfIntegers L)
local instance : SMulCommClass Gal(L/K) (RingOfIntegers K) (RingOfIntegers L) :=
  S2381_smulCommClass
example : SMulCommClass Gal(L/K) (RingOfIntegers K) (RingOfIntegers L) :=
  S2381_smulCommClass
theorem s2382_arithFrobAt_reduction
    (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
    (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
    (sigma : Gal(L/K)) (H : IsArithFrobAt (RingOfIntegers K) sigma P)
    (a : RingOfIntegers L) :
    Ideal.Quotient.mk P (sigma • a) =
      frobBar p P (Ideal.Quotient.mk P a) := by
  have h := AlgHom.IsArithFrobAt.mk_apply H a
  rw [show sigma • a = (MulSemiringAction.toAlgHom (RingOfIntegers K) (RingOfIntegers L) sigma) a from rfl]
  rw [frobBar]
  convert h using 2
  rw [Ideal.over_def P p]
/-- Arithmetic Frobenius on O_L-roots reduces to permBar on residue roots. -/
theorem s2382_redRoot_smul
    (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
    (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
    (f : (RingOfIntegers K)[X]) (hmonic : f.Monic)
    (hsep : (fbar f p).Separable)
    (hsplit : (Polynomial.map (algebraMap (RingOfIntegers K) L) f).Splits)
    (sigma : Gal(L/K)) (H : IsArithFrobAt (RingOfIntegers K) sigma P)
    (a : f.rootSet (RingOfIntegers L)) :
    redRoot f p P hmonic
      ⟨sigma • a.1, by
        have ht := LeanFormal.IUT.XiFPaper.S2368RootGaloisDoneActual.s2368_rootTransport
          (K := K) (L := L) f hmonic hsplit sigma a
        rw [← ht]
        exact (LeanFormal.IUT.XiFPaper.S2345RootSetEquivActual.s2345RootSetEquiv
          (K := K) (L := L) f hmonic).symm
          (LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual.rootPerm K L f hsplit sigma
            ((LeanFormal.IUT.XiFPaper.S2345RootSetEquivActual.s2345RootSetEquiv
              (K := K) (L := L) f hmonic) a)) |>.2⟩ =
      permBar (f := f) p P (redRoot f p P hmonic a) := by
  apply Subtype.ext
  change Ideal.Quotient.mk P (sigma • a.1) =
    frobBar p P (Ideal.Quotient.mk P a.1)
  exact s2382_arithFrobAt_reduction (K := K) (L := L) p P sigma H a.1
end
#print axioms s2382_arithFrobAt_reduction
end LeanFormal.IUT.XiFPaper.S2382ArithFrobDoneActual
end
