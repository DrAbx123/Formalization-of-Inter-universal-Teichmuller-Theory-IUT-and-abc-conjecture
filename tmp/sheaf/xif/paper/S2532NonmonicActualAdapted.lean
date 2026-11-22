import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual
import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
noncomputable section
set_option maxHeartbeats 4000000
open Polynomial NumberField
attribute [local instance] Ideal.Quotient.field
namespace LeanFormal.IUT.XiFPaper.S2532NonmonicActualAdapted
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
  (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
  (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
/-- Nonmonic root reduction: only needs the reduction to be nonzero. -/
lemma mk_mem_rootSet_nonmonic
    (hfbar : fbar f p ≠ 0) (α : RingOfIntegers L)
    (hα : α ∈ f.rootSet (RingOfIntegers L)) :
    Ideal.Quotient.mk P α ∈ (fbar f p).rootSet ((RingOfIntegers L) ⧸ P) := by
  rw [mem_rootSet']
  constructor
  · exact hfbar
  · rw [fbar, aeval_def, ← mk_aeval_eq_of p P f α]
    rw [mem_rootSet'] at hα
    rw [hα.2, map_zero]
/-- Nonmonic root reduction map. -/
noncomputable def redRootNonmonic (hfbar : fbar f p ≠ 0) :
    f.rootSet (RingOfIntegers L) →
      (fbar f p).rootSet ((RingOfIntegers L) ⧸ P) :=
  fun α => ⟨Ideal.Quotient.mk P α.1,
    mk_mem_rootSet_nonmonic f p P hfbar α.1 α.2⟩
/-- The nonmonic orbit-size Dedekind--Frobenius statement. -/
def NonmonicDedekindFrobeniusOrbitSizeStatement
    (hsep : (fbar f p).Separable)
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits) : Prop :=
  ∃ sigma : Gal(L/K), IsArithFrobAt (RingOfIntegers K) sigma P ∧
    orbitSizeMultiset (rootPerm K L f hsplit sigma) = factorDegrees (fbar f p)
/-- The nonmonic theorem, universally quantified. -/
def NonmonicDedekindFrobeniusOrbitSizeTheorem : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
    (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
    (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
    (hsep : (fbar f p).Separable)
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits),
    NonmonicDedekindFrobeniusOrbitSizeStatement f p P hsep hsplit
#check mk_mem_rootSet_nonmonic
#check redRootNonmonic
#check NonmonicDedekindFrobeniusOrbitSizeTheorem
end LeanFormal.IUT.XiFPaper.S2532NonmonicActualAdapted
end
