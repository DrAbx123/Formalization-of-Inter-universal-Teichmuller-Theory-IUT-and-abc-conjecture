import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual

noncomputable section
set_option maxHeartbeats 8000000
open Polynomial
attribute [local instance] Ideal.Quotient.field
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual

namespace LeanFormal.IUT.XiFPaper.S2533NonmonicDedekindActual

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
variable (f : (NumberField.RingOfIntegers K)[X])
  (p : Ideal (NumberField.RingOfIntegers K)) [hp : p.IsMaximal]
  (P : Ideal (NumberField.RingOfIntegers L)) [hP : P.IsPrime]
  [hPover : P.LiesOver p]

/-- The reduction map on roots of an arbitrary nonzero reduction of f:
the monicity assumption is replaced by nonvanishing of fbar. -/
noncomputable def S2533RedRoot (hfb : fbar f p ≠ 0) :
    f.rootSet (NumberField.RingOfIntegers L) →
      (fbar f p).rootSet ((NumberField.RingOfIntegers L) ⧸ P) :=
  fun α =>
    ⟨Ideal.Quotient.mk P α.1, by
      rw [mem_rootSet']
      constructor
      · exact Polynomial.map_ne_zero hfb
      · have hαroot : aeval (α : NumberField.RingOfIntegers L) f = 0 := by
          have hα := α.2
          rw [mem_rootSet'] at hα
          exact hα.2
        rw [fbar, aeval_def, ← mk_aeval_eq_of p P f α.1, hαroot, map_zero]⟩

/-- The q-Frobenius permutation on roots of fbar; no monicity needed. -/
noncomputable def S2533PermBar :
    Equiv.Perm ((fbar f p).rootSet ((NumberField.RingOfIntegers L) ⧸ P)) :=
  permBar f p P

end LeanFormal.IUT.XiFPaper.S2533NonmonicDedekindActual
end
