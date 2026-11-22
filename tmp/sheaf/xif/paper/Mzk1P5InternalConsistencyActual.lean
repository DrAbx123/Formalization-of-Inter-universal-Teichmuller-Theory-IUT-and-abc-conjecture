import tmp.sheaf.xif.paper.Mzk1P5FinalSummaryActual

/-!
# CONDITIONAL internal-consistency check for P5NamedInputs

This file only checks that P5NamedInputs can be packaged from named data.
The actual L=RootExtension, toRoot=id attempt is NOT lawful: a hypothetical
NormedField instance on RootExtension creates a Field instance distinct from
the canonical AlgebraicClosure.instField, a typeclass diamond.  No fake normed
instance is added.  The analytic bridge remains GAP.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P5InternalConsistencyActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.Mzk1P5LabelShiftActual
open LeanFormal.IUT.XiFPaper.Mzk1P5FinalSummaryActual
open LeanFormal.IUT.XiFPaper.Mzk1P5PhaseExponentDataActual
open LeanFormal.IUT.Foundations.Theta

universe u v

variable {l : PrimeGeFive}
variable {K : Type v} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type*} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)
variable (v0 : V)
variable {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]

/-- Package the four inputs once a map/root are supplied; this is a
satisfiability check of the structure, not a construction of toRoot. -/
theorem internalConsistency
    (toRoot : L →+* RootExtension (G := G) v0) (r : L)
    (hroot : toRoot r =
      (twoLthRootAt (G := G) v0 : RootExtension (G := G) v0) ^ l.value)
    (P : PhaseExponentData l) :
    ∃ I : P5NamedInputs (L := L) (l := l) (G := G) (v0 := v0),
      I.toRoot = toRoot := by
  exact ⟨⟨toRoot, r, hroot, P⟩, rfl⟩

#print axioms internalConsistency

end LeanFormal.IUT.XiFPaper.Mzk1P5InternalConsistencyActual
