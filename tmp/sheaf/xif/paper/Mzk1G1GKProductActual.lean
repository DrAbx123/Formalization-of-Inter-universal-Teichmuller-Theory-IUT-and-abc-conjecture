/- GK §7.3, batch 3c: the product tuple space `X = prod_i (ProjY (L i))^d` is compact
and nonempty (route L671-705). -/
import tmp.sheaf.xif.paper.Mzk1G1GKProjQuotientActual
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Tactic

noncomputable section
open scoped Valued WithZeroTopology
open ValuativeRel
namespace LeanFormal.IUT.XiFPaper.Mzk1G1GKProductActual
open LeanFormal.IUT.XiFPaper.Mzk1G1GKProjectiveCompactActual
open LeanFormal.IUT.XiFPaper.Mzk1G1GKProjQuotientActual

variable {K : Type*} [NormedField K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Nonemptiness of the projective Fermat curve for positive `n`. -/
theorem projY_nonempty (n : Nat) (hn : 0 < n) : Nonempty (ProjY (K := K) n) :=
  (Ysphere_nonempty (K := K) n hn).map
    (fun v => (Quotient.mk (projSetoid (K := K) n) v : ProjY (K := K) n))

section Product

variable {ι : Type} [Fintype ι]
variable (L : ι → Type) [∀ i, NormedField (L i)] [∀ i, ValuativeRel (L i)]
  [∀ i, TopologicalSpace (L i)] [∀ i, IsNonarchimedeanLocalField (L i)]

/-- The GK product tuple space: for each place `i`, `d` projective points of the Fermat
curve over the local field `L i` (route §7.3). -/
abbrev gkProductSpace (n d : Nat) : Type _ :=
  (i : ι) → Fin d → ProjY (K := L i) n

/-- **Compactness of the product tuple space** (finite product of compact spaces). -/
theorem gkProductSpace_compactSpace [∀ i, T2Space (L i)] (n d : Nat) :
    CompactSpace (gkProductSpace (L := L) n d) := by
  haveI : ∀ i, CompactSpace (ProjY (K := L i) n) :=
    fun i => projY_compactSpace (K := L i) n
  infer_instance

/-- **Nonemptiness of the product tuple space** (each factor is nonempty). -/
theorem gkProductSpace_nonempty (n d : Nat) (hn : 0 < n) :
    Nonempty (gkProductSpace (L := L) n d) :=
  ⟨fun i _ => (projY_nonempty (K := L i) n hn).some⟩

end Product

#print axioms projY_nonempty
#print axioms gkProductSpace_compactSpace
#print axioms gkProductSpace_nonempty
end LeanFormal.IUT.XiFPaper.Mzk1G1GKProductActual
