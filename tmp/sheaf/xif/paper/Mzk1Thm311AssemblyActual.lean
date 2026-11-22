import tmp.sheaf.lana_latest.Iut.Multiradial.Spec
import tmp.sheaf.lana_latest.Iut.Cor312.Container
import tmp.sheaf.xif.paper.Mzk1HullDetStep3115Actual
import tmp.sheaf.gogopex.Iut.Foundations.QualitativeData

/-! Mainline (A517-4): the Theorem 3.11 multiradial-representation assembly object, combining
the real pieces: the raw output / MRRep / possibleRegion data (LANA latest
`Multiradial/Spec.lean`), the tensor-packet container and log-shell admissible region (LANA
latest `Cor312/Container.lean`), the hull/det readouts and the det-normalized Step (xi-f)
comparison (our hull lane `Mzk1HullDetStep3115Actual`), and the qualitative IPL/SHE/APT
certificate (Gogopex `QualitativeData`).  The assembly exposes the 3.12-necessary data and the
proved comparison; it does not assert ABC/Thm 1.10. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Thm311AssemblyActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open scoped BigOperators
open LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual

universe u v w w'

/-- **The Theorem 3.11 assembly object** (multiradial representation + tensor/log-shell data
  + hull/det data). -/
structure Thm311Assembly (G : Type u) [Groupoid.{v} G] (A : Type w') [Group A]
    (ι : Type) (Vplaces : Type) {label : Type} [Fintype label] [DecidableEq label] where
  /-- The raw output of the multiradial algorithm (Theorem 3.11(i) data). -/
  raw : Iut.Multiradial.RawOutput G A
  /-- The functorial algorithm assignment (the multiradial representation). -/
  alg : ∀ P, Iut.Multiradial.MRRep raw P
  /-- The large volume container (tensor packets + log-shell region). -/
  container : Iut.LargeVolumeContainerData ι Vplaces
  /-- The hull/det state of the hull lane. -/
  hullDet : LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual.HullDetState label

section Assembly

variable {G : Type u} [Groupoid.{v} G] {A : Type w'} [Group A]
variable {ι Vplaces : Type} {label : Type} [Fintype label] [DecidableEq label]

/-- The multiradial representation of a raw-output representative in the assembly. -/
def Thm311Assembly.mrRepMk (M : Thm311Assembly G A ι Vplaces (label := label))
    (P : G) (x : M.raw.F.obj P) : Iut.Multiradial.MRRep M.raw P :=
  Iut.Multiradial.MRRep.mk x

/-- **Ind1 independence of transport** for the assembly's raw output (LANA real theorem). -/
theorem Thm311Assembly.transport_eq_transport (M : Thm311Assembly G A ι Vplaces (label := label))
    {P Q : G} (f g : P ⟶ Q) :
    Iut.Multiradial.MRRep.transport (R := M.raw) f =
      Iut.Multiradial.MRRep.transport (R := M.raw) g :=
  Iut.Multiradial.MRRep.transport_eq_transport (R := M.raw) f g

/-- The assembly is functorial when its algorithm is (LANA real predicate). -/
def Thm311Assembly.IsFunctorial (M : Thm311Assembly G A ι Vplaces (label := label)) : Prop :=
  Iut.Multiradial.IsFunctorialAlg M.raw M.alg

/-- **Possible images** in the assembly: for a region-valued construction on the raw output. -/
def Thm311Assembly.possibleRegion (M : Thm311Assembly G A ι Vplaces (label := label))
    {P : G} {X : Type*} (reg : M.raw.F.obj P → Set X)
    (r : Iut.Multiradial.MRRep M.raw P) : Set X :=
  Iut.Multiradial.MRRep.possibleRegion reg r

/-- **(Ind3) closure of possible images** (LANA real theorem). -/
theorem Thm311Assembly.subset_possibleRegion
    (M : Thm311Assembly G A ι Vplaces (label := label))
    {P : G} {X : Type*} (reg : M.raw.F.obj P → Set X) (x : M.raw.F.obj P)
    {S : Set X} (hS : S ∈ Iut.Multiradial.ind3Possible (reg x)) :
    S ⊆ M.possibleRegion reg (M.mrRepMk P x) :=
  Iut.Multiradial.MRRep.subset_possibleRegion reg x hS

/-- The assembly's log-shell admissible region (LANA real def of the container). -/
def Thm311Assembly.logShellRegion (M : Thm311Assembly G A ι Vplaces (label := label))
    (i : Fin M.container.proc.length) : M.container.AdmissibleRegion i :=
  M.container.logShellAdmissible i

/-- The assembly's hull readout (our real hull-lane readout). -/
def Thm311Assembly.hullReadout (M : Thm311Assembly G A ι Vplaces (label := label)) : ℝ :=
  LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual.hullReadout M.hullDet

/-- The assembly's det readout (our real hull-lane readout). -/
def Thm311Assembly.detReadout (M : Thm311Assembly G A ι Vplaces (label := label)) : ℝ :=
  LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual.detReadout M.hullDet

/-- **Step (xi-f) comparison inside the assembly**, from the det-normalized criterion
  `packetDet·q ≤ 1` (our real hull-lane theorem). -/
theorem Thm311Assembly.step3115_comparison
    (M : Thm311Assembly G A ι Vplaces (label := label))
    (h : LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual.packetDet
      M.hullDet.packet * M.hullDet.q ≤ 1) :
    M.hullReadout ≤ M.detReadout :=
  LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual.step3115_comparison_hullDet
    M.hullDet h

end Assembly

end

end LeanFormal.IUT.XiFPaper.Mzk1Thm311AssemblyActual