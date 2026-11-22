import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31SignQuotientSupplyReduction
import LeanFormal.IUT.IUTI.InitialTheta.SourceSignQuotientConstruction
import LeanFormal.IUT.IUTI.HodgeTheater.SourceClauseAssemblyUnitsReduction

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource

namespace LeanFormal.IUT.XiFPaper.Node09P2SignQuotientActual

universe u
variable {l : PrimeGeFive}

/-- Actual conditional assembly: a geometric core plus the canonical place
selection produces a full SourceSignQuotientData. -/
theorem p2_sourceSignQuotientData_of_geometricCore
    (A : InitialThetaArithmeticData.{u} l)
    (G : SourceSignQuotientGeometricCore A) :
    Nonempty (SourceSignQuotientData A) :=
  ⟨G.toSourceSignQuotientData
    (placeSelectionOfArithmeticData A)⟩

/-- Actual equivalence: the sign-quotient supply is exactly the geometric-core supply. -/
theorem p2_signQuotientSupply_iff_geometricCoreSupply :
    SourceSignQuotientSupply.{u} l ↔
      SourceSignQuotientGeometricCoreSupply.{u} l :=
  sourceSignQuotientSupply_iff_geometricCoreSupply

/-- Actual necessary condition: a geometric core supplies étale stack fibers over both F and K. -/
theorem p2_geometricCore_gives_stackSupply
    {A : InitialThetaArithmeticData.{u} l}
    (G : SourceSignQuotientGeometricCore A) :
    EtaleStackInstanceSupply A.F ∧
      EtaleStackInstanceSupply A.K :=
  etaleStackInstanceSupply_of_geometricCore G

def Node09P2SignQuotientStatus : List String :=
  [ "actual: p2_sourceSignQuotientData_of_geometricCore assembles a full SourceSignQuotientData from a geometric core plus the canonical place selection",
    "actual: p2_signQuotientSupply_iff_geometricCoreSupply is the exact equivalence SourceSignQuotientSupply <-> SourceSignQuotientGeometricCoreSupply",
    "actual: p2_geometricCore_gives_stackSupply shows a core supplies EtaleStackInstanceSupply over both F and K",
    "TRUE BLOCKER: no producer of SourceSignQuotientGeometricCore exists; equivalently the named card GeometricCoreStackUnit / SourceSignQuotientGeometricCoreSupply is not constructed. The existing reductions only prove equivalences to EtaleStackInstanceSupply / contract-root supply; the finite-etale quotient gluing, sign action, quotient witness and group inclusion fields are still supplied as a core, not built",
    "no fake, no True/PUnit/axiom/sorry" ]

end LeanFormal.IUT.XiFPaper.Node09P2SignQuotientActual