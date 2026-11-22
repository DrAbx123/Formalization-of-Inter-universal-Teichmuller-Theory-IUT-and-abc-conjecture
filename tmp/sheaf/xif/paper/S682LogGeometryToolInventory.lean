import LeanFormal.IUT.IUTII.Kummer.NatRootSystem
import LeanFormal.IUT.IUTII.Kummer.CompatibleRoots
import LeanFormal.IUT.IUTII.Kummer.TimesMuQuotient
import LeanFormal.IUT.IUTII.Kummer.KummerClass
/-! # S682: reusable Kummer/root/torsion tool inventory
Research inventory only; no new geometry and no fake O^triangleright root.
The companion note is S682LogGeometryToolsResearch.md. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.S682LogGeometryToolInventory
open LeanFormal.IUT
#check NatRootSystem
#check NatRootSystem.pow_self
#check AlgebraicClosureRootSystem.exists_pow_root
#check CompatibleRootSystem
#check TimesMuQuotient
#check TimesMuQuotient.quotientMap
#check TimesMuQuotient.action
#check CyclotomicTower
-- Research conclusion: no current Mathlib/LeanFormal LogStructure or RootStack;
-- available tools are abstract roots, torsion quotient and mu-action only.
end LeanFormal.IUT.XiFPaper.S682LogGeometryToolInventory
