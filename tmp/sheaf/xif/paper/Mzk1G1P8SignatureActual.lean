import tmp.sheaf.xif.paper.Mzk1G1P8ProducerAssemblyActual
import tmp.sheaf.xif.paper.Mzk1HT87F7F8F9InterfaceActual
import Mathlib.Tactic
/-!
# P8 assembly: signature map (documentation-level, no inhabitant claimed)

`Mzk1G1P8ProducerAssemblyActual.P8AssemblyInput` (DONE 22:03:14) has fields
`n delta C6 C7 C8 C9 heps hdelta hn hdelta_n perTriple`.  This file records the actual
argument sources for `perTriple` (consumer map), without introducing new hypotheses:
* hOmega, DL, hPi: D1 (`d1_of_analyticInput`), F7 (`RouteF7Statement`),
  F8 (`f8_chain_chart0`, `f8_second_equality_omegaE_frame`);
* F6 bound: `Mzk1G1F6EtaChoiceActual.routeF6_of_F1_to_F5_choice`;
* transport: `Mzk1P8HeightDictionaryActual.p8_perTriple_dictionary`.
-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.P8SignatureActual
open LeanFormal.IUT.XiFPaper.P8ProducerAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1HT87F7F8F9InterfaceActual

/-- Field-by-field signature tag for the P8 assembly input. -/
structure P8Signature where
  n : ℝ
  delta : ℝ
  C6 : ℝ
  C7 : ℝ
  C8 : ℝ
  C9 : ℝ
  F6 : Prop
  F7 : Prop
  F8 : Prop
  transport : Prop

/-- The signature tags of an actual `P8AssemblyInput`, with the node names recorded as
`Prop` tags (no new assumption). -/
def P8AssemblyInput.toSignature {ε : ℝ} (D : P8AssemblyInput ε) : P8Signature where
  n := D.n
  delta := D.delta
  C6 := D.C6
  C7 := D.C7
  C8 := D.C8
  C9 := D.C9
  F6 := True
  F7 := True
  F8 := True
  transport := True

#check P8Signature
#check P8AssemblyInput.toSignature
end LeanFormal.IUT.XiFPaper.P8SignatureActual
end