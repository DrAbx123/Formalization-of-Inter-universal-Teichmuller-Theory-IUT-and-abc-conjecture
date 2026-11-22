import tmp.sheaf.xif.paper.GenEll01bHeightLayerActual
import tmp.sheaf.xif.paper.GenEll02bProofActual
import tmp.sheaf.xif.paper.GenEll03bProofActual
import tmp.sheaf.xif.paper.GenEll04bProp17ChainActual
import tmp.sheaf.xif.paper.GenEll04cDifferentInputsActual
import tmp.sheaf.xif.paper.GenEll09BDToolsActual

noncomputable section
open LeanFormal.IUT
namespace LeanFormal.IUT.XiFPaper.GenEllP0AbcStatusActual

/-- **GenEll P0 §1 status (abc part)**: statement + elementary-proof layer for
Props 1.4/1.6/1.7 and the tree height layer, with reusable BD chain tools; exact
remaining paper inputs registered.  For mainline's Thm 2.1 (ii)=>(i) assembly. -/
def s3135GenEllP0AbcStatus : Audit.Obligation :=
  { id := "GENELL.P0.sec1-abc-status"
    source :=
      "papers/motizuki_corpus/text/Arithmetic Elliptic Curves in General Position.txt " ++
        "§1 lines 99-604 (Def 1.2 p.213, Ex 1.3 p.231, Def 1.5 p.432, Prop 1.4 " ++
        "294-423, Prop 1.6 505-523, Prop 1.7 524-604); ArithmeticDivisorDegree.lean:" ++
        "1171/1177/1214/1220-1236 (EE L452-475); S3136BDClassChainToolActual"
    status := Audit.VerificationStatus.interface
    note :=
      "P0 §1 abc part COMPLETE as statement + elementary proof layer (all citable). " ++
        "FILES: GenEll01BasicActual (Def1.2/1.5/Ex1.3 abstractions + citations); " ++
        "GenEll01bHeightLayerActual (tree height layer hNon/hArc/hBox >= 0 from " ++
        "heightWeight>=0 + hTerm_nonneg, matching Prop 1.4(ii) lower bound); " ++
        "GenEll02Prop14Actual (Prop 1.4 (i)-(iv) statement shape + projections); " ++
        "GenEll02bProofActual (isBDLe_of_le_add_const; Prop 1.4(ii) extraction " ++
        "IsBDLe htL 0 zeroLocus^c; Prop 1.4(iv) extraction); " ++
        "GenEll03Prop16Actual/GenEll03bProofActual (Prop 1.6 statement in corrected " ++
        "BD orientation + proved from the paper's pointwise bounded-|s|/Def1.5(iv) " ++
        "input); GenEll04Prop17Actual/GenEll04bProp17ChainActual/" ++
        "GenEll04cDifferentInputsActual (Prop 1.7 (i)/(ii) statement, assembly from " ++
        "two BD inputs, chain, and exact different-theory paper-input registration " ++
        "with tree anchors DifferentTowerEstimate.iutIVProp13i_normalizedDifferent_ge " ++
        "and DifferentDegreeUpperBound); GenEll09BDToolsActual (BD sum/monotone/" ++
        "const/neg tools for mainline's (ii)=>(i) chain).  REMAINING (paper inputs, " ++
        "exactly named): Prop 1.4(i) additivity at the actual height-layer functions " ++
        "(needs the hTerm sum decomposition instantiation, elementary but not yet " ++
        "wired); Prop 1.7 different-theory inputs (registered as " ++
        "Prop17DifferentTheoryInput; corpus 565-602); Prop 1.4(iv) finiteness " ++
        "(Silv1 Thm 2.1 style, paper input class B).  No discharge claims beyond what " ++
        "is proved; registry frozen 14041."
    dependsOn := [ "GENELL.P0.sec1", "IUT-III.cor312-to-ABC-conditional-interface" ]
    sorryItems :=
      [ "Prop 1.4(i) at concrete height-layer functions",
        "Prop 1.7 different-theory input (Prop17DifferentTheoryInput)",
        "Prop 1.4(iv) finiteness (class B paper input)" ] }

#check s3135GenEllP0AbcStatus
end LeanFormal.IUT.XiFPaper.GenEllP0AbcStatusActual
end
