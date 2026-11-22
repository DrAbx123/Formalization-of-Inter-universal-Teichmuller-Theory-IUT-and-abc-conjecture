## 2026-11-10 06:05 — abc GenEll P0 §1 COMPLETE (statement + elementary proof layer), all checker-CITABLE

- Files (all EXIT=0, tools/xif_citable_check CITABLE):
  GenEll01BasicActual (Def 1.2/1.5/Ex 1.3 abstractions; BDClassOn; reuse S3131BDClassCompositionActual.IsBDLe) decls 7
  GenEll01bHeightLayerActual (tree height layer: hTerm_nonneg reuse; hNon/hArc/hBox >= 0 given heightWeight >= 0; ArithmeticDivisorDegree:1171/1177/1214/1220-1236) decls 7
  GenEll02Prop14Actual (Prop 1.4 (i)-(iv) statement shape + immediate projections; corpus 294-423) decls 9
  GenEll02bProofActual (isBDLe_of_le_add_const; Prop 1.4(ii) extraction IsBDLe htL 0 zeroLocus^c; Prop 1.4(iv) extraction) decls 5
  GenEll03Prop16Actual (Prop 1.6 statement, corrected orientation IsBDLe htD logCondD UQ; corpus 505-523) decls 4
  GenEll03bProofActual (Prop 1.6 PROVED from the paper's pointwise bounded-|s|/Def1.5(iv) input) decls 3
  GenEll04Prop17Actual (Prop 1.7 (i) two BD inequalities + (ii) Riemann-Hurwitz degree shape; corpus 524-604) decls 6
  GenEll04bProp17ChainActual (Prop 1.7(i) assembly from two BD inputs + two-step chain; anchors DifferentTowerEstimate/DifferentDegreeUpperBound) decls 4
  GenEll04cDifferentInputsActual (Prop17DifferentTheoryInput exact paper-input registration + assembly) decls 4
  GenEll09BDToolsActual (isBDLe_add / isBDLe_of_le / isBDLe_add_const_left / isBDLe_neg_swap — BD chain tools for Thm 2.1 (ii)=>(i)) decls 4
  GenEllP0AbcStatusActual (P0 §1 status Obligation for mainline; remaining inputs named exactly: Prop 1.4(i) concrete wiring, Prop 1.7 different theory, Prop 1.4(iv) finiteness class B)
  GenEll05Theorem21Actual (mainline; CaseI/CaseII + theorem21_i_implies_ii) decls 8
  GenEll00NamingActual decls 2
- Probes green trio: GenEllP0AbcProbe2Actual, GenEllP0AbcProbe3Actual, GenEllP0AbcProbe4Actual. BD orientation note (S3136 tool): IsBDLe f g F := exists C, forall x in F, g x - f x <= C; Prop 1.6 = IsBDLe htD logCondD; Prop 1.7 first = IsBDLe (logDiffY-logDiffZ) (logCondE-logCondD).
- PRIOR-ART-INDEX sections H/H2 appended (STEP 0 lines: queries -> hits -> reuse). No re-proof of BD algebra, hTerm layer, or different estimates; registry frozen 14041; no registry edits from abc.
- Remaining GenEll §1 (paper inputs, exactly named): Prop 1.4(i) additivity at concrete height-layer functions (elementary wiring of hTerm sums), Prop 1.7 different theory input (Prop17DifferentTheoryInput), Prop 1.4(iv) finiteness (Silv1 Thm 2.1 style, class B).
