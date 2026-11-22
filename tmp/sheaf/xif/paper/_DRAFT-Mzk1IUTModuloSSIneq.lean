/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import Iut.Wall.MultiContainer
import Iut.Wall.Constraints
import Iut.Cor312.Concrete.ThetaRegion
import Iut.Tripod.Main
import Iut.Tripod.ClassicalAbc
import LeanFormal.IUT.ABCBridge.Bridge.Statement

/-! # IUT modulo ONE inequality: the single allowed sorry

USER-AUTHORIZED ARCHITECTURE (A871): the ENTIRE repository may use exactly ONE `sorry`,
placed below at `ssIneq_sorry`, whose statement is IUT III Cor 3.12 Step (xi), i.e.
`forall D, Iut.Wall.SSIneq D`.  All other statements must be proved.  Acceptance test:
removing the `sorry` (e.g. replacing it with `by` ) must make `lake env lean` FAIL on this
file, while the rest of the repo builds.  No other sorry/axiom may exist in this file.

DEPENDENCIES (must have oleans before this file compiles):
* lana: `Iut/Wall/MultiContainer.lean` (def `SSIneq`), `Iut/Wall/Constraints.lean`
  (`wall_idAlgOn_iff`), `Iut/Cor312/Concrete/ThetaRegion.lean:375` (`Cor312VariantHolds`),
  `Iut/Tripod/Main.lean:120` (`abc_of_variant`), `Iut/Tripod/ClassicalAbc.lean:286`
  (`classicalABC_of_statementI`), `Iut/Abc/Classical.lean` (`ClassicalABC`);
* our bridge: `LeanFormal/IUT/ABCBridge/Bridge/Statement.lean` (`ABCConjecture`) and the
  `ClassicalABC -> ABCConjecture` glue (name to be confirmed once oleans are available).

STATUS: DRAFT (does not compile yet: lana `Iut/Wall/*` oleans are not built in this
workspace).  This file is intentionally QUEUED; do not claim green. -/


namespace LeanFormal.IUT.XiFPaper.Mzk1IUTModuloSSIneq

open LeanFormal.IUT

/-- **The single allowed sorry**: IUT III Corollary 3.12, Step (xi) / Scholze-Stix
inequality, for every initial Theta-data `D`.  This is the ONLY `sorry` permitted in the
whole repository (A871). -/
theorem ssIneq_sorry : ∀ D : InitialThetaData, Iut.Wall.SSIneq D := by
  sorry

/-- Step (xi) gives the Corollary 3.12 variant statement (wiring; names per audit A738/A740). -/
theorem cor312VariantHolds_of_ssIneq (h : ∀ D : InitialThetaData, Iut.Wall.SSIneq D) :
    Iut.Cor312VariantHolds := by
  sorry -- TODO: replace by the lana glue once `Iut/Wall/*` oleans exist

/-- Variant statement gives ClassicalABC (lana `abc_of_variant`, Tripod/Main.lean:120). -/
theorem classicalABC_of_cor312Variant (h : Iut.Cor312VariantHolds) :
    Iut.ClassicalABC := by
  sorry -- TODO: replace by `abc_of_variant`

/-- ClassicalABC gives our ABCConjecture (bridge name TBC once oleans are available). -/
theorem abcConjecture_of_classicalABC (h : Iut.ClassicalABC) :
    LeanFormal.IUT.ABCBridge.ABCConjecture := by
  sorry -- TODO: replace by the ClassicalABC -> ABCConjecture glue

/-- FINAL (modulo the single sorry): ABC for all triples. -/
theorem abcConjecture_of_ssIneq_sorry : LeanFormal.IUT.ABCBridge.ABCConjecture :=
  abcConjecture_of_classicalABC (classicalABC_of_cor312Variant
    (cor312VariantHolds_of_ssIneq ssIneq_sorry))

end LeanFormal.IUT.XiFPaper.Mzk1IUTModuloSSIneq
