/-! # A806 Szpiro upper-bound direction: green-asset audit

Audit of which green assets can feed the Szpiro-6 upper-bound direction, and
which hypotheses remain open.  Status is read from the current oleans/logs; no
file is recompiled or changed. -/

structure SzpiroAssetRow where
  asset : String
  green : Bool
  use : String
  limit : String
  deriving Repr

def szpiroUpperRows : List SzpiroAssetRow :=
  [ { asset := "Mzk1FinalBoundarySzpiroActual", green := true, use := "Szpiro6Shape + forward/backward conditional theorems", limit := "forward needs V upper bound; two log-volume dictionary items PENDING" },
    { asset := "Mzk1ShellCoeffComputationActual", green := true, use := "cVPaperBox = 1/4, szpiroThreshold_hull = 6; tensor cV = 1/8, threshold 3", limit := "coefficient arithmetic only" },
    { asset := "Mzk1SSIneqExplicitFormActual", green := true, use := "SSIneqExplicit definition; sigma criterion ssIneq_of_sigma_bound", limit := "needs certified V lower bound" },
    { asset := "Mzk1KappaLemmaActual", green := true, use := "kappa factor/bound; SSIneqKappa", limit := "algebra only" },
    { asset := "Mzk1N3SharedContainerBridgeShaActual", green := true, use := "paperGap <-> Paper312Statement / qTheta comparison", limit := "bridge; no volume bound" },
    { asset := "Mzk1ABCTwoEstimatesHeightWeightShaActual", green := true, use := "height estimate <-> weight bound", limit := "conditional dictionary" },
    { asset := "Mzk1HeightWeightFromTripleQpilotActual", green := true, use := "height-weight shape from triple comparison", limit := "conditional" },
    { asset := "Mzk1GapHeightWeightSharpQpilotActual", green := true, use := "sharp epsilon height-weight bound", limit := "conditional" },
    { asset := "S3131ThetaBoundToHeightWeightReuseActual", green := true, use := "v2 normalized volume comparison -> height-weight", limit := "conditional bridge" },
    { asset := "S3135HeightWeightAtPaperActual", green := true, use := "height-weight bound at paper functions", limit := "conditional" },
    { asset := "Mzk1DifferentDictionaryActual", green := true, use := "diffPaperLog/diffPaperPerPlace/torsionConstant/archConstant", limit := "per-place algebra; no upper different estimate" },
    { asset := "Mzk1DifferentTameBothActual / Mzk1DifferentTowerCompositeActual", green := false, use := "(candidate tame/tower different estimates)", limit := "RED (FAIL EXIT=1)" },
    { asset := "IntegralLogShellSharpBounds", green := true, use := "paper A/B exponent estimates; log-lattice inclusions", limit := "local coefficient bounds; no global hull V upper bound" },
    { asset := "FreyOddConductorHeightCriterion", green := true, use := "Frey conductor/radical/height dictionary", limit := "dictionary; no Szpiro upper bound" },
    { asset := "ABCFrontierHeightWeightRefutation", green := true, use := "counterexample (1,8,9): naive frontier height-weight clause FALSE", limit := "negative result; only epsilon/additive strengthening can survive" } ]

/-- The crucial missing analytic input for the forward Szpiro direction. -/
def szpiroUpperMissing : List String :=
  [ "V <= (1/4) * l * (log d + log f) + C0  (exact hull upper bound)",
    "qPilotLogVolumeReading = -A (q-side dictionary)",
    "thetaPilotHullLogVolumeReal = V (theta-hull dictionary)",
    "tame/tower different exponent upper estimates (currently RED)" ]

theorem szpiroUpperRows_length : szpiroUpperRows.length = 15 := rfl
theorem szpiroUpperMissing_length : szpiroUpperMissing.length = 4 := rfl

#print axioms szpiroUpperRows_length
