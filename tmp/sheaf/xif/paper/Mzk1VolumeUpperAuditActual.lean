/-! # A810 volume-upper-bound provability audit

Audit of green assets usable for the hull-volume upper bound
`V <= (1/4) * l * (log d + log f) + C0`, which is the open input of
`Mzk1FinalBoundarySzpiroActual.ssIneqExplicit_to_szpiro6`.  Statuses are the
current oleans/logs; no file is changed or recompiled here. -/

structure VolumeUpperRow where
  asset : String
  green : Bool
  usableFor : String
  limitation : String

def volumeUpperRows : List VolumeUpperRow :=
  [ { asset := "Mzk1FinalBoundarySzpiroActual.ssIneqExplicit_to_szpiro6", green := true, usableFor := "forward Szpiro-6 from SSIneq + V upper bound", limitation := "consumes V <= (1/4) l logdf + C0; that bound is PENDING" },
    { asset := "Mzk1FinalBoundarySzpiroActual.szpiro6_to_ssIneqExplicit", green := true, usableFor := "converse from sigma-margin + V lower bound", limitation := "needs V >= (1/4) l logdf; lower bound not formalized" },
    { asset := "Mzk1ShellCoeffComputationActual.cVModel_eq / cVModel_szpiroThreshold", green := true, usableFor := "coefficient c_V = 1/4 and sigma* = 6", limitation := "coefficient arithmetic only" },
    { asset := "Mzk1ShellCoeffComputationActual.unprovedInputs", green := true, usableFor := "explicit list of structural hull/procession inputs", limitation := "records that hullPacket exact / procession average are NOT formalized" },
    { asset := "Mzk1PaperNormMuActual.logMuPaper_le_base", green := true, usableFor := "per-place upper bound logMuPaper <= (1+[p=2]) log p when r/n >= 0", limitation := "summed local bound; not a global hull V <= (1/4) l logdf + C0" },
    { asset := "Mzk1PaperNormMuActual.sum_logMuPaper_ge_odd / _ge_two", green := true, usableFor := "per-place lower bounds for sumLogMuPaper", limitation := "lower side only" },
    { asset := "IntegralLogShellSharpBounds.logShellPaperAExponent_sub_inv_mul_log_le_two", green := true, usableFor := "local A-exponent upper bound (A - 1/e) log p <= 2", limitation := "local paper exponent, not global hull volume" },
    { asset := "IntegralLogShellSharpBounds.logShellPaperBExponent_add_inv_mul_log_le_one_add_log", green := true, usableFor := "local B-exponent upper bound (B + 1/e) log p <= 1 + log e", limitation := "local paper exponent" },
    { asset := "IntegralLogShellSharpBounds.logShellPaperExponent_sum_mul_log_le_three_add_log", green := true, usableFor := "local (A+B) log p <= 3 + log e", limitation := "local only" },
    { asset := "IntegralLogShellIndexResidueFormula.logShellResidueCard_eq_prime_pow_of_qfe", green := true, usableFor := "q = p^f residue cardinal dictionary", limitation := "dictionary only" },
    { asset := "Mzk1DifferentDictionaryActual.diffPaperPerPlace_eq / diffPaperLog_eq", green := true, usableFor := "per-place different/arch/torsion algebra", limitation := "algebra; no upper different estimate" },
    { asset := "Mzk1DifferentTameBothActual / Mzk1DifferentTowerCompositeActual", green := false, usableFor := "(candidate tame/tower different upper estimates)", limitation := "RED (FAIL EXIT=1); not usable" },
    { asset := "Mzk1LANADifferentRamificationActual", green := false, usableFor := "(candidate LANA different layer)", limitation := "olean absent; only elementary definitions, not a volume upper bound" } ]

def volumeUpperUsable : List String :=
  [ "coefficient/threshold: cVModel = 1/4, sigma* = 6",
    "per-place upper/lower bounds on logMuPaper",
    "local A/B exponent upper bounds from IntegralLogShellSharpBounds",
    "q = p^f residue dictionary",
    "different/arch/torsion algebra dictionary" ]

def volumeUpperMissing : List String :=
  [ "exact hull volume upper bound V <= (1/4) l (log d + log f) + C0",
    "hullPacket exact formula / procession average (listed as unproved structural inputs)",
    "q-side reading = -A and theta-hull reading = V (two log-volume alignments)",
    "tame/tower different upper estimates (currently RED)",
    "global log d + log f dictionary from the conductor/different data" ]

theorem volumeUpperRows_length : volumeUpperRows.length = 13 := rfl
theorem volumeUpperUsable_length : volumeUpperUsable.length = 5 := rfl
theorem volumeUpperMissing_length : volumeUpperMissing.length = 5 := rfl

#print axioms volumeUpperRows_length
