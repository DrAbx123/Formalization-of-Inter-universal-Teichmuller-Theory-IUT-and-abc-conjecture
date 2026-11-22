/-! # A812 volume-identification audit (which green assets can be assembled)

Audit for the two log-volume identifications needed by the final boundary:
`qPilotLogVolumeReading = -A` (`A = log q/(2l)`) and
`thetaPilotHullLogVolumeReal = V = logVol(hull(vcI D))`.  Statuses are from
current oleans/logs; no file is changed or recompiled here. -/

structure VolumeIdRow where
  asset : String
  green : Bool
  identifies : String
  remaining : String

def volumeIdRows : List VolumeIdRow :=
  [ { asset := "S3137QThetaPilotLogVolumeReadingsActual", green := true, identifies := "actual q reading = -|log q| (signed q-pilot); theta hull = actual C3 region; theta reading = log actual Haar", remaining := "qTheta comparison Q_C <= H_C is a pending Audit obligation; no q=-A or theta=V identification" },
    { asset := "Mzk1S3137ReadoutBridgeActual", green := true, identifies := "qPilotLogVolumeReading = signedQPilotLogVolume = log||q||; nonpositive", remaining := "inhabitant of N8Closure.PaperQPilotObjectActual is an external source obligation" },
    { asset := "GlobalThetaPilotHullLogVolumeActual", green := true, identifies := "globalThetaHullLogVolume = sum_v log(sourceHolomorphicHull volume); globalQPilotLogVolume = I.qPilotSignedLogVolume", remaining := "actual per-place hull volume, not paper normalized V" },
    { asset := "GlobalPositiveThetaHullLogVolumeActual", green := true, identifies := "positive theta hull per-place log = -thetaPacket.logVolume; global sum", remaining := "positive hull reading, not the qTheta comparison" },
    { asset := "Mzk1HullLogVolumeFormulaActual", green := true, identifies := "S1902 product Haar/log formulas; s1902LogVolume_hull_eq_normalized; productHaar_hull_log", remaining := "S1902 carrier, not the C3/paper V identification" },
    { asset := "S3137C3LogShellPacketNormalizedLogVolumeActual", green := true, identifies := "C3 tensor packet normalized log-volume", remaining := "normalization vs paper Vol(hull) still needs dictionary" },
    { asset := "Mzk1Cor312S3137AssemblyActual", green := true, identifies := "conditional cor312 from S3137 comparison/membership", remaining := "consumes the comparison; does not prove it" },
    { asset := "Mzk1FinalBoundarySzpiroActual", green := true, identifies := "paperGap <-> Paper312Statement / qThetaPilotLogVolumeComparison; Szpiro6Shape", remaining := "dictionary rows: qPilotReading=-A and thetaHullReading=V are PENDING" },
    { asset := "Mzk1ShellCoeffComputationActual", green := true, identifies := "cVModel = 1/4; hull coefficient (l+5)/4; hullProcession coefficient", remaining := "unprovedInputs lists exact hull packet/procession formula as not formalized" },
    { asset := "Mzk1PaperHullLogVolumeStatementActual", green := true, identifies := "paper hull log-volume statement shape", remaining := "statement only; no identification with actual readings" },
    { asset := "Mzk1S3137ComparisonArithmeticActual", green := false, identifies := "(candidate arithmetic identification of qTheta comparison)", remaining := "RED (FAIL EXIT=1)" },
    { asset := "Mzk1S3137ComparisonAttemptActual", green := false, identifies := "(candidate S3137 comparison attempt)", remaining := "RED (FAIL EXIT=1)" },
    { asset := "Mzk1HullLogVolumeMonotoneActual", green := false, identifies := "(candidate hull log-volume monotonicity)", remaining := "RED (FAIL EXIT=1)" },
    { asset := "Mzk1QThetaPilotObjectActual", green := false, identifies := "(candidate concrete q/Theta pilot object)", remaining := "RED (FAIL EXIT=1)" },
    { asset := "Mzk1S3137GogopexBridgeActual", green := false, identifies := "(candidate Gogopex bridge)", remaining := "RED (FAIL EXIT=1)" } ]

def volumeIdUsable : List String :=
  [ "actual q reading = -|log q| (S3137 green)",
    "actual theta hull = actual C3 region; theta reading = log Haar (S3137 green)",
    "global per-place theta hull log-volume (GlobalThetaPilotHullLogVolume green)",
    "S1902 normalized hull log formula (Mzk1HullLogVolumeFormulaActual green)",
    "C3 packet normalized log-volume (S3137C3... green)",
    "conditional cor312 assembly from S3137 comparison (Mzk1Cor312S3137Assembly green)" ]

def volumeIdMissing : List String :=
  [ "qPilotLogVolumeReading = -A with A = log q/(2l) (currently only -|log q|)",
    "thetaPilotHullLogVolumeReal = paper V = logVol(hull(vcI D)) (actual Haar vs normalized paper Vol)",
    "exact hull volume upper bound V <= (1/4) l (log d + log f) + C0",
    "qTheta comparison Q_C <= H_C (pending Audit obligation)",
    "inhabitant of PaperQPilotObjectActual (external paper source obligation)",
    "S3137 arithmetic comparison + hull log-volume monotonicity (both currently RED)" ]

theorem volumeIdRows_length : volumeIdRows.length = 15 := rfl
theorem volumeIdUsable_length : volumeIdUsable.length = 6 := rfl
theorem volumeIdMissing_length : volumeIdMissing.length = 6 := rfl

#print axioms volumeIdRows_length
