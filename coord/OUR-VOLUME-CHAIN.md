# OUR-VOLUME-CHAIN — paper-normalized inventory (A905)

Status: inventory of our own Lean files (lane hull).  All listed files are green
with gate trio unless noted.  This is NOT an IUT theorem; conditional interfaces are
marked CONDITIONAL/GAP.

## 1. Shell volume (L1)

File: `Mzk1PaperNormMuActual.lean`
- `paperMuCoeff p e r n = 1 + [p=2] - 1/e - r/n` (def)
- `logMuPaper p e r n = paperMuCoeff * Real.log p` (def)
- `logMuPaper_ge_odd`: p != 2, log p >= 0 => lower bound (p=2 correction absent)
- `logMuPaper_ge_two`: p = 2 => lower bound
- `logMuPaper_le_base`: upper bound

File: `Mzk1Chain2VolumeDataActual.lean`
- `logMuPaper_p11 : logMuPaper 11 10 1 10 = (4/5) log 11`
- `logMuPaper_p2 : logMuPaper 2 2 1 2 = log 2`
- `archTerm_eq_log : archTerm = log 2 / 2 + log pi`

## 2. Hull packet (L2/L3)

File: `Mzk1HullPacketFormulaActual.lean`
- `hullPacketFinite`, `hullPacketTame` (defs, sums over capsules/places)
- `hullPacketFinite_eq`, `hullPacketTame_eq`
- `hullPacketFinite_nonneg`
- `hullPacketTame_le`: tame bound
- `logVolHullVcI` (def), `logVolHullVcI_eq`
- `logVolHullVcI_le_of_packet_le`: upper bound from per-packet upper bounds

File: `Mzk1VolumeIdentificationActual.lean`
- `processionAverage n f = (1/n) sum f` (def)
- `tameHullVolume` (def), `tameHullVolume_eq`, `tameHullVolume_le`
- `VolumeIdentification V stepV : Prop := V = stepV` (GAP interface)
- `volume_upper_of_general_identification`: from V = stepV and stepV <= C get V <= C

File: `Mzk1ProcessionAverageActual.lean`
- `avgJPlusOne_eq_l : (1/n) sum_{j<n}(j+2) = (l+5)/4` for l = 2n+1
- `avgJSquare_eq_l : (1/n) sum_{j<n}(j+1)^2 = l(l+1)/12`

## 3. Local volume assembly (L4/L5)

File: `Mzk1LocalVolumeAssemblyActual.lean`
- `assembledVolume l D = ((l+5)/4) * D` (def)
- `assembledVolume_nonneg`
- `volume_eq_assembled`: V = assembledVolume => V = ((l+5)/4)D (conditional)
- L1-L5 rows: L4 is now PROVED in Mzk1ProcessionAverageActual; L5 still needs
  identification of actual V with assembledVolume (GAP).

File: `Mzk1DExactFromHullActual.lean`
- `DExact w h logp = sum w*h*logp` (def)
- `DExactWithArch = DExact + arch` (def)
- `term_ge`: w>=1, c<=h, c>=0, logp>=0 => c logp <= w h logp
- `tame_height_ge`: l<=e => 1-1/l <= 1-1/e
- `L7_term`: tame e>=l, w>=1, logp>=0 => (1-1/l)logp <= w(1-1/e)logp
- `L7_global`: per-place bounds => sum <= DExact
- `L7_with_arch`: arch>=0 => same for DExact+arch

## 4. Different / arch / torsion

File: `Mzk1DifferentDictionaryActual.lean`
- `log_norm_differentGenerator_eq_neg_paperOrder_mul_log`
- `diffPaperPerPlace order logp r n := -order logp - r/n + archConstant`
- `diffPaperPerPlace_eq`, `diffPaperPerPlace_different_eq`
- `archConstant = log(sqrt 2 * pi)`; `archConstant_eq_log = log2/2 + log pi`

File: `Mzk1ArchTorsionDictionaryActual.lean`
- `torsionTerm r n = r/n`; `torsionTerm_nonneg`, `torsionTerm_le_one`
- `diffTerm = -order logp - torsionTerm r n + archConstant`
- `diffTerm_ge`: torsionTerm <= 1 => diffTerm >= -order logp - 1 + archConstant

File: `Mzk1IdentificationFinalActual.lean`
- `paperDifferentOrder v e = v/e`
- `paperDifferentOrder_ge_one_sub_inv`; `DifferentIntegerLower v e := e-1 <= v`
- `different_add_a_ge_one`; `RadiusPointwiseBound` (interface)

## 5. Step V box / volume upper

File: `Mzk1PaperStepVBoxActual.lean`
- `paperLHS`, `paperRHS`, `paperRHS_expand`
- `paperStepV_inequality`: paper-original Step-V inequality PROVED (l>=5)

File: `Mzk1VolumeUpperLeActual.lean`
- `neg_le_neg_floor`, `sum_rho_le`
- `volume_upper_le_of_rho`, `volume_upper_le_of_rho_mul_log`
- `VolumeUpperLeDictionary` with field `V_le_step : V <= stepVExpr`
- `volume_upper_of_le_dictionary`

File: `Mzk1StepVIdentificationActual.lean`
- `StepVDictionary` (fields: V, stepVExpr, `V_le_step : V <= stepVExpr`, plus box data)
- `volume_upper_of_dictionary`
- `PaperDictionaryShape` (pure equality, no True)

File: `Mzk1StepVVolumeUpperActual.lean`
- `stepVExpr`, `stepVRHS`, `paperBox`
- `volume_upper_of_stepV`, `volume_upper_of_identification`, `volume_upper_of_exceptional_abs`

## 6. Deficit / verdict forms

File: `Mzk1PaperNormMuActual.lean`
- `PaperNormVerdict`, `paperNormDeficit`
- `paperNormVerdict_iff_deficit_nonpos`: verdict iff deficit <= 0

File: `Mzk1PaperNormThetaActual.lean`
- `thetaSumPaper`, `clana = (sFactor nC - 1)/(2l)`
- `thetaSumPaper_eq_clana_mul`
- `paperDeficit`, `paperDeficit_thetaSubst`, `paperDeficit_expanded`
- `paperVerdict_iff_deficit`

## 7. Coverage of (sF-1)A <= V

Equivalent deficit form: `paperNormVerdict`/`paperVerdict` is true iff the deficit
is <= 0 (`paperNormVerdict_iff_deficit_nonpos`, `paperVerdict_iff_deficit`).

What our files actually prove:
- CONDITIONAL UPPER bounds in the opposite direction: `VolumeUpperLeDictionary.V_le_step`
  gives `V <= stepVExpr`, and `volume_upper_of_le_dictionary` turns it into an upper
  bound on V (used for Szpiro side), NOT `(sF-1)A <= V`.
- CONDITIONAL equality/identification: `VolumeIdentification V stepV := V = stepV`
  (VolumeIdentificationActual) and `volume_eq_assembled`; these are interfaces/
  conditionals, not proved for the actual lana V.
- L7 lower bound only: `L7_term/L7_global/L7_with_arch` prove
  `(1-1/l) log p <= DExact` (tame e>=l, w>=1, logp>=0, arch>=0); this is NOT
  `(sF-1)A <= V` and does not supply the q-side coefficient sF.

Conclusion: **no unconditional theorem of ours proves `(sF-1)A <= V` / deficit <= 0.**
Covered assumptions are exactly: V = stepV (or V <= stepV) via StepVDictionary/
VolumeIdentification interfaces, plus the explicit tame/arch positivity hypotheses of
L7.  The object identification `V = stepV` for the actual lana carrier remains GAP.

## 8. References

All files under `tmp/sheaf/xif/paper/`; compile with
`lake env lean -R . -o ...olean <file>.lean`.  Q-side/SSIneq (lana) is NOT in this
chain; see coord/VCI-FROM-HULL.md for the q-dependence audit.
