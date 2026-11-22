# Eta Rss admissible correction

- Task: admissible-region correction (actual open/closed masses).
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/EtaRssAdmissibleCorrection.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0; zero sorry.

## Construction

- `AdmissibleRegion`: measurable, `0 < mu < top`.
- `RegionSetoid` identifies admissible regions by actual Haar volume.
- `Rss := Quotient RegionSetoid`; `readout` is `Quotient.lift mu`, so it
  descends; `readout_mk` rfl.
- `admClosedBall` and `admOpenBall` are actual closed/open unit balls,
  admissible with positive finite mass.
- `admOpenBall_volume_lt_closedBall` is imported actual
  `EtaRssNontrivialActual.open_mass_lt_closed_mass`; hence
  `admOpenBall_volume_ne_closedBall`.
- `rss_admissible_not_subsingleton`: open and closed classes differ.
- `readout_ne_open_closed`: the quotient readout differs on these classes.

No empty/univ witness, no scaled-ball gap, no arbitrary region.