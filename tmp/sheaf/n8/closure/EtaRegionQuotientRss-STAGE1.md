# Eta Rss as equal-volume region quotient

- Task: ETA v2 highest-value correction.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/EtaRegionQuotientRss.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0, no sorry.

## Construction

- `K` is the actual F-completion at `EtaAnabAtFPlace.nativeFPlaceAtPrime`.
- `Region := Set K`; `RegionSetoid` identifies regions by equality of the
  actual additive Haar volume `mu`.
- `Rss := Quotient RegionSetoid`, not a fixed shell record.
- `rssOf` is the quotient class; `readout` is the `Quotient.lift` of `mu`, so
  the volume readout descends to the quotient.
- `readout_mk` is rfl; `rssOf_ne_of_volume_ne` reflects volume inequality.

## Non-subsingleton

- `exists_two_regions_diff_volume`: empty has volume 0, universe has positive
  Haar volume (`measure_pos_of_nonempty_interior`).
- `rss_not_subsingleton`: empty and full classes differ, so the quotient is not
  a subsingleton/singleton.

## Fixed shell donor

- `fixedShellDonor` is the actual F log-shell `localShellAtF.logShell`.
- `fixedShellDonor_readout` shows its quotient readout is its Haar volume; the
  fixed shell is only a donor point, not the Rss definition.

No singleton Rss; no fixed-shell-as-Rss; no Fmod shell.