# HDD-C3-BRIDGE — rank>1 det assets vs `actualC3LogShellTensorRegion` (A1054)

Status: read-only bridge audit; no compile.

## 1. What the HDD files actually provide

### S1476 `HDDRankActual`
- `S1476GlobalSections r := Fin r → O_ℚ` (`:74`);
- `S1476RankArithmeticVectorBundle r` (`:82`):
  `total : Type` with `Module O_ℚ`, `localization : total →ₗ (Fin r → O_v)`, `rank`;
- `s1476GlobalLocalization`, `s1476FreeArithmeticVectorBundle`,
  `s1476LocalLattice`, `s1476LocalLatticeEquiv`,
  `s1476LocalLattice_finrank`, `s1476LocalLattice_integral`;
- `S1476ArithmeticVectorBundleLocalization` (`:219`),
  `s1476ActualLocalization` (`:232`),
  `s1476S1215HDDLocalLattice` (`:251`),
  `s1476S1215HDDLocalLattice_rank_gt_one` (`:258`).

Carrier: `O_ℚ^r` at **rational** finite places, with local lattice
`Fin r → CompletionIntegers v` and ambient `Fin r → Completion v`.

### S1418 `HDDConsumerActual`
- `S1402DependentHDDSource I s` over `s : Finset (FinitePlace ℚ)`;
  `image : Theorem311Output I → Set ((v : {v // v∈s}) → Completion v)`;
- `S1418GlobalLattice D o = D.dependentHull o` (`:67`),
  `s1418GlobalLattice_eq_hull` (`:73`),
  `s1418Image_subset_globalLattice` (`:80`),
  `s1418GlobalLattice_mono` (`:91`),
  `s1418GlobalLattice_idempotent` (`:97`),
  `s1418GlobalLattice_eq_region` (`:141`),
  `s1418IntegralSpan_eq_globalLattice` (`:221`);
- det consumption: `s1418DetTensorPower_globalLattice` (`:245`),
  `s1418DetTensorPower_image` (`:253`), `s1418DetTensorPower_two` (`:261`),
  `s1418ActualFrozenHullDetSpec` (`:275`).

Carrier: dependent product `(v : {v // v∈s}) → Completion v`, not a tensor
block over a C3 `tensorIndex`; `detData` is the source's
`DetTensorPowerLogVolumeBookkeeping`.

### S1422 `HDDDetActual`
- `dependentPoint s := (v : {v // v∈s}) → Completion v`;
- `dependentRegion s := Set (dependentPoint s)`;
- `detDataOfHull` (`:262`): `DetTensorPowerLogVolumeBookkeeping` with
  `logVolume` = actual Haar mass of `LocalFieldProductHull.hull`;
- `dependentDetDataOfChar` (`:374`);
- `hullPacket` (`:420`), `hullPacket_det_eq_prod` (`:428`),
  `hullPacket_logVolume_eq_log_det` (`:436`);
- `frozenSpecZero_holds` (`:413`).

Carrier: same dependent product, measure `Measure.addHaar` on it;
det operation is multiplicative dilation by coordinate prime-inverse units;
tensor exponent = product of residue characteristics.

## 2. Is there an existing bridge to `actualC3LogShellTensorRegion`?

**No.**  The types are different:

| HDD | C3 |
|---|---|
| `(v : {v // v∈s}) → Completion v` | `ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple` |
| factors indexed by rational finite places `v` | factors indexed by `C3.tensorIndex` |
| local field `Completion v` | `CommonPrimeCompletion (c3LogShellPlace C3 i)` |
| Haar on dependent product | `actualC3LogShellTensorHaar` on tensor block |
| `Fin rank → Completion v` (S1476) | C3 tensor factors; no `Fin rank` indexing |
| `S1402DependentHDDSource` | `SourcePilotRegionData C3` |

No declaration in S1476/S1418/S1422 mentions
`actualC3LogShellTensorRegion`, `thetaPilotHull`, `qPilotClassicalRegion`, or
`C3LogShellTensorBlock`.

The only structural overlap is that both are Haar log-volumes of a
`LocalFieldProductHull`-style region, but on different product types and
with different factor fields.

## 3. What a bridge would need

To connect the HDD determinant comparison to the C3 theta/q regions:

1. **Region type equivalence / map**
   `Φ : Set (dependentPoint s) → Set (C3LogShellTensorBlock C3)`
   (or a measurable equivalence `dependentPoint s ≃ C3LogShellTensorBlock C3`)
   preserving the region operations (`region`, `hull`, multiplication).
2. **Place/label correspondence**
   a map `{v // v ∈ s} → C3.tensorIndex` (or a common refinement), compatible
   with `C3.tensorPlaces` and `S1402DependentE`; no such map exists.
3. **Local-field identification**
   `Completion v ≃ CommonPrimeCompletion (c3LogShellPlace C3 i)` for the
   corresponding places; not present.
4. **Measure comparison**
   `Measure.addHaar` on the dependent product vs
   `actualC3LogShellTensorHaar`; need a normalization/equivalence theorem
   (different dimensions; C3 `c3TensorBlockDimension`).
5. **Det/lattice identification**
   `S1476LocalLattice`/`Fin rank → CompletionIntegers` vs the C3 tensor
   integral region/local log-shells; no lattice equivalence.
6. **Hull comparison**
   `S1418GlobalLattice`/`LocalFieldProductHull.hull` vs
   `actualHolomorphicHull`/`thetaPilotHull`; no inclusion theorem.
7. **Packet/det identity**
   `S2807 hpacket` (`actualC3LogShellTensorLogVolume = packetLogVolume`) is
   still an explicit hypothesis, not a bridge.

## 4. What the HDD bridge could give under the correct direction

Assume a bridge `Φ` as in §3 and a q-region `qC3`/theta-region `thetaC3`
with HDD counterparts `qHDD`, `thetaHDD`.

- If the bridge is order-preserving and identifies the HDD hull with the C3
  theta hull, it can transport a **theta-side volume identity**
  `−R = log/neg-log of the HDD hull` to `−R` on C3.
- It can also transport the **det/tensor-power algebra** (S1418/S1422
  scaling laws) to the C3 det layer.
- It **does not** by itself produce `thetaC3 ⊆ qC3`: S1418/S1422 contain only
  the hull/det side; there is no q-pilot region in those files.
- If the bridge additionally maps a q-pilot region and preserves inclusion,
  then `thetaHDD ⊆ qHDD` (or the correct A1049 direction) would transfer to
  C3, and with volume identities yield `−A ≤ −R`.
- Without the q side, the HDD bridge can at most give a **one-sided** theta
  volume (`−R`) and det algebra, not the N5 inequality.

Warning: `RootHullContainmentInequalityActual` proves
`qPilotClassicalRegion ⊆ rootThetaHull` on an `ArithmeticTensorTupleBlock`.
That is the **q⊆theta** direction; under A1049 it gives the reversed inequality
and must not be used as the N5 bridge.

## 5. Declaration checklist

New bridge module would need:
- `HDDToC3BlockEquiv` (measurable equivalence + region/hull preservation);
- `hddPlaceToC3Index` and compatibility with `C3.tensorPlaces`;
- `hddCompletionEquivC3CommonPrime`;
- `hddHaar_eq_c3Haar_under_equiv` (normalization);
- `hddHull_eq_c3ThetaHull` / `hddRegion_eq_c3QRegion`;
- `hddDet_eq_c3PacketDet` (through `S2807 hpacket`);
- `hddContainment_transfer` (order-preserving inclusion transfer);
- `hddVolumeIdentity` (`−R`, and `−A` if q region exists).

None exists today; all are explicit GAPs.

## 6. Verdict

- S1476/S1418/S1422 are genuine rank>1/det/tensor-power assets, but on the
  **dependent-product HDD carrier**, not on `C3LogShellTensorBlock`.
- There is **no existing bridge**; the place/rank/measure/lattice types differ.
- A bridge would first give the theta-side `−R` and det algebra; to get
  `−A≤−R` it must also transport a q-pilot region and the correct
  `theta⊆q` inclusion, which is absent.
- Thus the HDD assets are reusable for the determinant/tensor-power law, not
  for the N5 region comparison until a C3 bridge is built.
