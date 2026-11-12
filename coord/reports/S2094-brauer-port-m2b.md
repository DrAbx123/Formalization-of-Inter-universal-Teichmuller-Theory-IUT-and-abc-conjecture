# S2094: Brauer closure port and M2b `PadicField.artin_transfer`

Date: 2026-11-02. Consumer: S2027 / S2039 M2b; follows S2050 (PadicField/Reciprocity port) and S2093 (Artin bridge).

## Source and adaptation

- External source: `D:/lean/tmp/local-cft-port/local-class-field-theory-main/LocalClassFieldTheory/Brauer` (23 files).
- Ported target: `D:/lean/tmp/local-cft-port/Brauer` (23 files).
- Enclosing workspace checkout HEAD: `9399e9fab4d62ea5f78a4a0d56ceecb84525a3ee`; the copied external source directory has no nested `.git`, so its upstream commit is not recorded locally (source file SHA256 values below identify the exact inputs).
- Source toolchain: Lean `v4.32.0`, Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Build toolchain: project Lean `v4.32.2`, Mathlib `905b95818eb32af7874a58b427f50c1711a5e96c`.
- Adaptation is import-prefix only:
  - `LocalClassFieldTheory.Brauer.*` -> `Brauer.*`
  - `LocalClassFieldTheory.Reciprocity.*` -> `Reciprocity.*`
  - `LocalClassFieldTheory.PadicField.*` -> `PadicField.*`
  - `LocalClassFieldTheory.Galois.*` -> `Galois.*`
  - `ContinuousKummerTheory.*` unchanged.
- Line-by-line check over all 23 files: every non-import line is text-identical to the source; only 38 import lines changed in total. See `tmp/local-cft-port/brauer_copy_manifest.json`.
- No `sorry`, `admit`, or source `axiom` in the 23 ported files (`grep` count 0).

## Target

```
module        Brauer.ArtinTransfer
source        D:/lean/tmp/local-cft-port/Brauer/ArtinTransfer.lean
src SHA256    F7D422B14286E8D399574C76446708903E51B39455017031B425408E84DA5162  (adapted; 15117 bytes)
source SHA256 84AA1D219492C8B9D050A999BA219455F29D2123581F12EA15C0D76B3ACE874A  (original external file)
EXIT          0
olean         D:/lean/.lake/build/lib/lean/Brauer/ArtinTransfer.olean
olean bytes   1099768
olean SHA256  68F95A3F04C0AF9A715D176BFED2044C5FF9B8F1676403FAFD00ABC5DE1CCA64
axioms        [propext, Classical.choice, Quot.sound]
```

Build command (per module, topological order):

```powershell
$env:LEAN_PATH = @(
  'D:\lean\.lake\packages\Cli\.lake\build\lib\lean',
  'D:\lean\.lake\packages\batteries\.lake\build\lib\lean',
  'D:\lean\.lake\packages\Qq\.lake\build\lib\lean',
  'D:\lean\.lake\packages\aesop\.lake\build\lib\lean',
  'D:\lean\.lake\packages\proofwidgets\.lake\build\lib\lean',
  'D:\lean\.lake\packages\importGraph\.lake\build\lib\lean',
  'D:\lean\.lake\packages\LeanSearchClient\.lake\build\lib\lean',
  'D:\lean\.lake\packages\plausible\.lake\build\lib\lean',
  'D:\lean\.lake\packages\mathlib\.lake\build\lib\lean',
  'D:\lean\.lake\build\lib\lean',
  'C:\Users\Administrator\.elan\toolchains\leanprover--lean4---v4.32.2\lib\lean'
) -join ';'
lean --root 'D:\lean\tmp\local-cft-port' -o 'D:\lean\.lake\build\lib\lean\Brauer\<Module>.olean' 'D:\lean\tmp\local-cft-port\Brauer\<Module>.lean'
```

The target type (from `#check`, verbatim):

```
PadicField.artin_transfer.{u_3, u_4} {p : ℕ} [hp : Fact (Nat.Prime p)] {K : Type u_3} [Field K]
  [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] {Ω : Type u_4} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω]
  [IsScalarTower ℚ_[p] K Ω] [IsAlgClosed Ω] [IsGalois K Ω] (K' : IntermediateField K Ω) [FiniteDimensional K ↥K'] (a : Kˣ) (g : Gal(Ω/K))
  (hg : (AlgEquiv.restrictNormalHom ↥(PadicField.maxAbelian K Ω)) g = (PadicField.artin p K Ω) a) :
  (PadicField.artin p (↥K') Ω) ((Units.map ↑(algebraMap K ↥K')) a) = (PadicField.ver p K') g
```

`PadicField.exists_lift_artin` supplies the required `g` for every `a`; it is part of the same closure.

## Closure build (16/16 EXIT=0)

| module | EXIT | sec | source SHA256 (adapted) | olean bytes | olean SHA256 |
|---|---:|---:|---|---:|---|
| Brauer.ContH2 | 0 | 74.5 | 241EC43BCD96DECBDF0FC5D2201B0F260780AB8F565084D2420FF02CEFA70DC0 | 1447392 | 331D5CDC138A24D09E34ADED502BEF15CEB3BD2DCDFEF0ACC223CF8A48179DD7 |
| Brauer.Cyclic | 0 | 81.3 | A2BDA3064242DC534E963BB429AE9F8E0DB610B2270368BB6E803F3D1C91201C | 903056 | 6A02F240882588DE3AB0D43A8E5B687008DA92E78B33136784C3C2440105512E |
| Brauer.Relative | 0 | 73.3 | 31E27620D05E5202A6B5632B7EAA17F53B7DC0D1428B62E6B972565E35A94C3D | 617680 | C78D5EF68D9E299B73B5A9FF089C40007B8753B68FE655B179F3160BA9AA54BA |
| Brauer.Absolute | 0 | 93.2 | 86CD365989DD2C3E52FA79DD009885FA7753A851361C001DA66BD33FB3E71658 | 1150872 | 33FB6D1BF42518B0D6AF225BC6A7491AE449EC72C06E2D2E04BF09557F168747 |
| Brauer.Unramified | 0 | 78.7 | 8E19AEF43CF1D434FF0465F53769BBE9E1F39F6C748134218C4AF356529F61E6 | 1342888 | 193F0A1363CF8B44B8ED307543CF640CE8376417115708816FA4F69FDC8869E4 |
| Brauer.Restriction | 0 | 75.2 | 3815EBAFBCF2EE3D22C73323BF581D65CB41E101DBE8B7750283ABE9EBE6C2DB | 1423560 | 01334C2DCEA5976E3D224F54E90C8B684AEBB651C90B468BD93DD958D2E519E3 |
| Brauer.InfRes | 0 | 82.5 | 7434D583A609D6435A4B49C1FF632E533A99634C51AAED1B1FFD89992B3C9E09 | 965352 | 1C74C70DFAB246580E9F708C472587E832F61E424EE3227336F0E3D82D4D0A58 |
| Brauer.LocalGalois | 0 | 72.6 | 9FE32CC7597F3DC12CE1E62D8BDAC27663F9ACB74E08A9D6FD4245E5EB54AED9 | 1065320 | BFFE0214880AFDB4E53A1A539B868D9669C92130EA4647A405C372A9DE35AC69 |
| Brauer.OrderBound | 0 | 83.7 | C0CCF44EC7A05C2C478A25F40EF37592A5A2D04F238A0417183248646AC7E5A1 | 1116376 | 3CED54D4DF353E2F2E5445462F85A2B5DF67D88E0606C2705EDF503384317B2B |
| Brauer.Invariant | 0 | 68.3 | 8E179B4B7864544B42A227EB14271CF82106F632AC066B2B1E39FE06CE45C3BC | 989576 | 4AB07A8B2689C37C4FFD9B51F691F4F6415496F70624496725771AC10839C429 |
| Brauer.KummerH2 | 0 | 78.0 | 4C75857A1288DF8CD22487493AF4C84A59ED2D789CA0F1A5E8434219AA2686E0 | 972216 | B22B62FD50ACCFAC793792FC4F38E21623D93D379434A110E7565899F3423F6A |
| Brauer.Duality | 0 | 67.6 | DDE8887292C4CF761B2513AEA24977BBC51AF2944998D6DC5AE42306A4282946 | 1930320 | B38854F5560D10903112C66428604EF4083C926C029D38CDF7E2C843C50E61BB |
| Brauer.ArtinPairing | 0 | 55.7 | AEE0978564F78E19B985FB6633A550EAA4A65CCBA8929585D1FCF75FF5A00BD6 | 1200720 | E4EA3980D818D531CDF30501F2CC378B6CA1AA53C99EE1995BE6D78E9709F99A |
| Brauer.Corestriction | 0 | 77.4 | 312ACD855EB1CAD521313DA73FCD407E109B1B013A973BD45BD3509BBE5134FA | 629960 | 3DAD2BC04B5FD04AAEDBB3C11BB1659195222086EF5894C2194D517EA6632F5E |
| Brauer.CorBr | 0 | 71.3 | CE14DF1F60B4C5C35671699D4905DA541D621FEE1B12091B89D16606D7AA9D5E | 405144 | F6A2C5AA386608ACD32100FA8744608FC29E777FA2B0C34741EBE6895BBF6994 |
| Brauer.ArtinTransfer | 0 | 65.3 | F7D422B14286E8D399574C76446708903E51B39455017031B425408E84DA5162 | 1099768 | 68F95A3F04C0AF9A715D176BFED2044C5FF9B8F1676403FAFD00ABC5DE1CCA64 |

ContH2 was compiled first as the environment smoke test (EXIT=0, 74.5 s) and reused by the closure run. Every other closure module was compiled EXIT=0 on attempt 1. No retries were needed.

## Remaining Brauer modules (7/7 EXIT=0)

The seven files outside the ArtinTransfer import closure were also built after the target, so the whole copied directory has oleans:

| module | EXIT | sec | source SHA256 (adapted) | olean bytes | olean SHA256 |
|---|---:|---:|---|---:|---|
| Brauer.DualityH1 | 0 | 70.6 | CAA4497E42BB01E912A24EA0F2213B05619CF4DD96F5630A9E07C39A00BD0CF0 | 455912 | BBE9E8FB144A98C38B70E67CB142BBF643923E9B579D6BBB7C111335C0CAB53F |
| Brauer.FundamentalClass | 0 | 71.5 | 79720A44FEEF7C7B435ACF47D3FA687C20B7B7AB8D5019BD77A4D740C03EFB5E | 553592 | 0D90802466F9AC46854FFF0D6402DC9C48737C09F2C184E8AF77A2DED7977278 |
| Brauer.KummerCompat | 0 | 66.4 | 1625F14DC1B8E00E8E1D0315B84C85D6CF3414E547BEC0DD1F00D245C341F7C9 | 558552 | 3E9B794431CAFCCC828876D02A9A0512C31AC63EF881FCB99570F2CC155F3E79 |
| Brauer.MathlibBridge | 0 | 65.0 | A809EE90D215592218F5FCF9504880318866911EE0AECC86E7AB79FE8523949D | 228992 | C0F5168C9FCC4D335942145EEE4FB7C7583C38185D2B90808EC0A1F390835C5C |
| Brauer.H2ZHat | 0 | 65.7 | DC0937A3599F465B90CCC845278D636CCE5CB5C8F0AD894B11F11CF6BF615094 | 536408 | 3C4FCFCF518888AB1DF0DF4FCC3FFE7F5649BA0C90C875C7995E26AD6937C116 |
| Brauer.TateNakayama | 0 | 86.7 | 29DDAA4E548DBE3F2303C904217B0F343CE1813E8CF51B39F60BF80F75BBEFF4 | 1621840 | F1E5678E8C84E4F9F5432D2E6CCAF5EF17E467111B5EB4989030486F7A16A305 |
| Brauer.TateNakayamaDegrees | 0 | 65.8 | C85A27E28D31A107205A11D61A30B6A5B49B84168EFBAB984A390F3F23B8794C | 310776 | 313C41E39EF1ED11EB31874DDE0171B7A9E94A87AEB7A3F0584C2C61A6998F39 |

## Axioms

`lean --root D:/lean/tmp/local-cft-port .../_M2bAxiomProbe.lean` exited 0 (61.4 s). Full output: `tmp/local-cft-port/_m2b_axioms.log`. Every probed declaration reports exactly:

```
[propext, Classical.choice, Quot.sound]
```

Probed: `ContH2.transfer_eq_prod_kappa`, `PadicField.corChar`, `PadicField.uSum`, `PadicField.corLocChar`, `PadicField.corBr_carryClass`, `PadicField.pairing_corLocChar`, `PadicField.ver`, `Brauer.corBr`, `PadicField.invEquiv_corBr`, `PadicField.artin_transfer`. No `sorryAx`.

## Import smoke test

`lake env lean --root D:/lean/tmp/local-cft-port .../_M2bImportSmoke.lean` exited 0; that is `import Brauer.ArtinTransfer` plus `#check`/`#print axioms` using only the project LEAN_PATH. The olean is therefore importable through the normal project environment.

## Boundaries / not claimed

- This package supplies the transfer theorem and the Brauer closure oleans. It does not prove S2027 M2b or assume any `LocalArtinSourceData`; the downstream bridge and consumer checks remain with the parent/consumer.
- Build was a direct `lean -o` topological build, not `lake build`. `lakefile.toml` now registers `Brauer` with `srcDir = "tmp/local-cft-port"`, but a full `lake build Brauer.ArtinTransfer` was not run; the manually built oleans have no Lake `.trace` files.
- No mathematical source content was edited. Only import prefixes changed; the original external file SHA256 is recorded above.
- Machine-readable evidence: `tmp/local-cft-port/_m2b_results_all.json`, `_m2b_build.tsv`, `_m2b_olean_manifest.json`, `_m2b_axioms.log`, and the build script `_m2b_build.mjs`.

