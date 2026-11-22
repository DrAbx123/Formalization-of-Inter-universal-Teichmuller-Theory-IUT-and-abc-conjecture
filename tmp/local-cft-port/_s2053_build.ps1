$ErrorActionPreference = 'Continue'
$log = 'D:\lean\tmp\local-cft-port\_s2053_build.tsv'
$raw = 'D:\lean\tmp\local-cft-port\_s2053_build.raw.log'
$TAB = [char]9
$pkgs = 'D:\lean\.lake\packages'
$env:LEAN_PATH = @(
  "$pkgs\Cli\.lake\build\lib\lean",
  "$pkgs\batteries\.lake\build\lib\lean",
  "$pkgs\Qq\.lake\build\lib\lean",
  "$pkgs\aesop\.lake\build\lib\lean",
  "$pkgs\proofwidgets\.lake\build\lib\lean",
  "$pkgs\importGraph\.lake\build\lib\lean",
  "$pkgs\LeanSearchClient\.lake\build\lib\lean",
  "$pkgs\plausible\.lake\build\lib\lean",
  "$pkgs\mathlib\.lake\build\lib\lean",
  'D:\lean\.lake\build\lib\lean'
) -join ';'
$KROOT = 'D:/lean/tmp/local-cft-port/continuous-kummer-theory-main'
$PROOT = 'D:/lean/tmp/local-cft-port'
$OUT = 'D:\lean\.lake\build\lib\lean'
$tasks = @(
  @('ContinuousKummerTheory.Kummer.Corestriction','ContinuousKummerTheory/Kummer/Corestriction.lean',$KROOT),
  @('ContinuousKummerTheory.Kummer.ProfiniteCompletion','ContinuousKummerTheory/Kummer/ProfiniteCompletion.lean',$KROOT),
  @('ContinuousKummerTheory.Kummer.Topology','ContinuousKummerTheory/Kummer/Topology.lean',$KROOT),
  @('ContinuousKummerTheory.Kummer.Values','ContinuousKummerTheory/Kummer/Values.lean',$KROOT),
  @('ContinuousKummerTheory.Kummer.PAdic','ContinuousKummerTheory/Kummer/PAdic.lean',$KROOT),
  @('ContinuousKummerTheory.Kummer.Specialization','ContinuousKummerTheory/Kummer/Specialization.lean',$KROOT),
  @('ContinuousKummerTheory.Kummer.Decomposition','ContinuousKummerTheory/Kummer/Decomposition.lean',$KROOT),
  @('ContinuousKummerTheory.Kummer.CorRes','ContinuousKummerTheory/Kummer/CorRes.lean',$KROOT),
  @('ContinuousKummerTheory','ContinuousKummerTheory.lean',$KROOT),
  @('PadicField.PowIndex','PadicField/PowIndex.lean',$PROOT),
  @('PadicField.PowIndexPadic','PadicField/PowIndexPadic.lean',$PROOT)
)
"START $(Get-Date -Format o)" | Set-Content $raw
foreach ($t in $tasks) {
  $m = $t[0]; $rel = $t[1]; $root = $t[2]
  $src = "$root/$rel"
  $out = Join-Path $OUT ($m.Replace('.','\') + '.olean')
  New-Item -ItemType Directory -Force -Path (Split-Path $out) | Out-Null
  $srchash = (Get-FileHash $src -Algorithm SHA256).Hash
  $done = $false
  for ($i = 1; $i -le 5; $i++) {
    $sw = [Diagnostics.Stopwatch]::StartNew()
    $o = (& lean -j1 -R $root -o $out $src 2>&1 | Out-String)
    $code = $LASTEXITCODE
    $sw.Stop()
    $sec = [math]::Round($sw.Elapsed.TotalSeconds,1)
    ("ATTEMPT $m try=$i exit=$code sec=$sec") | Add-Content $raw
    if ($code -eq 0) {
      $done = $true
      $b = if (Test-Path $out) { (Get-Item $out).Length } else { -1 }
      $oh = if (Test-Path $out) { (Get-FileHash $out -Algorithm SHA256).Hash } else { 'NONE' }
      (@($m,'EXIT=0',"SEC=$sec","OLEAN_BYTES=$b","OLEAN_SHA256=$oh","SRC_SHA256=$srchash") -join $TAB) | Add-Content $log
      break
    }
    if ($o.Trim().Length -gt 0) { ("----- OUTPUT $m try=$i -----") | Add-Content $raw; $o | Add-Content $raw }
    if ($o -match 'failed to read file|cannot open|could not read|object file .* does not exist') {
      ("TRANSIENT $m try=$i; sleeping") | Add-Content $raw
      Start-Sleep -Seconds 10
    } else { break }
  }
  if (-not $done) {
    (@($m,'EXIT=FAIL',"SRC_SHA256=$srchash") -join $TAB) | Add-Content $log
    ("HARDSTOP $m") | Add-Content $raw
    break
  }
}
"ALLDONE $(Get-Date -Format o)" | Add-Content $raw