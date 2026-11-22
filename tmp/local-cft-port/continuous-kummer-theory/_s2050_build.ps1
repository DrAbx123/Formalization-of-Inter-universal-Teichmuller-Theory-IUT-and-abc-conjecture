param(
  [string]$root = 'D:\lean\tmp\local-cft-port\continuous-kummer-theory'
)
$ErrorActionPreference = 'Continue'
$env:LEAN_PATH = $root
Set-Location 'D:\lean'
$log = Join-Path $root '_s2050_logs'
New-Item -ItemType Directory -Force $log | Out-Null
$summary = Join-Path $log 'summary.tsv'
if (Test-Path $summary) { Remove-Item $summary }
$order = @(
  'ContinuousKummerTheory.Hilbert90',
  'ContinuousKummerTheory.ContH1.Basic',
  'ContinuousKummerTheory.ContH1.Comparison',
  'ContinuousKummerTheory.ContH1.Corestriction',
  'ContinuousKummerTheory.ContH1.CorestrictionIndep',
  'ContinuousKummerTheory.Kummer.Basic',
  'ContinuousKummerTheory.Kummer.Equiv',
  'ContinuousKummerTheory.Kummer.Restriction',
  'ContinuousKummerTheory.Kummer.Corestriction',
  'ContinuousKummerTheory.Kummer.CorRes',
  'ContinuousKummerTheory.Kummer.Values',
  'ContinuousKummerTheory.Kummer.Specialization',
  'ContinuousKummerTheory.Kummer.Decomposition',
  'ContinuousKummerTheory.Kummer.Limit',
  'ContinuousKummerTheory.Kummer.ZHat',
  'ContinuousKummerTheory.Kummer.ProfiniteCompletion',
  'ContinuousKummerTheory.Kummer.Topology',
  'ContinuousKummerTheory.Kummer.PAdic',
  'ContinuousKummerTheory'
)
foreach ($m in $order) {
  $rel = ($m -replace '\.', '\') + '.lean'
  $src = Join-Path $root $rel
  $out = Join-Path $root (($m -replace '\.', '\') + '.olean')
  $lg = Join-Path $log ($m + '.log')
  if (Test-Path $out) { Remove-Item $out -Force }
  $sw = [System.Diagnostics.Stopwatch]::StartNew()
  $cmdline = 'lake env lean -R "' + $root + '" -o "' + $out + '" "' + $src + '" 2>&1'
  $output = & cmd /c $cmdline
  $code = $LASTEXITCODE
  $sw.Stop()
  $output | Out-File -FilePath $lg -Encoding utf8
  $line = $m + [char]9 + $code + [char]9 + [math]::Round($sw.Elapsed.TotalSeconds,1) + [char]9 + $lg
  Add-Content -Path $summary -Value $line
  Write-Output $line
}
Write-Output 'S2050_BUILD_DONE'
