param([string]$root = 'D:\lean\tmp\local-cft-port\continuous-kummer-theory')
$ErrorActionPreference = 'Continue'
$env:LEAN_PATH = $root
Set-Location 'D:\lean'
$log = Join-Path $root '_s2050_logs'
New-Item -ItemType Directory -Force $log | Out-Null
$summary = Join-Path $log 'summary4.tsv'
if (Test-Path $summary) { Remove-Item $summary }
$order = @(
  'ContinuousKummerTheory.ContH1.Basic',
  'ContinuousKummerTheory.Hilbert90',
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
  $rel = ($m -replace '\.','\') + '.lean'
  $src = Join-Path $root $rel
  $out = Join-Path $root (($m -replace '\.','\') + '.olean')
  $lg  = Join-Path $log ($m + '.log')
  $lgout = Join-Path $log ($m + '.out.log')
  $attempts = 0; $finalCode = -1; $note = ''; $secs = 0
  $fresh = $false
  if ((Test-Path $out) -and ((Get-Item $out).LastWriteTime -gt (Get-Item $src).LastWriteTime)) { $fresh = $true }
  if ($fresh) { $finalCode = 0; $note = 'cached-olean' }
  else {
    $ok = $false
    while ((-not $ok) -and ($attempts -lt 8)) {
      $attempts++
      if (Test-Path $out) { Remove-Item $out -Force }
      $sw=[System.Diagnostics.Stopwatch]::StartNew()
      $p = Start-Process -FilePath 'lake.exe' -ArgumentList @('env','lean','-R',$root,'-o',$out,$src) -NoNewWindow -PassThru -RedirectStandardOutput $lgout -RedirectStandardError $lg
      $done = $p.WaitForExit(1200000)
      $sw.Stop(); $secs = [math]::Round($sw.Elapsed.TotalSeconds,1)
      if (-not $done) { try { $p.Kill($true) } catch {} ; $code = -999; $note = 'timeout' } else { $code = $p.ExitCode }
      $finalCode = $code
      Add-Content -Path $lgout -Value ('EXIT=' + $code + ' SECONDS=' + $secs + ' ATTEMPT=' + $attempts)
      if ($code -eq 0) { $ok = $true; $note = '' }
      else {
        $txt = ((Get-Content $lgout -Raw -ErrorAction SilentlyContinue) + ' ' + (Get-Content $lg -Raw -ErrorAction SilentlyContinue))
        if ($txt -match 'failed to read file' -or $txt -match 'bad_alloc' -or $txt -match 'not enough memory' -or $txt -match 'resource temporarily unavailable') {
          $note = 'transient-read'
          Write-Output ('TRANSIENT ' + $m + ' attempt=' + $attempts + ' secs=' + $secs)
          Start-Sleep -Seconds ([math]::Min(60, 15 * $attempts))
        } else { $note = 'compile-error'; break }
      }
    }
  }
  $line = $m + [char]9 + $finalCode + [char]9 + 'att=' + $attempts + [char]9 + 'secs=' + $secs + [char]9 + $note
  Add-Content -Path $summary -Value $line
  Write-Output $line
}
Write-Output 'S2050_BUILD4_DONE'