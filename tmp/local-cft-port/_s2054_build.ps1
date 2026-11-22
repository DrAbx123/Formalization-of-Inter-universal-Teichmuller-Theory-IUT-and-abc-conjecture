param([string[]]$mods = @())
$ErrorActionPreference = 'Continue'
$srcRoot = 'D:\lean\tmp\local-cft-port\continuous-kummer-theory'
$outRoot = 'D:\lean\.lake\build\lib\lean'
$logDir  = 'D:\lean\tmp\local-cft-port\_s2054_logs'
New-Item -ItemType Directory -Force $logDir | Out-Null
Set-Location 'D:\lean'
foreach ($m in $mods) {
  $rel = $m.Replace('.', '\')
  $src = Join-Path $srcRoot ($rel + '.lean')
  $out = Join-Path $outRoot ($rel + '.olean')
  $attempt = 0; $ok = $false; $code = $null; $secs = 0
  while (($attempt -lt 4) -and (-not $ok)) {
    $attempt++
    $o = Join-Path $logDir ($m + '.a' + $attempt + '.stdout')
    $e = Join-Path $logDir ($m + '.a' + $attempt + '.stderr')
    $sw = [Diagnostics.Stopwatch]::StartNew()
    $argl = @('env','lean','-j1','-R',$srcRoot,'-o',$out,$src)
    $p = Start-Process -FilePath 'lake.exe' -ArgumentList $argl -NoNewWindow -PassThru -RedirectStandardOutput $o -RedirectStandardError $e
    $done = $p.WaitForExit(2400000)
    $sw.Stop()
    if (-not $done) { try { $p.Kill($true) } catch {}; $code = -999 } else { $code = $p.ExitCode }
    $secs = [math]::Round($sw.Elapsed.TotalSeconds, 1)
    Add-Content (Join-Path $logDir 'summary.tsv') ('MODULE=' + $m + ' ATTEMPT=' + $attempt + ' EXIT=' + $code + ' SECONDS=' + $secs)
    if ($code -eq 0) { $ok = $true }
    else {
      $txt = ((Get-Content $o -Raw -ErrorAction SilentlyContinue) + ' ' + (Get-Content $e -Raw -ErrorAction SilentlyContinue))
      if ($txt -match 'failed to read file|bad_alloc|not enough memory|resource temporarily unavailable|locked|being used by another process') { Start-Sleep -Seconds 20 } else { break }
    }
  }
  if ($ok -and (Test-Path $out)) {
    $fs = (Get-Item $out).Length
    $sha = (Get-FileHash $out -Algorithm SHA256).Hash
    Add-Content (Join-Path $logDir 'summary.tsv') ('RESULT=' + $m + ' OK EXIT=0 OLEAN=' + $fs + ' SHA256=' + $sha)
    Write-Output ('OK ' + $m + ' EXIT=0 SECONDS=' + $secs + ' OLEAN=' + $fs + ' SHA256=' + $sha)
  } else {
    Add-Content (Join-Path $logDir 'summary.tsv') ('RESULT=' + $m + ' FAIL EXIT=' + $code)
    Write-Output ('FAIL ' + $m + ' EXIT=' + $code)
  }
}
Write-Output 'S2054_BUILD_DONE'
