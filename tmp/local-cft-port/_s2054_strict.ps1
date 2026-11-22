$ErrorActionPreference='Continue'
Set-Location 'D:\lean'
$src = 'D:\lean\tmp\local-cft-port\continuous-kummer-theory\ContinuousKummerTheory\Kummer\PAdic.lean'
$root = 'D:\lean\tmp\local-cft-port\continuous-kummer-theory'
$outDir = 'D:\lean\tmp\local-cft-port\_s2054_strict'
New-Item -ItemType Directory -Force $outDir | Out-Null
$out = Join-Path $outDir 'PAdic.olean'
$o = 'D:\lean\tmp\local-cft-port\_s2054_logs\PAdic.strict.stdout'
$e = 'D:\lean\tmp\local-cft-port\_s2054_logs\PAdic.strict.stderr'
$args = @('env','lean','-j1','-DrelaxedAutoImplicit=false','-DmaxSynthPendingDepth=3','-Dpp.unicode.fun=true','-R',$root,'-o',$out,$src)
$sw=[Diagnostics.Stopwatch]::StartNew()
$p = Start-Process -FilePath 'lake.exe' -ArgumentList $args -NoNewWindow -PassThru -RedirectStandardOutput $o -RedirectStandardError $e
$p.WaitForExit(1200000) | Out-Null
$sw.Stop()
Write-Output ('STRICT_EXIT=' + $p.ExitCode + ' SECONDS=' + [math]::Round($sw.Elapsed.TotalSeconds,1))
if (Test-Path $out) { Write-Output ('STRICT_OLEAN=' + (Get-Item $out).Length + ' SHA256=' + (Get-FileHash $out -Algorithm SHA256).Hash) }
Write-Output '--- stdout ---'
Get-Content $o -Raw -ErrorAction SilentlyContinue
Write-Output '--- stderr ---'
Get-Content $e -Raw -ErrorAction SilentlyContinue
