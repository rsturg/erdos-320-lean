$ErrorActionPreference = 'Stop'
$env:LEAN_NUM_THREADS = '2'
$records = [System.Collections.Generic.List[object]]::new()
$log = 'verification/independent-kernel-replay.log'
$plan = [System.Collections.Generic.List[object]]::new()
$base = (Get-Location).Path
Get-ChildItem -LiteralPath 'Erdos320' -Filter '*.lean' -Recurse | Sort-Object FullName | ForEach-Object {
  $relative = $_.FullName.Substring($base.Length+1).Replace('\','/')
  $plan.Add([pscustomobject]@{group='own'; module=$relative.Substring(0,$relative.Length-5).Replace('/','.')})
}
$cone = Get-Content -Raw -LiteralPath 'verification/independent-cache-import-cone.json' | ConvertFrom-Json
foreach ($item in $cone) {
  if ($item.path -match '^\.lake/packages/PrimeNumberTheoremAnd/(.+)\.lean$') {
    $plan.Add([pscustomobject]@{group='pnt'; module=$Matches[1].Replace('/','.')})
  } elseif ($item.path -match '^\.lake/packages/LeanArchitect/(.+)\.lean$') {
    $plan.Add([pscustomobject]@{group='architect'; module=$Matches[1].Replace('/','.')})
  }
}
$plan | ConvertTo-Json -Depth 5 | Set-Content -LiteralPath 'verification/independent-kernel-replay-plan.json' -Encoding utf8
$prefixes = @($plan | ForEach-Object {
  $targetName = $_.module
  [pscustomobject]@{module=$targetName; planned_prefix_matches=@($plan | Where-Object {$_.module -eq $targetName -or $_.module.StartsWith($targetName+'.')} | ForEach-Object {$_.module})}
})
$prefixes | ConvertTo-Json -Depth 5 | Set-Content -LiteralPath 'verification/independent-kernel-replay-prefixes.json' -Encoding utf8
foreach ($target in $plan) {
  # The official checker treats a module argument as a namespace prefix.
  # Architect's umbrella therefore also replays its eight children; one
  # runtime worker keeps that umbrella invocation sequential as well.
  $expanded = @($plan | Where-Object {$_.module -eq $target.module -or $_.module.StartsWith($target.module+'.')})
  $threads = if ($expanded.Count -gt 1) { '1' } else { '2' }
  $env:LEAN_NUM_THREADS = $threads
  $start = [DateTime]::UtcNow
  $header = 'START ' + $target.group + ' ' + $target.module + ' ' + $start.ToString('o')
  $header | Tee-Object -FilePath $log -Append
  $output = @(lake env leanchecker -v $target.module 2>&1)
  $code = $LASTEXITCODE
  $output | Tee-Object -FilePath $log -Append
  $replayed = @($output | ForEach-Object { if ($_ -match '^replaying ([A-Za-z0-9_.]+)$') { $Matches[1] } })
  $end = [DateTime]::UtcNow
  $records.Add([pscustomobject]@{group=$target.group; module=$target.module; replayed_modules=$replayed; runtime_threads=[int]$threads; exit_code=$code; utc_start=$start.ToString('o'); utc_end=$end.ToString('o'); elapsed_seconds=[math]::Round(($end-$start).TotalSeconds,3)})
  $records | ConvertTo-Json -Depth 5 | Set-Content -LiteralPath 'verification/independent-kernel-replay-results.json' -Encoding utf8
  ('END ' + $target.module + ' exit=' + $code + ' seconds=' + [math]::Round(($end-$start).TotalSeconds,3)) | Tee-Object -FilePath $log -Append
  if ($code -ne 0) { exit $code }
}
exit 0
