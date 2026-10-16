$ErrorActionPreference = 'Stop'
$modules = [System.Collections.Generic.HashSet[string]]::new()
$mathlibRoots = [System.Collections.Generic.HashSet[string]]::new()
$queue = [System.Collections.Generic.Queue[string]]::new()
Get-ChildItem -LiteralPath 'Erdos320' -Filter '*.lean' -Recurse | ForEach-Object {
  $queue.Enqueue($_.FullName)
}
$queue.Enqueue((Join-Path (Get-Location).Path 'Erdos320.lean'))
$sourceRecords = [System.Collections.Generic.List[object]]::new()
$checkout = (Get-Location).Path
while ($queue.Count -gt 0) {
  $file = $queue.Dequeue()
  if (-not $modules.Add($file)) { continue }
  $sourceRecords.Add([pscustomobject]@{ path=$file.Substring($checkout.Length+1).Replace('\','/'); sha256=(Get-FileHash -LiteralPath $file -Algorithm SHA256).Hash.ToLowerInvariant() })
  foreach ($line in (Get-Content -LiteralPath $file)) {
    if ($line -match '^\s*(?:public\s+)?import\s+([A-Za-z0-9_.]+)') {
      $name = $Matches[1]
      if ($name.StartsWith('Mathlib.')) { [void]$mathlibRoots.Add($name); continue }
      $localRoot = $null
      if ($name.StartsWith('PrimeNumberTheoremAnd.')) { $localRoot = '.lake/packages/PrimeNumberTheoremAnd' }
      elseif ($name -eq 'Architect' -or $name.StartsWith('Architect.')) { $localRoot = '.lake/packages/LeanArchitect' }
      if ($null -ne $localRoot) {
        $path = Join-Path $localRoot ($name.Replace('.', '/') + '.lean')
        if (-not (Test-Path -LiteralPath $path)) { throw "Missing source $path" }
        $queue.Enqueue((Resolve-Path -LiteralPath $path).Path)
      }
    }
  }
}
$sourceRecords | Sort-Object path | ConvertTo-Json -Depth 5 | Set-Content -LiteralPath 'verification/independent-cache-import-cone.json' -Encoding utf8
$mathlibRoots | Sort-Object | Set-Content -LiteralPath 'verification/independent-mathlib-cache-roots.txt' -Encoding utf8
[pscustomobject]@{mathlib_root_count=$mathlibRoots.Count; source_files_read=$modules.Count; pnt_files_read=($sourceRecords | Where-Object {$_.path -match 'packages[\\/]PrimeNumberTheoremAnd[\\/]'}).Count; architect_files_read=($sourceRecords | Where-Object {$_.path -match 'packages[\\/]LeanArchitect[\\/]'}).Count} | ConvertTo-Json | Set-Content -LiteralPath 'verification/independent-cache-cone-summary.json' -Encoding utf8
