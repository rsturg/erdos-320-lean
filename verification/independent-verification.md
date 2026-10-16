# Fresh release verification

**Result: passed on 2026-10-16 UTC.** A fresh release directory, populated with
the unchanged original development sources, reproduced the
complete theorem `Erdos320.erdos_320`, its exact expected type, and its kernel
replay without changing any proof source or dependency configuration. This is
an automated project verification pass, not independent human review or an
alternative proof kernel.

## Exact statement

`IndependentAudit.lean` spells out the literal cardinality of the image of the
powerset of `{1,...,N}` under the rational reciprocal-subset-sum map, including
the empty subset. It checks this definition against `S` by reflexivity and
elaborates the full two-sided theorem at that literal count. The positive
constants are chosen before the eventual quantifier over natural `N`.

The product starts with `log₃ N`, stops before a factor at most two, and uses
every required factor. `fullLogProduct_stable` proves that every height `k≥N`
gives the same product for `N≥2`. The final theorem has no mathematical
hypotheses and no fixed-depth restriction. See the actual
[expected-type and axiom output](independent-expected-type-axioms.log).

## Clean source build and immutable inputs

The release initially had no `.lake` directory and **zero project `.olean`
files**. All 14 Git dependencies were freshly resolved from the committed
manifest; every actual `HEAD` matched its immutable pin. No `lake update` was
run. Principal revisions are:

| Input | Revision |
| --- | --- |
| Lean | 4.31.0, compiler `68218e876d2a38b1985b8590fff244a83c321783` |
| Mathlib | `db127794c79fdeb86f6b0cf6ff2c804026fbaff1` |
| PrimeNumberTheoremAnd | `6739793850d3eaa031e3543ed72d7f026f8080f5` |
| LeanArchitect | `f38c848196b0467e7b9dcc3d129a866b4051c23c` |

The recorded PowerShell commands included:

```powershell
$env:LEAN_NUM_THREADS = '2'
lake env lean --version
$roots = Get-Content verification/independent-mathlib-cache-roots.txt
lake exe cache get @roots
lake build
lake env lean verification/IndependentAudit.lean
python scripts/audit.py --lean --fingerprints verification/source-fingerprints.json --output verification/release-audit.json
```

The official Mathlib cache supplied **3,530 artifacts** for the recorded
82 Mathlib import roots and their dependency closure. The project and the
14 imported PNT plus 9 Architect modules were compiled from source. The default
`lake build` passed **3,614 jobs**, exit 0, from 03:59:30 to 04:07:54 UTC, with
zero compiler warning or error lines. It compiled 42 own modules including the
import-only root shim. The three remaining audit-only modules were then
[source-compiled sequentially](independent-additional-modules.json), each with
`lake env lean -o <recorded olean> <recorded source>`, all exit 0.

[Build log](independent-standard-build.log) ·
[build exit](independent-standard-build-exit.json) ·
[fresh environment](independent-environment-before.json) ·
[all dependency heads](independent-dependency-pins.json) ·
[module counts](independent-build-module-counts.json).

## Type, axiom, source, and dependency checks

Both the standalone expected-type check and the portable audit passed, exit 0.
For the final theorem, product-stability theorem, and explicitly typed expected
theorem, the transitive axiom set was exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The [strict portable audit](release-audit.json) also passed all 46 canonical-LF
source fingerprints, 14 clean tracked Git checkouts, license hashes, 23 imported
PNT/Architect Git-blob and SHA-256 identities, and the exact dependency import
closure. A separate comment/string-aware
[original-source trust scan](independent-original-trust-scan.json) found no
executable `unsafe`, `partial`, `run_tac`, `run_meta`, `elab`, `macro`, or
`implemented_by` tokens in those original files.

Final raw-byte comparisons after replay confirmed **all 45 project Lean files
and all three toolchain/Lake configuration files unchanged**:
[comparison](independent-source-and-manifest-comparison.json),
[source hashes](independent-proof-sources-after.json),
[configuration hashes](independent-manifests-after.json).

## Kernel replay

This official command passed, exit 0, from 04:16:16 to 04:26:18 UTC:

```powershell
$env:LEAN_NUM_THREADS = '1'
lake env leanchecker -v Erdos320 PrimeNumberTheoremAnd Architect
```

The [actual output](independent-kernel-replay-bulk.log) contains **68 unique
modules**, exactly matching the expected scope: **45 project, 14 PNT,
9 Architect**. The [scope summary](independent-kernel-replay-summary.json)
checks that no module was missing, extra, or duplicated. The recorded peak
working set was 1,660.76 MiB; shared-host memory pressure was handled with one
runtime worker, and replay completed successfully. The
[97-sample resource record](independent-kernel-replay-resources.json) and
[resource summary](independent-kernel-replay-resource-summary.json) preserve
the measurements.

Five individual invocations had already passed, including `Erdos320.Final`.
The initial 67-invocation loop was intentionally stopped during `Lower` startup
to avoid repeated full filesystem scans, then replaced by the complete command
above. It is not reported as 67 completed separate checks. The
[adaptation record](independent-replay-adaptation.json) preserves this history
and a corrected non-proof metadata-record typo. Neither change altered proof
source or verification results.

## Trust boundary

Lean's official checker replays safe, nonpartial declarations, including
private/server data and constructor/recursor checks. It skips unsafe or partial
metaprogramming implementations by design. The original mathematical proof
terms were checked; no claim is made to kernel-verify every tactic's executable
implementation. Imported Mathlib/cache infrastructure was not rebuilt or
replayed from an empty environment. Lean's kernel/compiler, standard axioms,
the pinned imported infrastructure, official cache mechanism, OS, and hardware
remain trusted.

Public evidence uses project-relative paths; initial checkout prefixes in the
cache-import inventory were normalized without changing mathematical output,
exit status, or source hashes. Proof verification establishes neither prize
priority nor award eligibility.
