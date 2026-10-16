# Verification record

The complete target is `Erdos320.erdos_320`, with the exact rational counting function and the manuscript's full stopping-threshold-2 product. Verification was performed on 2026-10-16 UTC before public submission. The selected public proof SHA is named in the awards PR; source fingerprints identify the exact checked files independently of Git metadata.

## Statement and coverage

A separate agent reviewed `Core.lean`, `Statement.lean`, and `Final.lean` against the original problem and manuscript. It found no missing case, hidden mathematical assumption, or fixed-depth truncation. The [semantic review](../verification/final-statement-review.md) records the definitions, quantifiers, threshold comparison, sufficient-height argument, and reviewed file hashes.

The standalone [IndependentAudit.lean](../verification/IndependentAudit.lean) independently spells out the rational image-cardinality definition and elaborates the expected two-sided eventual theorem. The portable [audit script](../scripts/audit.py), run with `--lean`, performs another fixed expected-type check and requires the transitive axioms of the result, product-stability theorem, and expected-type theorem to be precisely the standard three.

## Fresh release build

The release directory initially had no `.lake` directory or project build artifacts. Dependencies were freshly resolved from the committed 14-package Git manifest, with every checkout `HEAD` checked. The official Mathlib cache supplied 3,530 Mathlib-cache artifacts for the recorded 82-root import cone, including imported support-package artifacts. The original proof and all imported PNT/Architect modules were compiled from source with Lean 4.31.0, compiler commit `68218e876d2a38b1985b8590fff244a83c321783`, on Windows, using two Lean runtime workers.

The default **`lake build` passed all 3,614 jobs**, reporting:

```text
'Erdos320.erdos_320' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3614 jobs).
```

[Build log](../verification/independent-standard-build.log), [exit record](../verification/independent-standard-build-exit.json), [initial environment](../verification/independent-environment-before.json), [pre-build manifest hashes](../verification/independent-manifests-before.json), and [source fingerprints](../verification/source-fingerprints.json) preserve the evidence. The imported `MediumPNT` was also freshly source-built and printed the same three standard axioms.

The standalone audit and portable release audit both passed. The official `leanchecker` then passed all **68 unique selected modules**: 45 project modules, 14 PNT modules, and nine Architect modules, with one runtime worker. [Replay output](../verification/independent-kernel-replay-bulk.log) and [exit record](../verification/independent-kernel-replay-bulk-exit.json) preserve the result. The separate automated verifier's [detailed report](../verification/independent-verification.md) explains the exact scope and the switch from individual invocations to a batch that avoids repeated file discovery. A workflow definition alone is not verification evidence.

## Dependency and source audit

The selected public proof commit is **`93e88e53935c8a18c421425efa797576d895fd85`**. Its 46 canonical Lean fingerprints, 45 raw project-source hashes, and all three raw toolchain/Lake configuration hashes match the verified inputs: [committed-source check](../verification/selected-commit-source-check.json). The later submission-record commit adds documentation and evidence without changing those proof inputs.

The comment/string-aware guard covers all 45 original project Lean files plus the standalone verification file. It rejects executable proof holes and added axiom declarations. The audit checks all 14 immutable Git revisions, clean tracked dependency files, license hashes, 23 PNT/Architect source blob and SHA-256 identities, and the exact imported closure. [Dependency provenance](../verification/dependency-provenance.json) and [dependency documentation](DEPENDENCIES.md) record these checks. Canonical LF fingerprints make the source check independent of Windows newline conversion.

The [root static audit](../verification/root-static-audit.json) independently passed against the fresh release dependency checkouts. The final portable run, exact-statement output, and replay evidence are linked in the detailed verifier report. Checkout-specific absolute path prefixes in public evidence are normalized to relative paths or a documented placeholder; mathematical output and exit status are not changed.

## Trust boundary and interpretation

The [GitHub Actions Linux reproduction](https://github.com/rsturg/erdos-320-lean/actions/runs/38851143985) for that exact public proof commit also **passed** on Ubuntu 24.04: pinned toolchain installation, the recorded import-cone cache, a fresh original-source `lake build`, manifest retention, and the full portable source/dependency/type/axiom audit. [Remote job-step evidence](../verification/github-ci-jobs.json) records success. The 68-module explicit kernel replay reported above was performed in the Windows verification pass; the Linux run is a separate fresh build and audit.

The transitive final-theorem axiom audit excludes proof holes and custom unproved mathematical assumptions reaching through imported theorems. The kernel replay checks safe kernel-checkable declarations at the recorded module scope; the official replay tool skips unsafe and partial implementations, including some metaprogramming utilities. It checks the generated mathematical proof terms and is part of Lean, not an alternate kernel implementation. The entire cached Mathlib/Lean environment was not rebuilt or replayed from an empty environment. Lean's compiler/kernel, its standard axioms, the pinned imported infrastructure, the official Mathlib cache mechanism, operating system, and hardware remain part of the stated trust boundary.

This verification is an AI-assisted project self-check, including a separate automated review pass. No independent human review or organizer acceptance is claimed. Successful formal verification does not establish personal contribution, first-formalizer priority, legal consent, prize eligibility, or payment. Those remain subject to the official process.

## Prior-proof audit

Earlier Star Fleet and plby sources are disclosed in [PRIOR_WORK.md](PRIOR_WORK.md). Static statement/source inspections established relevant earlier complete-looking targets. A separate Star Fleet source-build reproduction reached progress 120 of 131 planned modules before it was deliberately stopped to release memory for this project's verification. Its final target and axiom audit were not independently completed. This is an incomplete reproduction, not a verification failure or evidence of a defect. Its publisher's own verification claims are not presented as our independently observed result. The plby project was not independently clean-built in this project. These limitations are not assertions that either earlier proof is defective.
