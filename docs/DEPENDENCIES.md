# Dependency provenance and reproducibility

The proof toolchain is Lean `leanprover/lean4:v4.31.0`. The root `lake-manifest.json` pins all 14 installed packages to full Git commit identifiers. It contains no path dependencies. `verification/dependency-provenance.json` records every revision, license hash, and the imported PNT/Architect source hashes.

The analytic input is the original [PrimeNumberTheoremAnd repository](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/6739793850d3eaa031e3543ed72d7f026f8080f5), commit `6739793850d3eaa031e3543ed72d7f026f8080f5` (2026-07-10 22:48:02 UTC). Its [CITATION.cff](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/6739793850d3eaa031e3543ed72d7f026f8080f5/CITATION.cff) credits Alex Kontorovich and Terence Tao as project organizers; the source headers and Git history identify additional contributors. The project is distributed under [Apache-2.0](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/6739793850d3eaa031e3543ed72d7f026f8080f5/LICENSE). We use the original Git checkout, preserving its license and headers.

The selected theorem imports `PrimeNumberTheoremAnd.MediumPNT`. Its PNT closure contains 14 source modules and imports nine modules from [LeanArchitect](https://github.com/hanwenzhu/LeanArchitect/tree/f38c848196b0467e7b9dcc3d129a866b4051c23c), pinned to `f38c848196b0467e7b9dcc3d129a866b4051c23c` and licensed Apache-2.0. These 23 source files are listed by Git blob identifier and SHA-256 in the provenance record. All 14 PNT files, and its license, README, toolchain, Lake configuration and manifest, match that official upstream commit exactly. No competing Erdős 320 proof package is a dependency.

Mathlib is pinned to [db127794c79fdeb86f6b0cf6ff2c804026fbaff1](https://github.com/leanprover-community/mathlib4/tree/db127794c79fdeb86f6b0cf6ff2c804026fbaff1), licensed Apache-2.0. The upstream PNT package also requires `leancert`, `PrimeCert`, and `checkdecls`. They remain pinned installed package dependencies because we retain the original upstream configuration, although they are outside the imported `MediumPNT` proof closure. `PrimeCert` and `Cli` use MIT licenses; the other locked packages use Apache-2.0. Each checkout retains its own license. This is an audit of the target's imported proof closure, not a claim that every unused theorem in the entire upstream PNT repository is free of placeholders.

For additional source integrity evidence, the [official PNT source archive](https://codeload.github.com/AlexKontorovich/PrimeNumberTheoremAnd/zip/6739793850d3eaa031e3543ed72d7f026f8080f5) has 1,857,768 bytes and SHA-256 `f5b8e9aee7c7e4a2fa3e7800f78d7788598193a8597aad229bdba267bf72ea63`. The proof build uses Git, rather than this archive.

## Reproduce

Install Git, Python 3.10 or later, and [elan](https://github.com/leanprover/elan). In a fresh checkout of the selected release commit, run:

```sh
lake env lean --version
python3 scripts/fetch_mathlib_cache.py
lake build
python3 scripts/audit.py --lean --fingerprints verification/source-fingerprints.json
```

On Windows, use the installed Python executable if `python3` is unavailable. Retain the committed manifest: do not run `lake update` during reproduction. `lake env lean --version` clones dependencies at their locked revisions when needed. The portable audit checks the exact revisions against provenance. The cache helper passes the recorded 82 Mathlib roots to `lake exe cache get`; the fresh run fetched 3,530 official Mathlib-cache artifacts, including imported support-package artifacts. The original proof and the PNT/Architect closure are compiled from source. A build using previously compiled original project artifacts is not a fresh reproduction.

The audit scans every original Lean file and verification Lean file, masking strings and nested comments before rejecting executable `sorry`, `admit`, `axiom`, `sorryAx`, `native_decide`, and `ofReduceBool`. It checks the dependency manifest, checkout `HEAD`s, clean tracked dependency files, license hashes, and the precise PNT/Architect import closure. Canonical committed bytes are used for dependency hashes; original source fingerprints normalize CRLF to LF.

With `--lean`, it also elaborates a fixed expected theorem type with no mathematical hypotheses: the cardinality of the image of all subsets of `{1,...,N}` under rational reciprocal summation, bounded above and below for all sufficiently large natural `N` by positive constants times `(N / log N)` and the full product stopped at threshold 2. It checks the count and product aliases by definitional equality. It prints axioms for the theorem, the product-stability theorem, and the fixed expected-type theorem, and requires precisely `propext`, `Classical.choice`, and `Quot.sound`. This transitive final theorem audit excludes hidden extra assumptions reaching through dependencies. Source scanning is an additional guard; Lean elaboration and its kernel provide proof checking.

The CI workflow uses immutable top-level action commits recorded in `verification/ci-action-pins.json`. It disables reuse of GitHub project-build caches, obtains the Mathlib cache, runs `lake build`, and runs the same portable audit. CI helper software is separate from the mathematical dependency graph. A workflow definition is not evidence of a successful remote run; consult the actual Actions result for the selected commit.
