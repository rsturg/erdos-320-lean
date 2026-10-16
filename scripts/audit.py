#!/usr/bin/env python3
"""Audit the pinned Erdős 320 release. Uses only Python's standard library.

Run after `lake build`: python3 scripts/audit.py --lean
This is a reproducibility and source guard, not an independent proof kernel.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile


ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(r"\b(?:sorry|admit|axiom|sorryAx|native_decide|ofReduceBool)\b")
EXPECTED_AUDIT = r'''import Erdos320

namespace ReleaseVerification

def explicitCount (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.image
    (fun B : Finset ℕ => ∑ n ∈ B, (n : ℚ)⁻¹)).card

example (N : ℕ) : Erdos320.S N = explicitCount N := rfl

example (N : ℕ) : Erdos320.fullLogProduct N =
    Erdos320.stoppedProductAt 2 N (Real.log (Real.log (N : ℝ))) := rfl

theorem expected_erdos_320 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ N : ℕ in Filter.atTop,
      c * ((N : ℝ) / Real.log N) * Erdos320.fullLogProduct N ≤
          Real.log (explicitCount N : ℝ) ∧
      Real.log (explicitCount N : ℝ) ≤
          C * ((N : ℝ) / Real.log N) * Erdos320.fullLogProduct N :=
  Erdos320.erdos_320

#print axioms Erdos320.erdos_320
#print axioms Erdos320.fullLogProduct_stable
#print axioms ReleaseVerification.expected_erdos_320

end ReleaseVerification
'''


class AuditError(Exception):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AuditError(message)


def read_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8-sig"))


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(repo: Path, *args: str, binary: bool = False):
    p = subprocess.run(["git", "-C", str(repo), *args], capture_output=True)
    require(p.returncode == 0, f"Git check failed in dependency {repo.name}: {args[0]}")
    return p.stdout if binary else p.stdout.decode("utf-8").strip()


def clean_lean(source: str) -> str:
    """Mask line comments, nested block comments and string literals.

    Preserve newlines and positions for diagnostics. Unterminated comments or
    strings fail closed; Lean itself supplies the complete syntax check.
    """
    out = list(source)
    i, n = 0, len(source)
    while i < n:
        if source.startswith("--", i):
            j = source.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                out[k] = " "
            i = j
        elif source.startswith("/-", i):
            start, depth = i, 1
            i += 2
            while i < n and depth:
                if source.startswith("/-", i):
                    depth += 1
                    i += 2
                elif source.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            require(depth == 0, "Unterminated Lean block comment")
            for k in range(start, i):
                if source[k] != "\n":
                    out[k] = " "
        elif source[i] == '"':
            start = i
            i += 1
            while i < n:
                if source[i] == "\\":
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise AuditError("Unterminated Lean string literal")
            for k in range(start, min(i, n)):
                if source[k] != "\n":
                    out[k] = " "
        else:
            i += 1
    return "".join(out)


def imports(source: str) -> list[str]:
    result = []
    for line in clean_lean(source).splitlines():
        match = re.match(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)$", line)
        if match:
            result.extend(re.findall(r"[A-Za-z_][A-Za-z_0-9.]*", match.group(1)))
    return result


def forbidden_token(code: str):
    for match in FORBIDDEN.finditer(code):
        # Lean name quotations denote data. Architect's audit utility, for
        # example, erases the quoted name ``sorryAx from a collected NameSet.
        if match.start() and code[match.start() - 1] == "`":
            continue
        return match
    return None


def original_sources(root: Path) -> list[Path]:
    paths = [root / "Erdos320.lean"]
    paths += sorted((root / "Erdos320").rglob("*.lean"))
    paths += sorted((root / "verification").glob("*.lean"))
    require(all(p.is_file() for p in paths), "Missing original Lean source")
    return paths


def source_guard(root: Path) -> dict:
    files = {}
    for path in original_sources(root):
        raw = path.read_bytes()
        code = clean_lean(raw.decode("utf-8-sig"))
        bad = forbidden_token(code)
        name = path.relative_to(root).as_posix()
        require(bad is None, f"Forbidden executable token {bad.group(0) if bad else ''} in {name}")
        require(not re.search(r"\b(?:ResearchPNT|Research)\b", code),
                f"Unexpected competing-proof namespace in {name}")
        files[name] = sha256(raw.replace(b"\r\n", b"\n"))
    require(len(files) >= 2, "No original project source found")
    return {"filesChecked": len(files), "canonicalLfSha256": files}


def audit_dependencies(root: Path, provenance: dict, packages: Path, pnt_override: Path | None) -> dict:
    manifest = read_json(root / "lake-manifest.json")
    entries = manifest["packages"]
    expected = {x["name"]: x["lockedRev"] for x in provenance["dependencyAudit"]}
    expected["PrimeNumberTheoremAnd"] = provenance["pnt"]["commit"]
    require(len(entries) == len(expected) == 14, "Expected exactly 14 locked Git packages")
    require({x["name"] for x in entries} == set(expected), "Dependency name set changed")
    require((root / "lean-toolchain").read_text().strip() == provenance["proofToolchain"],
            "Lean toolchain differs from provenance")
    locations = {}
    checked = []
    for entry in entries:
        name, rev = entry["name"], entry["rev"]
        require(entry["type"] == "git", f"Non-Git dependency: {name}")
        require(re.fullmatch(r"[0-9a-f]{40}", rev) is not None, f"Non-immutable pin: {name}")
        require(rev == expected[name], f"Manifest revision changed: {name}")
        require(entry.get("subDir") in (None, ""), f"Unexpected dependency subdirectory: {name}")
        repo = pnt_override if name == "PrimeNumberTheoremAnd" and pnt_override else packages / name
        require(repo.is_dir(), f"Dependency checkout absent: {name}")
        require(git(repo, "rev-parse", "HEAD") == rev, f"Dependency HEAD differs: {name}")
        require(not git(repo, "status", "--porcelain", "--untracked-files=no"),
                f"Tracked dependency files changed: {name}")
        locations[name] = repo
        checked.append({"name": name, "revision": rev, "trackedFilesClean": True})

    # SHA-256 and Git blob identities use canonical committed bytes, so Windows
    # checkout line-ending conversion cannot create a false mismatch.
    for key, name in (("pnt", "PrimeNumberTheoremAnd"), ("architect", "LeanArchitect")):
        repo = locations[name]
        for item in provenance[key]["sourceFiles"]:
            path = item["path"]
            require(git(repo, "rev-parse", f"HEAD:{path}") == item["gitBlob"],
                    f"Source blob differs: {name}/{path}")
            raw = git(repo, "cat-file", "blob", f"HEAD:{path}", binary=True)
            require(sha256(raw) == item["sha256"], f"Source SHA-256 differs: {name}/{path}")
            # Upstream metaprogramming utilities legitimately implement tactics
            # using g.admit and inspect quoted axiom names. Do not mistake those
            # utilities for proof holes: the final transitive axiom check below
            # determines whether any such construction enters the target proof.
    for row in provenance["dependencyAudit"]:
        for license_file in row["licenses"]:
            raw = git(locations[row["name"]], "cat-file", "blob",
                      f"HEAD:{license_file['file']}", binary=True)
            require(sha256(raw) == license_file["sha256"],
                    f"License changed: {row['name']}/{license_file['file']}")
    require(git(locations["PrimeNumberTheoremAnd"], "cat-file", "blob", "HEAD:LICENSE", binary=True)
            .startswith(b"                                 Apache License"), "PNT Apache license missing")

    expected_modules = {}
    for key, name in (("pnt", "PrimeNumberTheoremAnd"), ("architect", "LeanArchitect")):
        for item in provenance[key]["sourceFiles"]:
            module = item["path"][:-5].replace("/", ".")
            expected_modules[module] = (name, item["path"])
    reached = set()
    todo = []
    for source in original_sources(root):
        todo += imports(source.read_text(encoding="utf-8-sig"))
    while todo:
        module = todo.pop()
        require(not module.startswith(("Research.", "ResearchPNT.")), "Competing-proof import found")
        if not (module == "Architect" or module.startswith(("Architect.", "PrimeNumberTheoremAnd."))):
            continue
        if module in reached:
            continue
        require(module in expected_modules, f"Imported PNT/Architect closure expanded: {module}")
        reached.add(module)
        name, path = expected_modules[module]
        raw = git(locations[name], "cat-file", "blob", f"HEAD:{path}", binary=True)
        todo += imports(raw.decode("utf-8-sig"))
    require(reached == set(expected_modules), "Recorded PNT/Architect import closure differs")
    return {"packages": checked, "pntModules": 14, "architectModules": 9,
            "sourceBlobAndSha256Checks": 23, "importClosureMatches": True,
            "licenseHashesMatch": True}


def audit_lean(root: Path, lake: str) -> dict:
    with tempfile.TemporaryDirectory(prefix="erdos320-audit-") as tmp:
        path = Path(tmp) / "ReleaseAudit.lean"
        path.write_text(EXPECTED_AUDIT, encoding="utf-8", newline="\n")
        result = subprocess.run([lake, "env", "lean", str(path)], cwd=root,
                                capture_output=True, text=True, encoding="utf-8")
    output = result.stdout + result.stderr
    require(result.returncode == 0, "Lean expected-type audit failed:\n" + output)
    records = {}
    pattern = r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]"
    for name, body in re.findall(pattern, output, re.DOTALL):
        axioms = {part.strip() for part in body.split(",") if part.strip()}
        require(axioms <= ALLOWED_AXIOMS, f"Unapproved axioms for {name}: {sorted(axioms - ALLOWED_AXIOMS)}")
        records[name] = sorted(axioms)
    expected = {"Erdos320.erdos_320", "Erdos320.fullLogProduct_stable",
                "ReleaseVerification.expected_erdos_320"}
    require(set(records) == expected, "Missing or extra axiom reports in Lean audit")
    require(all(set(v) == ALLOWED_AXIOMS for v in records.values()),
            "Expected exactly the three recorded standard axioms for audited targets")
    return {"expectedTypeChecked": True, "subsetSumDefinitionChecked": True,
            "thresholdTwoDefinitionChecked": True, "axioms": records}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=Path("."))
    parser.add_argument("--provenance", type=Path)
    parser.add_argument("--packages-dir", type=Path)
    parser.add_argument("--pnt-root", type=Path, help="Read-only alternate PNT checkout for audit reproduction")
    parser.add_argument("--fingerprints", type=Path, help="Require the recorded canonical-LF source fingerprints")
    parser.add_argument("--lean", action="store_true", help="Also elaborate exact expected type and print axioms")
    parser.add_argument("--lake", default="lake", help="Lake executable, default: lake on PATH")
    parser.add_argument("--output", type=Path, help="Write the same JSON report to this file")
    args = parser.parse_args()
    try:
        root = args.project.resolve()
        provenance = read_json(args.provenance or root / "verification" / "dependency-provenance.json")
        sources = source_guard(root)
        if args.fingerprints:
            recorded = read_json(args.fingerprints)
            require(sources == recorded, "Original source fingerprints differ from the recorded release")
        result = {"schema": "erdos320-release-audit-v1", "status": "passed",
                  "originalSourceGuard": sources,
                  "sourceFingerprintsMatch": True if args.fingerprints else "not requested",
                  "dependencies": audit_dependencies(root, provenance,
                       (args.packages_dir or root / ".lake" / "packages").resolve(),
                       args.pnt_root.resolve() if args.pnt_root else None),
                  "leanAudit": audit_lean(root, args.lake) if args.lean else "not requested"}
        text = json.dumps(result, indent=2, ensure_ascii=False) + "\n"
        if args.output:
            args.output.write_text(text, encoding="utf-8", newline="\n")
        print(text, end="")
        return 0
    except (AuditError, OSError, ValueError, KeyError) as exc:
        print(f"AUDIT FAILED: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
