#!/usr/bin/env python3
"""Freeze/check a source snapshot, then build and verify the BB84 audits.

Run with Python 3.9+ and Lake/Elan installed. Generated logs and the source
archive go to --output, outside the checked source tree.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[2]
MANIFEST = ROOT / "docs/quantum/artifact-manifest.json"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
AUDITS = {
    "Foundation/Quantum/QKD/BB84PaperAudit.lean": "docs/quantum/paper-axioms.txt",
    "Foundation/Quantum/GoalAudit.lean": "docs/quantum/goal-axioms.txt",
}


def inputs():
    paths = [ROOT / p for p in (
        ".gitignore", "README.md", "Foundation.lean", "lean-toolchain",
        "lakefile.toml", "lake-manifest.json", "flake.nix", "flake.lock",
        "docs/quantum/reproduce.py",
    )]
    paths += list((ROOT / "Foundation").rglob("*.lean"))
    paths += list((ROOT / "docs").rglob("*.md"))
    paths += list((ROOT / "docs/quantum").glob("*axioms.txt"))
    return sorted({p.relative_to(ROOT).as_posix(): p for p in paths}.items())


def digest(data):
    return hashlib.sha256(data).hexdigest()


def snapshot():
    files = {name: digest(path.read_bytes()) for name, path in inputs()}
    identity = digest(json.dumps(files, sort_keys=True, separators=(",", ":")).encode())
    return {
        "schema": 1,
        "source_sha256": identity,
        "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "dependencies": json.loads((ROOT / "lake-manifest.json").read_text())["packages"],
        "files": files,
    }


def run(command, output):
    print("Running:", " ".join(command), flush=True)
    with output.open("w") as log:
        subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=True)
    return output.read_text()


def audit_declarations(text):
    pattern = re.compile(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
    found = {}
    for match in pattern.finditer(text):
        name, axioms = match.groups()
        used = {a.strip() for a in (axioms or "").split(",") if a.strip()}
        if not used <= ALLOWED:
            raise RuntimeError(f"Unexpected axioms for {name}: {sorted(used - ALLOWED)}")
        found[name] = sorted(used)
    if not found or "sorryAx" in text or re.search(r"\berror:", text):
        raise RuntimeError("Invalid/empty axiom audit")
    return found


def verify_dependencies():
    packages = json.loads((ROOT / "lake-manifest.json").read_text())["packages"]
    for package in packages:
        directory = ROOT / ".lake/packages" / package["name"]
        actual = subprocess.check_output(
            ["git", "-C", str(directory), "rev-parse", "HEAD"], text=True).strip()
        if actual != package["rev"]:
            raise RuntimeError(f"Dependency revision mismatch: {package['name']}: {actual}")
        changes = subprocess.check_output(
            ["git", "-C", str(directory), "status", "--porcelain", "--untracked-files=no"], text=True)
        if changes:
            raise RuntimeError(f"Modified dependency sources: {package['name']}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--freeze", action="store_true", help="write a new content-addressed manifest")
    parser.add_argument("--refresh-audits", action="store_true", help="regenerate expected audit outputs")
    args = parser.parse_args()
    out = args.output.resolve()
    if out == ROOT or ROOT in out.parents:
        parser.error("--output must be outside the source tree")
    out.mkdir(parents=True, exist_ok=True)
    if not args.freeze and args.refresh_audits:
        parser.error("--refresh-audits requires --freeze")
    if not args.freeze and snapshot() != json.loads(MANIFEST.read_text()):
        raise RuntimeError("Source snapshot differs from artifact-manifest.json")
    run(["lake", "build"], out / "build.log")
    verify_dependencies()
    version = run(["lake", "env", "lean", "--version"], out / "lean-version.txt")
    declared = (ROOT / "lean-toolchain").read_text().strip().split(":")[-1].removeprefix("v")
    if not re.search(r"\b" + re.escape(declared) + r"\b", version):
        raise RuntimeError("Lean executable version does not match lean-toolchain")
    all_declarations = {}
    for source, expected in AUDITS.items():
        text = run(["lake", "env", "lean", source], out / Path(expected).name)
        declarations = audit_declarations(text)
        source_text = (ROOT / source).read_text()
        requested = re.findall(r"^#print axioms (\S+)", source_text, re.MULTILINE)
        if not set(requested) <= declarations.keys():
            raise RuntimeError(f"Missing audit declarations in {source}")
        all_declarations[source] = declarations
        if args.refresh_audits:
            (ROOT / expected).write_text(text)
        elif text != (ROOT / expected).read_text():
            raise RuntimeError(f"Audit output differs: {expected}")
        print(f"Checked {len(declarations)} declarations: {source}", flush=True)
    current = snapshot()
    if args.freeze:
        MANIFEST.write_text(json.dumps(current, ensure_ascii=False, indent=2) + "\n")
    elif current != json.loads(MANIFEST.read_text()):
        raise RuntimeError("Source changed during verification")
    archive = out / f"bb84-{current['source_sha256'][:16]}.tar.gz"
    with tarfile.open(archive, "w:gz") as bundle:
        for name in [*current["files"], MANIFEST.relative_to(ROOT).as_posix()]:
            bundle.add(ROOT / name, arcname=f"bb84/{name}", recursive=False)
    report = {
        "source_sha256": current["source_sha256"],
        "archive": archive.name,
        "archive_sha256": digest(archive.read_bytes()),
        "lean_version": version.strip(),
        "audits": all_declarations,
    }
    (out / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Verified source SHA-256:", current["source_sha256"], flush=True)
    print("Source archive:", archive, flush=True)


if __name__ == "__main__":
    main()
