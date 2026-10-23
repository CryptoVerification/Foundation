#!/usr/bin/env python3
"""Measure reused client proofs for identical complete-state correspondence.

Run inside `nix develop path:.`. Both methods import the SAME precompiled
libraries; those libraries are built before any measurement. This experiment
measures client checking, not library construction, kernel proof-term size,
native caller runtime, or human proof-maintenance effort. It is intentionally
permissive about lemma sharing for the ordinary baseline.
"""
import argparse
import hashlib
import json
import platform
import statistics
import subprocess
import tempfile
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SOURCES = [
    "Foundation/Crypto/Logic/Polygraph/OracleProofEdits.lean",
    "Foundation/Crypto/Logic/Polygraph/OracleLocalEdits.lean",
    "Foundation/Constructions/Symmetric/RandomFunctionMACProofSyntax.lean",
    "Foundation/Constructions/Symmetric/RandomFunctionMACProofEdits.lean",
    "Foundation/Examples/OracleProofEditsBaseline.lean",
    "Foundation/Examples/ScheduleCertificate.lean",
]
PRELUDE = """import Foundation.Examples.OracleProofEditsBaseline
import Foundation.Constructions.Symmetric.RandomFunctionMACProofEdits
import Foundation.Examples.ScheduleCertificate
open CryptoOracle CryptoOracle.ProofEdits Foundation.Symmetric.RandomFunctionMACProofEdits
def padded : Nat → Program (Fin 8) (Fin 256) (Fin 8 × Fin 256)
  | 0 => Foundation.Symmetric.RandomFunctionMACSchedules.Examples.attack
  | n + 1 => .query 0 (fun _ => padded n)
"""
PROOFS = {
    "ordinary": "Baseline.cached_eq (padded {n}) RandomOracle.oracle lazy_cache_laws [] []",
    "elementary": "(localCachedRoutes (padded {n})).sound RandomOracle.oracle lazy_cache_laws [] [] (knows_nil [])",
}


def run(command):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(f"{command!r} failed\n{result.stdout}\n{result.stderr}")
    return result.stdout.strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runs", type=int, default=3)
    parser.add_argument("--output", type=Path,
                        default=ROOT / "docs/experiments/oracle-proof-edits-benchmark.json")
    args = parser.parse_args()
    if args.runs < 3:
        parser.error("Use at least three measured repetitions.")
    run(["lake", "build", "Foundation.Examples.OracleProofEditsBaseline",
         "Foundation.Constructions.Symmetric.RandomFunctionMACProofEdits",
         "Foundation.Examples.ScheduleCertificate"])
    records, clients = [], {}
    with tempfile.TemporaryDirectory(prefix="foundation-proof-edits-") as directory:
        cases = []
        for n in (0, 4, 16):
            for method, proof in PROOFS.items():
                key = f"{method}-{n}"
                source = PRELUDE + f"""theorem check :
    (before (padded {n})).run RandomOracle.oracle [] [] =
      (cached (padded {n})).run RandomOracle.oracle [] [] :=
  {proof.format(n=n)}
"""
                path = Path(directory) / f"{key}.lean"
                path.write_text(source)
                clients[key] = {"source": source, "bytes": len(source.encode()),
                                "proof_application_lines": 1}
                cases.append((method, n, path))
        # One unmeasured warm-up per exact client, including all imports.
        for _, _, path in cases:
            run(["lake", "env", "lean", str(path)])
        for repetition in range(args.runs):
            # Reverse order on alternate repetitions to expose order effects.
            ordered = cases if repetition % 2 == 0 else list(reversed(cases))
            for method, n, path in ordered:
                start = time.perf_counter()
                run(["lake", "env", "lean", str(path)])
                elapsed = time.perf_counter() - start
                record = {"method": method, "extra_signing_queries": n,
                          "repetition": repetition, "elapsed_seconds": elapsed}
                records.append(record)
                print(json.dumps(record), flush=True)
    summaries = []
    for n in (0, 4, 16):
        for method in PROOFS:
            values = [r["elapsed_seconds"] for r in records
                      if r["method"] == method and r["extra_signing_queries"] == n]
            summaries.append({"method": method, "extra_signing_queries": n,
                              "measured_runs": len(values),
                              "median_seconds": statistics.median(values),
                              "min_seconds": min(values), "max_seconds": max(values)})
    report = {
        "scope": "client checking with common precompiled libraries and unrestricted lemma sharing",
        "excluded": ["library construction", "kernel proof-term size", "human proof-maintenance effort",
                     "native machine runtime", "asymptotic separation", "novelty judgment"],
        "platform": platform.platform(), "lean": run(["lake", "env", "lean", "--version"]),
        "git_head": run(["git", "rev-parse", "HEAD"]),
        "source_sha256": {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
                          for name in SOURCES},
        "unmeasured_warmups_per_client": 1, "clients": clients,
        "records": records, "summaries": summaries,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Saved {len(records)} measurements to {args.output}", flush=True)


if __name__ == "__main__":
    main()
