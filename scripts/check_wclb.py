"""Build the libraries and verify their statement map for the pinned WC.pdf."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

from check_complete import without_comments

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
PAPER_SHA256 = "002d3616e51469ac2bbc2c12a3e40236b3214cdc1409e3b9bee7cb3e0df63c9c"
# Numbered headings transcribed from the printed pages of the pinned PDF.
HEADINGS = [
    ("theorem", 1, 3), ("definition", 1, 4), ("definition", 2, 5),
    ("definition", 3, 5), ("definition", 4, 5), ("definition", 5, 5),
    ("theorem", 2, 6), ("condition", 1, 7), ("lemma", 1, 8),
    ("lemma", 2, 10), ("lemma", 3, 11), ("lemma", 4, 11),
    ("proposition", 1, 12), ("lemma", 5, 13), ("lemma", 6, 13),
    ("lemma", 7, 14), ("proposition", 2, 14), ("fact", 1, 15),
    ("lemma", 8, 15), ("proposition", 3, 18), ("lemma", 9, 18),
    ("proposition", 4, 22), ("lemma", 10, 23), ("lemma", 11, 26),
]


def fail(message):
    raise SystemExit(f"INCOMPLETE: {message}")


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command, env, quiet=False):
    result = subprocess.run(command, cwd=ROOT, env=env, capture_output=True,
                            text=True, encoding="utf-8", errors="replace")
    if not quiet or result.returncode:
        print(result.stdout, end="")
        print(result.stderr, end="", file=sys.stderr)
    if result.returncode:
        raise SystemExit(result.returncode)
    return result.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", type=Path, help="verify these PDF bytes against the pinned manuscript")
    args = parser.parse_args()
    coverage = json.loads((ROOT / "wclb_coverage.json").read_text(encoding="utf-8"))
    if (coverage["source"], coverage["sha256"], coverage["pages"]) != ("WC.pdf", PAPER_SHA256, 30):
        fail("wrong manuscript identity in the coverage map")
    if args.paper is not None and (not args.paper.is_file() or sha256(args.paper) != PAPER_SHA256):
        fail("the supplied PDF does not match the manuscript used for this statement map")
    items = coverage["items"]
    if [(i["environment"], i["number"], i["page"]) for i in items] != HEADINGS:
        fail("coverage does not match the numbered headings and pages in the pinned PDF")

    sources = [p for lib in ("WC", "WCLB")
               for p in [ROOT / f"{lib}.lean", *sorted((ROOT / lib).rglob("*.lean"))]]
    source_paths = {p.relative_to(ROOT).as_posix() for p in sources}
    mapped = set()
    for i in items:
        if (i["status"] not in {"proved", "formalized"} or not i["declarations"] or
                not i["modules"] or not set(i["modules"]) <= source_paths):
            fail(f"missing proof or module mapping for {i['environment']} {i['number']}")
        mapped.update(i["declarations"])

    imports = {}
    for p in sources:
        code = without_comments(p.read_text(encoding="utf-8-sig"))
        if re.search(r"\b(sorry|admit|axiom|opaque|unsafe)\b", code):
            fail(f"proof escape in {p.relative_to(ROOT)}")
        module = ".".join(p.relative_to(ROOT).with_suffix("").parts)
        imports[module] = re.findall(r"^import\s+((?:WC|WCLB)(?:\.\w+)*)\s*$", code, re.M)
    reachable, todo = set(), ["WC", "WCLB"]
    while todo:
        module = todo.pop()
        if module not in reachable:
            reachable.add(module)
            todo.extend(imports[module])
    if missing := imports.keys() - reachable:
        fail(f"modules outside checked umbrellas: {sorted(missing)}")

    check = ROOT / "scripts" / "check_wclb_coverage.lean"
    targets = set(re.findall(r"^#print axioms ([\w.]+)$", without_comments(check.read_text()), re.M))
    if missing := mapped - targets:
        fail(f"no axiom check for {sorted(missing)}")

    env = dict(os.environ)
    lake = shutil.which("lake")
    if lake is None:
        tc = (ROOT / "lean-toolchain").read_text().strip().replace("/", "--").replace(":", "---")
        bindir = Path.home() / ".elan" / "toolchains" / tc / "bin"
        lake = str(bindir / ("lake.exe" if os.name == "nt" else "lake"))
        env["PATH"] = str(bindir) + os.pathsep + env.get("PATH", "")
    run([lake, "--log-level=error", "build"], env)
    output = run([lake, "env", "lean", "-DautoImplicit=false", str(check)], env, quiet=True)
    reports = {n: set(filter(None, (a.strip() for a in axioms.split(","))))
               for n, axioms in re.findall(r"^'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output, re.M)}
    for n in re.findall(r"^'([^']+)' does not depend on any axioms", output, re.M):
        reports[n] = set()
    if reports.keys() != targets:
        fail(f"missing or unexpected axiom reports: {sorted(reports.keys() ^ targets)}")
    for n, axioms in reports.items():
        if extra := axioms - ALLOWED:
            fail(f"unexpected axioms in {n}: {sorted(extra)}")

    receipt = {
        "verified_at_utc": datetime.now(timezone.utc).isoformat(), "result": "passed",
        "theorem": coverage["main_theorem"], "paper_sha256": PAPER_SHA256,
        "supplied_pdf_hash_verified": args.paper is not None,
        "numbered_statements_checked": len(items), "mapped_declarations_checked": len(mapped),
        "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "allowed_axioms": sorted(ALLOWED), "axiom_dependencies": {n: sorted(v) for n,v in sorted(reports.items())},
        "source_sha256": {p.relative_to(ROOT).as_posix(): sha256(p) for p in
                          [*sources, ROOT / "wclb_coverage.json", check, Path(__file__).resolve()]},
    }
    (ROOT / "verification_wclb.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {len(items)} numbered statements; {len(mapped)} mapped declarations; "
          f"{len(reports)} transitive axiom checks.")
    if args.paper:
        print(f"PDF bytes verified: {PAPER_SHA256}")


if __name__ == "__main__":
    main()
