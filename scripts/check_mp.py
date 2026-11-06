"""Verify the MP submission, its complete module graph and proof axioms."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys

from check_complete import without_comments

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
TARGETS = [
    "MP.main", "MP.main_explicit", "MP.construction_satisfies_conditions",
    "MP.radial_moreau_barrier", "MP.radial_exterior_oracle",
    "MP.Concentration.sphere_mgf_le",
    "MP.Concentration.adaptive_projection_tail_product",
    "MP.family_barrierEvent_measurable", "MP.randomized_reduction",
    "MP.terminal_stationarity",
]


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
    sources = sorted((ROOT / "WC").rglob("*.lean")) + sorted((ROOT / "MP").rglob("*.lean"))
    for path in sources:
        if re.search(r"\b(sorry|admit|axiom|opaque|unsafe)\b",
                     without_comments(path.read_text(encoding="utf-8-sig"))):
            raise SystemExit(f"INCOMPLETE: proof escape in {path}")
    reachable, todo = set(), ["WC", "MP"]
    while todo:
        module = todo.pop()
        if module in reachable:
            continue
        reachable.add(module)
        path = ROOT / (module.replace(".", "/") + ".lean")
        todo.extend(re.findall(r"^import\s+((?:WC|MP)(?:\.[\w]+)*)\s*$",
                              without_comments(path.read_text(encoding="utf-8-sig")), re.M))
    missing = [str(p.relative_to(ROOT)) for p in sources
               if ".".join(p.relative_to(ROOT).with_suffix("").parts) not in reachable]
    if missing:
        raise SystemExit(f"INCOMPLETE: modules outside checked umbrellas: {missing}")
    coverage = json.loads((ROOT / "mp_coverage.json").read_text(encoding="utf-8-sig"))
    unfinished = [i for i in coverage["items"] if i["status"] not in {"proved", "formalized"}]
    if unfinished:
        raise SystemExit(f"INCOMPLETE: {len(unfinished)} manuscript statements lack proofs")
    snapshot = ROOT / "mp_snapshot" / "main.tex"
    tex = re.sub(r"(?<!\\)%[^\n]*", "", snapshot.read_text(encoding="utf-8-sig"))
    inventory = []
    for entry in re.finditer(r"\\begin\{(theorem|lemma|proposition|corollary|definition|condition)\}"
                             r"(?:\[([^\]]*)\])?", tex):
        end = tex.find("\\end{" + entry[1] + "}", entry.end())
        if end < 0:
            raise SystemExit("INCOMPLETE: unclosed formal manuscript statement")
        inventory.append((entry[1], tex[:entry.start()].count("\n") + 1,
                          re.findall(r"\\label\{([^}]+)\}", tex[entry.end():end])))
    mapped_inventory = [(i["environment"], i["line"], i.get("labels", [])) for i in coverage["items"]]
    if inventory != mapped_inventory:
        raise SystemExit("INCOMPLETE: coverage does not match the manuscript's formal statements")
    mapped_names = {n for item in coverage["items"] for n in item.get("declarations", [])}
    checked_names = set(re.findall(r"^#check\s+@?([\w.]+)",
        (ROOT / "scripts" / "check_mp_coverage.lean").read_text(encoding="utf-8-sig"), re.M))
    if mapped_names - checked_names:
        raise SystemExit(f"INCOMPLETE: unchecked mapped declarations {sorted(mapped_names - checked_names)}")
    source_hash = hashlib.sha256(snapshot.read_bytes()).hexdigest()
    if source_hash != "29efd2ce9866a9b719b4b5d9865d3b216cacfe23823ce43fdd9114e11f670f13":
        raise SystemExit("INCOMPLETE: unexpected MP manuscript snapshot")
    env = dict(os.environ)
    lake = shutil.which("lake")
    if lake is None:
        tc = (ROOT / "lean-toolchain").read_text().strip().replace("/", "--").replace(":", "---")
        bindir = Path.home() / ".elan" / "toolchains" / tc / "bin"
        lake = str(bindir / ("lake.exe" if os.name == "nt" else "lake"))
        env["PATH"] = str(bindir) + os.pathsep + env.get("PATH", "")
    run([lake, "--log-level=error", "build"], env)
    check = ROOT / "scripts" / "_mp_check.lean"
    check.write_text("import MP\nexample : MP.Model.MainTheorem := MP.main\n" +
                     "\n".join(f"#print axioms {name}" for name in TARGETS) + "\n", encoding="utf-8")
    try:
        output = run([lake, "env", "lean", "-DautoImplicit=false", str(check)], env)
    finally:
        check.unlink(missing_ok=True)
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output, re.S)
    if {name for name, _ in reports} != set(TARGETS):
        raise SystemExit("INCOMPLETE: missing transitive axiom reports")
    for name, report in reports:
        if {x.strip() for x in report.split(",") if x.strip()} - ALLOWED:
            raise SystemExit(f"INCOMPLETE: unexpected axioms in {name}")
    run([lake, "env", "lean", "-DautoImplicit=false", "scripts/check_mp_coverage.lean"], env, quiet=True)
    print(f"All {len(coverage['items'])} manuscript coverage entries resolve against the checked Lean project.")
    checked = [ROOT / "WC.lean", ROOT / "MP.lean", *sources]
    receipt = {
        "verified_at_utc": datetime.now(timezone.utc).isoformat(),
        "result": "passed", "theorem": "MP.main : MP.Model.MainTheorem",
        "c0": "1/512", "c": "1/2^29", "manuscript_statements": len(coverage["items"]),
        "mp_modules": len(list((ROOT / "MP").rglob("*.lean"))),
        "manuscript_inventory_exact_match": True,
        "mapped_declarations_checked": len(mapped_names),
        "source_snapshot_sha256": source_hash,
        "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "axiom_targets": TARGETS, "allowed_axioms": sorted(ALLOWED),
        "source_sha256": {str(p.relative_to(ROOT)).replace("\\", "/"):
                          hashlib.sha256(p.read_bytes()).hexdigest() for p in checked},
    }
    (ROOT / "verification_mp.json").write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n",
                                              encoding="utf-8")
    print("COMPLETE: MP main, all manuscript coverage, exact logarithmic reduction and axiom checks passed.")


if __name__ == "__main__":
    main()
