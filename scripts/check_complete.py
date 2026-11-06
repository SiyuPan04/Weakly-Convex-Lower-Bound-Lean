"""Completion gate for the full manuscript, not just the current partial library."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys

for stream in (sys.stdout, sys.stderr):
    if hasattr(stream, "reconfigure"):
        stream.reconfigure(encoding="utf-8", errors="replace")

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def without_comments(source: str) -> str:
    output, i, depth = [], 0, 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        else:
            output.append(source[i])
            i += 1
    return "".join(output)


def run(command: list[str], env: dict[str, str]) -> str:
    result = subprocess.run(command, cwd=ROOT, env=env, text=True,
                            encoding="utf-8", errors="replace", capture_output=True)
    print(result.stdout, end="")
    print(result.stderr, end="", file=sys.stderr)
    if result.returncode:
        raise SystemExit(result.returncode)
    return result.stdout


def main() -> None:
    for path in sorted((ROOT / "WC").rglob("*.lean")):
        code = without_comments(path.read_text(encoding="utf-8-sig"))
        forbidden = re.search(r"\b(sorry|admit|axiom)\b", code)
        if forbidden:
            raise SystemExit(f"INCOMPLETE: forbidden proof escape {forbidden[0]} in {path}")
    target = ROOT / "WC" / "Main.lean"
    if not target.exists():
        raise SystemExit("INCOMPLETE: WC/Main.lean and the proved WC.main theorem do not exist yet.")
    reachable, pending = set(), ["WC"]
    while pending:
        module = pending.pop()
        if module in reachable:
            continue
        reachable.add(module)
        path = ROOT / (module.replace(".", "/") + ".lean")
        for imported in re.findall(r"^import\s+(WC(?:\.[\w]+)*)\s*$",
                                   without_comments(path.read_text(encoding="utf-8-sig")), re.M):
            pending.append(imported)
    sources = sorted((ROOT / "WC").rglob("*.lean"))
    missing = [str(p.relative_to(ROOT)) for p in sources
               if ".".join(p.relative_to(ROOT).with_suffix("").parts) not in reachable]
    if missing:
        raise SystemExit(f"INCOMPLETE: modules outside the checked umbrella: {missing}")
    env = dict(os.environ)
    lake = shutil.which("lake")
    if not lake:
        toolchain = (ROOT / "lean-toolchain").read_text().strip().replace("/", "--").replace(":", "---")
        bindir = Path.home() / ".elan" / "toolchains" / toolchain / "bin"
        lake = str(bindir / ("lake.exe" if os.name == "nt" else "lake"))
        env["PATH"] = str(bindir) + os.pathsep + env.get("PATH", "")
    run([lake, "--log-level=error", "build"], env)
    audit = ROOT / "scripts" / "_completion_check.lean"
    audit.write_text("import WC.Main\n#check (WC.main : WC.Model.MainTheorem)\n#print axioms WC.main\n", encoding="utf-8")
    try:
        output = run([lake, "env", "lean", str(audit)], env)
    finally:
        audit.unlink(missing_ok=True)
    match = re.search(r"depends on axioms:\s*\[([^\]]*)\]", output, re.S)
    if match:
        axioms = {a.strip() for a in match[1].split(",") if a.strip()}
        unexpected = axioms - ALLOWED_AXIOMS
        if unexpected:
            raise SystemExit(f"INCOMPLETE: unexpected main-theorem axioms: {sorted(unexpected)}")
    elif "does not depend on any axioms" not in output:
        raise SystemExit("INCOMPLETE: could not verify the main theorem's axiom report.")
    receipt = {
        "verified_at_utc": datetime.now(timezone.utc).isoformat(),
        "theorem": "WC.main : WC.Model.MainTheorem",
        "axioms": sorted(axioms if match else []),
        "lean_source_modules": len(sources),
        "source_snapshot_sha256": hashlib.sha256(
            (ROOT / "snapshot" / "rand2_revised.tex").read_bytes()).hexdigest(),
        "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "source_sha256": {str(p.relative_to(ROOT)).replace("\\", "/"):
                          hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in [ROOT / "WC.lean", *sources]},
        "result": "passed"
    }
    (ROOT / "verification.json").write_text(
        json.dumps(receipt, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print("COMPLETE: the full WC.main theorem compiled and passed the axiom gate.")


if __name__ == "__main__":
    main()
