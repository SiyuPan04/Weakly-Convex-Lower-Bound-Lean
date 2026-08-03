# Weakly Convex Lower Bound — Lean 4 Formalization

[![Lean CI](https://github.com/SiyuPan04/Weakly-Convex-Lower-Bound-Lean/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/SiyuPan04/Weakly-Convex-Lower-Bound-Lean/actions/workflows/lean.yml)

This repository is a standalone Lean 4 verification of a deterministic
first-order oracle lower bound for weakly convex optimization. Its only Lean
package dependency is
[Mathlib](https://github.com/leanprover-community/mathlib4).

## Verified result

For positive `G`, `rho`, `Delta`, and `eps`, under

```text
eps^2 <= (1 / 7680) * min(G^2, rho * Delta),
```

the development proves a worst-case query lower bound for deterministic
algorithms using exact function values and the full set-valued
`rho`-subdifferential. The problem class consists of `G`-Lipschitz,
`rho`-weakly convex functions with initial gap at most `Delta`; stationarity is
the norm of the genuine Fréchet gradient of the literal Moreau envelope.

The principal endpoint is

```lean
WeaklyConvexLowerBound.paperProblemClass_fullOracle_lowerBound_and_rate
```

It combines the formal query lower bound with

```text
(1 / 47185920) * G^2 * min(rho * Delta, G^2) / eps^4 <= paperT.
```

The formalization also proves an arbitrary-output endpoint: every
deterministic output rule used before `paperT` oracle replies can be forced to
return a point whose stationarity exceeds `eps`.

```lean
WeaklyConvexLowerBound.paperProblemClass_outputAt_failure_before_paperT_all
```

The fixed-function zero-respecting theorem is exposed as

```lean
WeaklyConvexLowerBound.zeroRespectingMain
```

The published lower-bound endpoints are unconditional apart from the stated
numerical assumptions: no formula bridge or oracle-selection hypothesis is
left as an input.

## Build and verify

Install Lean with [elan](https://github.com/leanprover/elan), then run:

```bash
git clone https://github.com/SiyuPan04/Weakly-Convex-Lower-Bound-Lean.git
cd Weakly-Convex-Lower-Bound-Lean
lake update
lake exe cache get
lake build
lake env lean WeaklyConvexLowerBound/AxiomAudit.lean
```

On Windows, the full local check is also available as:

```powershell
powershell -ExecutionPolicy Bypass -File .\VERIFY.ps1
```

`VERIFY.ps1` performs a project build, checks root-module coverage, runs the
axiom audit, rejects
proof placeholders and project-defined axioms, checks that every Lean import
comes from Mathlib or this package, and rejects private absolute paths.

## Trust and scope

- The source contains no `sorry`, `admit`, `sorryAx`, `opaque` declaration, or
  project-defined `axiom`.
- `WeaklyConvexLowerBound/AxiomAudit.lean` prints the logical dependencies of
  all principal endpoints.
- The oracle is the literal full set-valued oracle, not a selected
  representative subgradient.
- The Moreau stationarity field is connected to an actual Fréchet derivative,
  not an uninterpreted surrogate.
- The present package verifies deterministic results; it does not claim a
  randomized lower bound.

## Source layout

- `Foundation/`: self-contained Euclidean, differentiability, frame,
  hidden-direction, arithmetic, and smooth-step lemmas.
- `FullOracleModel.lean`, `Framework.lean`: causal dimension-wise deterministic
  algorithms and the exact full-oracle model.
- `HardInstance.lean` through `FullSubdiffCharacterization.lean`: hard function,
  regularity, locality, and full-subdifferential semantics.
- `MoreauSemantics.lean`, `AmbientMoreauSemantics.lean`: literal Moreau envelope
  and genuine gradient bridge.
- `BatchResisting.lean`, `UniformResistingOracle.lean`: deterministic resisting
  construction.
- `UnconditionalMain.lean`, `PaperOutput.lean`: final lower-bound and
  arbitrary-output theorems.
- `AxiomAudit.lean`: explicit logical-dependency audit.

The project pins Lean and Mathlib versions in `lean-toolchain` and
`lake-manifest.json` for reproducible builds.

## License

This project is released under the [MIT License](LICENSE).
