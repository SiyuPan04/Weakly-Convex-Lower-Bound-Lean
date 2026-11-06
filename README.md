# Weakly Convex Lower Bound — Lean 4 Formalization

[![Lean CI](https://github.com/SiyuPan04/Weakly-Convex-Lower-Bound-Lean/actions/workflows/lean.yml/badge.svg)](https://github.com/SiyuPan04/Weakly-Convex-Lower-Bound-Lean/actions/workflows/lean.yml)

A Lean 4 formalization of oracle complexity lower bounds for finding Moreau stationary points of Lipschitz, weakly convex functions. The `WCLB` (Weakly Convex Lower Bound) library builds on the analytic constructions and oracle model in `WC`.

## Main result

[`WCLB.main`](WCLB/Main.lean) proves `WCLB.Model.MainTheorem`. Its explicit version, `WCLB.main_explicit`, establishes

```math
\mathrm{OracleComplexity}(G,\rho,\Delta,\varepsilon,\nu)
\ge \frac{\rho G^2\Delta}{2^{29}\varepsilon^4}.
```

for positive $G,\rho,\Delta,\varepsilon$, every failure tolerance $\nu\in[0,1)$, and

```math
\varepsilon \le \frac{1}{512}\min\left\lbrace G,\sqrt{\rho\Delta}\right\rbrace,
\qquad
\Delta \le \frac{G^2}{\rho}\exp\left(\frac{G^2}{200\varepsilon^2}\right).
```

Here $G$ is the Lipschitz bound, $\rho$ is the weak convexity parameter, and $\Delta$ bounds the initial objective gap. The constants are independent of $\nu$.

The model covers randomized Borel algorithms with access to function values and the **complete Fréchet subdifferential**. Stationarity uses the gradient of the actual Moreau envelope. Algorithms may return an arbitrary Borel output, including a point they never queried.

## Formalized components

- Coupled hard instances, weak convexity, Lipschitz regularity, and the initial gap bound.
- Full subdifferential formulas, source geometry, and robust oracle locality.
- Terminal Moreau gradient barriers and the prescribed radial modification.
- Haar random rotations, adaptive concentration, and the logarithmic dimension bound for the randomized reduction.
- Scaling to the explicit oracle complexity lower bound.

The [coverage table](WCLB_COVERAGE.md) maps the manuscript's **22 listed formal statements**—definitions, the hard-instance condition, and theorem-level results—to Lean declarations. The machine-readable inventory is [`wclb_coverage.json`](wclb_coverage.json), and [`scripts/check_wclb_coverage.lean`](scripts/check_wclb_coverage.lean) checks the mapped declarations and selected transitive axiom dependencies.

## Build and verify

The project pins **Lean 4.32.0** and mathlib revision `11d11a11a667a8fa8ea19d9456fe059f683e308f`. Install [elan](https://github.com/leanprover/elan), then run from the repository root:

```sh
lake exe cache get
lake build
python3 scripts/check_wclb.py
```

To run the declaration coverage check directly:

```sh
lake env lean scripts/check_wclb_coverage.lean
```

The verification script checks source completeness, module reachability, the manuscript inventory, the build, and transitive axioms for key results. Its accepted axiom dependencies are the standard `propext`, `Classical.choice`, and `Quot.sound`; it writes a reproducibility receipt to `verification_wclb.json`.

## Repository layout

| Path | Purpose |
| --- | --- |
| [`WCLB/`](WCLB/) | Current manuscript model, constructions, randomized reduction, and main theorem |
| [`WC/`](WC/) | Shared analytic library, full oracle model, and scaling results |
| [`WCLB.lean`](WCLB.lean), [`WC.lean`](WC.lean) | Library entry points |
| [`WCLB_COVERAGE.md`](WCLB_COVERAGE.md) | Statement-to-declaration mapping |
| [`scripts/`](scripts/) | Build, coverage, and axiom verification |
| [`wclb_snapshot/`](wclb_snapshot/) | Fixed manuscript source and provenance |

## License

This project is licensed under the [MIT License](LICENSE).
