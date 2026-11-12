# Weakly Convex Lower Bound — Lean 4 Formalization

[![Lean CI](https://github.com/SiyuPan04/Weakly-Convex-Lower-Bound-Lean/actions/workflows/lean.yml/badge.svg)](https://github.com/SiyuPan04/Weakly-Convex-Lower-Bound-Lean/actions/workflows/lean.yml)

This repository formalizes the lower bound in **Optimal Oracle Complexity for Weakly Convex Optimization**, by Jiajin Li and Siyu Pan. The reference is the **November 12, 2026** version of `WC.pdf`. See the [Chinese overview](README_WCLB.md) and the [paper-to-Lean index](WCLB_COVERAGE.md).

## Main result

[`WCLB.main`](WCLB/Main.lean) proves [the paper's Theorem 2](WCLB/Model.lean). For positive $G,\rho,\Delta,\varepsilon$ and every failure tolerance $\nu\in[0,1)$,

```math
\mathcal T_{\varepsilon,\nu}\bigl(\mathcal A_{\mathrm{rand}},\mathcal F(G,\rho,\Delta)\bigr)
\ge \frac{\rho G^2\Delta}{2^{29}\varepsilon^4},
```

provided that

```math
\varepsilon \le \frac{1}{512}\min\left\lbrace G,\sqrt{\rho\Delta}\right\rbrace,
\qquad
\Delta \le \frac{G^2}{\rho}\exp\left(\frac{G^2}{200\varepsilon^2}\right).
```

Here $G$ bounds the Lipschitz constant, $\rho$ is the weak convexity parameter and $\Delta$ bounds the initial objective gap. The oracle returns both the objective value and the **entire Fréchet subdifferential**. An output may be any Borel function of the private seed and the previous replies. Success means $\lVert\nabla f_{1/(2\rho)}(x)\rVert\le\varepsilon$ at that output. [`WCLB.main_for_sufficiently_small`](WCLB/Main.lean) proves Theorem 1: for fixed positive $G,\rho,\Delta$, one accuracy cutoff works for every $\nu$.

## From the hard instance to the lower bound

- [The unscaled construction](WCLB/Verification.lean) satisfies Condition 1. The [source and terminal geometry](WCLB/Certificates.lean) and [subgradient bound away from the inactive set](WCLB/OffTerminal.lean) cover Fact 1 and the parts of Lemma 9 used to prove the gradient barrier.
- [The radial modification](WCLB/Radial.lean) uses the prescribed radius; [its exterior oracle](WCLB/RadialOracle.lean) gives the value and the complete subdifferential. These results yield Lemma 10.
- [Lemma 11 and the scaling step](WCLB/RandomizedReduction.lean) use the logarithmic dimension in (6.5). The probability bound holds jointly over a Haar frame and an independent private seed, for all $T$ queries and an arbitrary output. Averaging over frames gives one fixed instance on which the scaled algorithm fails simultaneously through time $T$. Theorem 2 uses this bound.

## Build and verify

The project pins **Lean 4.32.0** and mathlib revision `11d11a11a667a8fa8ea19d9456fe059f683e308f`. With [elan](https://github.com/leanprover/elan) installed, run from the repository root:

```sh
lake exe cache get
python3 scripts/check_wclb.py
```

To check a local copy of the paper as part of the same run, use `python3 scripts/check_wclb.py --paper /path/to/WC.pdf`. Its expected SHA-256 is:

```text
002d3616e51469ac2bbc2c12a3e40236b3214cdc1409e3b9bee7cb3e0df63c9c
```

The [inventory](wclb_coverage.json) maps **24 numbered statements** to Lean declarations: 5 definitions, 1 condition, 1 fact, 2 theorems, 11 lemmas and 4 propositions. The verifier builds the project, checks that the mapped declarations resolve and audits their transitive axioms against `propext`, `Classical.choice` and `Quot.sound`. It writes a local verification receipt to `verification_wclb.json`. The page references and descriptions in the [coverage table](WCLB_COVERAGE.md) document the mathematical correspondence; a successful build or matching PDF hash does not establish that correspondence on its own.

[`WCLB/`](WCLB/) contains the manuscript-facing definitions and theorems; [`WC/`](WC/) contains the underlying analysis, oracle model and scaling lemmas. The TeX files in [`wclb_snapshot/`](wclb_snapshot/) are an earlier manuscript version.

## License

[MIT License](LICENSE).
