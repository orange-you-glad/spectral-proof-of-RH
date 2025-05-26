# Lean Formalization of the Spectral Reformulation of the Riemann Hypothesis

This directory contains the Lean 4 formalization of the canonical operator-theoretic equivalence with the Riemann Hypothesis (RH), as introduced in the paper:

> **A Canonical Spectral Determinant and Spectral Equivalence Formulation of the Riemann Hypothesis**  
> R.A. Jacob Martone, 2025  
> [[PDF]](../docs/spectral_determinant_RH_equivalence_v0.99.98.pdf)

## 📐 Structure

The formalization is modular and parallels the analytic architecture of the paper:

```

lean/
├── Bourbaki/
│   ├── RH/
│   │   ├── CanonicalOperator.lean        -- Definition of L\_sym via convolution
│   │   ├── DeterminantIdentity.lean      -- Zeta-regularized determinant identity
│   │   ├── SpectralBijection.lean        -- Mapping ζ-zeros to eigenvalues
│   │   ├── Equivalence.lean              -- RH ⇔ spectrum of L\_sym ⊆ ℝ
│   │   └── ...                           -- Additional lemmas and support
├── Main.lean                             -- Imports and orchestrates the proof
├── lakefile.lean                         -- Lake project file
├── lean-toolchain                        -- Specifies Lean version (via elan)
└── README.md                             -- You are here

````

## 🚧 Status

| Module                         | Status         |
|-------------------------------|----------------|
| Canonical operator \( L_{\mathrm{sym}} \) | ✅ Constructed |
| Determinant identity           | ✅ Verified    |
| Spectral bijection             | ✅ Proven      |
| RH ⇔ spectrum real             | ✅ Complete    |
| Heat-kernel reconstruction     | ⏳ In progress |

We enforce `sorry`-free commits via GitHub CI (see [`.github/workflows/lean.yml`](https://github.com/orange-you-glad/spectral-proof-of-RH/blob/main/.github/workflows/lean.yml).

## 🛠 Build Instructions

To build or check the project locally:

```bash
lake build
````

To verify no unproven stubs remain:

```bash
grep -r 'sorry' .
```

## 📚 Dependencies

* [Lean 4](https://leanprover.github.io/)
* No external dependencies beyond core Lean and `lake`

Your Lean version is pinned via:

```
lean-toolchain → leanprover/lean4:stable
```

## 📜 License

MIT © R.A. Jacob Martone
Formalization and micro-audits contributed via collaborative CI.
