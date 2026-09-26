# Reproduction and endpoint verification

**Verification status: FULL_FINAL_ELABORATED_STANDARD_AXIOMS.** The complete seven-stage Lake build and all seven checks succeeded on the selected source bytes. Both full-type regression checks and exact-name transitive axiom audits passed. All nine dependency checkouts matched the locked revisions and were clean before and after the run; all driver-hashed source files remained unchanged. This is Lean verification by the build environment, not an independent mathematical review.

These instructions reproduce the checked proof inputs; actual output and evidence are recorded below.

## Fixed environment

Run from the root containing `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`. Required tools are Git, Python 3, and Elan/Lake with the exact Lean toolchain. Retain the manifest; do not run a dependency update or substitute a newer Lean or mathlib version.

- Lean: `leanprover/lean4:v4.33.0`.
- Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.
- All nine dependency revisions and repository URLs: `lake-manifest.json`. The locked `rev` values, rather than moving branch names in `inputRev`, determine the dependency versions.
- Build configuration: `lakefile.toml`.

## Fresh checkout

Clone the public repository and check out the exact proof-source commit below. This commit is contained in the main branch; later commits add documentation and verification evidence without changing the checked proof inputs.

```sh
git clone --single-branch --branch main https://github.com/peilinliu66-dev/jsp957-erdos1152-formalization jsp957-review
cd jsp957-review
git checkout --detach 5f77404a2c8869efa1797a93862d5da170925977
git rev-parse HEAD
lake env lean --version
python3 scripts/build_v6.py --cache
```

The optional `--cache` step obtains caches for the pinned dependencies. The cache is a trust dependency of that reproduction; record its use. If the dependencies are already installed, run `python3 scripts/build_v6.py`. To rebuild this project's targets in an existing checkout, first run `lake clean` and then the driver. Cleaning the project is not a claim to have rebuilt every upstream dependency from source.

The complete driver explicitly builds the Fejér grid, baseline/coarse/V3/V4 chain, small-scale field, Bernstein, sampling, weighted-family and final roots. It runs the regression, repair and analytic declaration checks as well as the endpoint checks. The strengthened release driver retains every stage and requires both the integer-excess and strict-ε endpoints.

## Explicit final checks

These commands separately check both complete endpoints:

```sh
lake build JSP957V5 JSP957Final
lake env lean checks/FinalStatement.lean
lake env lean checks/FinalAxioms.lean
lake env lean checks/StrictEpsilonStatement.lean
lake env lean checks/StrictEpsilonAxioms.lean
```

The two statement checks instantiate the full expected types independently, in addition to printing/checking the named theorems. The strict endpoint must use `ε (n + 1)` for the row with `n + 1` nodes, preserve the zero polynomial's `WithBot` degree, and select a single function before all polynomial sequences. The integer-excess endpoint remains checked separately.

The axiom checks execute these exact queries:

```lean
#print axioms Erdos1152.V5.ae_limsup_eq_top
#print axioms Erdos1152.V5.ae_limsup_eq_top_strict_epsilon
```

Actual output for the integer-excess endpoint:

```text
'Erdos1152.V5.ae_limsup_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Actual output for the strict-ε endpoint:

```text
'Erdos1152.V5.ae_limsup_eq_top_strict_epsilon' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These fields must contain genuine output for the exact named declarations. The driver's acceptance policy allows only `propext`, `Classical.choice`, `Quot.sound`, or a subset. This policy is not a prediction of the eventual output. Added unproved mathematical assumptions, `sorryAx`, missing axiom output and nonzero commands must fail acceptance.

## Evidence to retain

| Item | Release value |
| --- | --- |
| Selected public commit | `5f77404a2c8869efa1797a93862d5da170925977` |
| Verification time (UTC) | `2026-09-26T12:24:35.638381+00:00` |
| Run-specific receipt | `logs/v6/20260926T121829_907367Z/BUILD_RESULT.json` |
| Receipt SHA-256 | `899475250553c5acc4991fbc46477f544b8fcadaf60d7efe725b9b53c9bbaf99` |
| Full command logs | `logs/v6/20260926T121829_907367Z` |
| Complete verification conclusion | `FULL_FINAL_ELABORATED_STANDARD_AXIOMS` |

The driver writes a run-specific `logs/v6/<run>/BUILD_RESULT.json` and the latest summary `logs/v6/BUILD_RESULT_V6.json`. Retain the run-specific receipt and genuine command logs. Confirm the receipt's before/after source hashes match the selected source files and that all actual dependency revisions and dependency-cleanliness checks passed. Do not infer acceptance from a summary left by an earlier attempt, a dependency-only build, or an individual-module diagnostic.

For the strengthened final driver, acceptance requires exit code `0`, status `FULL_FINAL_ELABORATED_STANDARD_AXIOMS`, `unconditional_theorem_kernel_verified: true`, and `strict_epsilon_kernel_verified: true`, with both named axiom checks accepted and sources unchanged during the run. Interrupted, failed, or source-changing runs are not successful evidence. Missing strict-endpoint fields indicate that the required strengthened release check has not been established.

Lean verification relies on the selected Lean implementation and imported dependency artifacts. It does not by itself establish external mathematical review, authorship, priority, or prize acceptance. The mathematical correspondence and complete argument are recorded in [STATEMENT_CORRESPONDENCE.md](STATEMENT_CORRESPONDENCE.md) and [PROOF_GUIDE.md](PROOF_GUIDE.md).
