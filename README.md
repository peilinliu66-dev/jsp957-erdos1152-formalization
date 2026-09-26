# JSP-000957 / Erdős Problem 1152

Lean 4 source for almost-everywhere divergence of polynomial interpolation with sublinear excess degree.

**Verification status: FULL_FINAL_ELABORATED_STANDARD_AXIOMS.** The complete seven-stage Lake build and all seven checks succeeded on the selected source bytes. Both full-type regression checks and exact-name transitive axiom audits passed. All nine dependency checkouts matched the locked revisions and were clean before and after the run; all driver-hashed source files remained unchanged. This is Lean verification by the build environment, not an independent mathematical review.

The evidence below records the complete canonical run, including both endpoints.

| Release evidence | Selected value |
| --- | --- |
| Intended proof repository | `https://github.com/peilinliu66-dev/jsp957-erdos1152-formalization` |
| Source branch | `main` |
| Full source commit | `412bf5f3bdff311fcd485459a394aadbcee8a103` |
| Verification time (UTC) | `2026-09-26T12:24:35.638381+00:00` |
| Complete build receipt | `logs/v6/20260926T121829_907367Z/BUILD_RESULT.json` |
| SHA-256 of that receipt | `899475250553c5acc4991fbc46477f544b8fcadaf60d7efe725b9b53c9bbaf99` |
| Mathematical review | `NOT INDEPENDENTLY REVIEWED; submitted argument requires review` |

The intended contribution account is [peilinliu66-dev](https://github.com/peilinliu66-dev); its selected repository and commit are the release fields above.

## Problem and scope

[JSP-000957](https://github.com/TheJustinSunPrize/awards/blob/1d1db84a39201357236183f0bbd620e2b220747e/problems/catalog-0901-1000.md#JSP-000957) refers to [Erdős Problem **1152**](https://www.erdosproblems.com/1152).
For every array of sets \(X_N\subset[-1,1]\) containing \(N\) distinct points and every real sequence \(\varepsilon_N\to0\), the requested conclusion is the existence of one real continuous function \(f\) such that **every** polynomial sequence satisfying

\[
\deg p_N<N(1+\varepsilon_N),\qquad p_N(t)=f(t)\quad(t\in X_N)
\]

has

\[
\limsup_{N\to\infty}|p_N(x)|=+\infty
\quad\text{for Lebesgue-almost every }x\in[-1,1].
\]

The same \(f\) is selected before all admissible sequences; the exceptional null set may depend on the sequence. No uniform spacing, node-separation condition, or prescribed convergence rate is assumed. The strict endpoint uses the degree of the zero polynomial as \(-\infty\), and includes every positive row size, even if some initial strict bounds are nonpositive.

The proof first targets the integer-excess formulation: for every \(r_N\in\mathbb N\) with \(r_N/N\to0\), obtain the same conclusion for all interpolants with \(\deg p_N\le N+r_N\). The strict formulation follows using the nonnegative integer majorant \(r_N=\lceil N|\varepsilon_N|\rceil\).

| Endpoint | Source and audit |
| --- | --- |
| `Erdos1152.V5.ae_limsup_eq_top` | `Erdos1152/V5/Main.lean`; `checks/FinalStatement.lean`; `checks/FinalAxioms.lean` |
| `Erdos1152.V5.ae_limsup_eq_top_strict_epsilon` | `Erdos1152/V5/StrictEpsilon.lean`; `checks/StrictEpsilonStatement.lean`; `checks/StrictEpsilonAxioms.lean` |

Strict endpoint integration and complete audit: **The strict endpoint is integrated in JSP957Final.lean. Its actual complete build, independent expected-type check and transitive axiom audit all passed in the same canonical run as the integer-excess endpoint.**. Both complete types and the indexing are explained in [STATEMENT_CORRESPONDENCE.md](STATEMENT_CORRESPONDENCE.md).

## Proof route and attribution

The route combines a coarse Remez bound and empirical logarithmic potentials with a construction on the minimum-potential region. The latter uses local external-field convergence, finite Fejér/Privalov witnesses, contour sampling with corrected moments, auxiliary-mesh Gamma/sinc identities, and polynomial tilts to build alternating peaks. The retained finite interpolation and Baire-category argument then produces one continuous function for all admissible interpolating sequences.

[PROOF_GUIDE.md](PROOF_GUIDE.md) gives the complete proposed mathematical argument and declaration map, including the constants, scale/deletion order, and final quantifiers. The supplied manuscript states the integer-excess result as Theorem 1, Section 1, page 1; its original Lean archive explicitly contains only a partial formalization. The continuation replaces some analytic constructions and must be reviewed on its own evidence.

[ATTRIBUTION.md](ATTRIBUTION.md) distinguishes the upstream manuscript and partial code, later assistant-assisted mathematical and implementation work, and the submitting account's contribution. Existing notices are retained; no license is added by these documents.

## Reproduce

Use Lean `leanprover/lean4:v4.33.0` and the exact revisions in `lake-manifest.json`, including mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. From the selected source root, with dependencies installed:

```sh
python3 scripts/build_v6.py
```

For a new checkout requiring the pinned dependency cache, use `python3 scripts/build_v6.py --cache`. [REPRODUCE.md](REPRODUCE.md) gives setup, full build stages, explicit endpoint checks, actual-output fields, and the receipt requirements. A default `lake build` alone does not check the complete final target.

Formal acceptance and mathematical review are separate: a successful Lean receipt must identify the exact checked source, and mathematical review must cover the complete argument and its correspondence to the original problem.
