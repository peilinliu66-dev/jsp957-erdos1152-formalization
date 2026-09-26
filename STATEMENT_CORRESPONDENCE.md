# Statement correspondence — JSP-000957 / Erdős 1152

**Verification status: FULL_FINAL_ELABORATED_STANDARD_AXIOMS.** `The complete seven-stage Lake build and all seven checks succeeded on the selected source bytes. Both full-type regression checks and exact-name transitive axiom audits passed. All nine dependency checkouts matched the locked revisions and were clean before and after the run; all driver-hashed source files remained unchanged. This is Lean verification by the build environment, not an independent mathematical review.`

This document records the full expected statements and their mathematical correspondence. Source version: `412bf5f3bdff311fcd485459a394aadbcee8a103`; mathematical review: `NOT INDEPENDENTLY REVIEWED; submitted argument requires review`.

## Sources and identity

The award identifier is JSP-000957. The mathematical source is Erdős Problem **1152**, not Erdős Problem 957:

- https://www.erdosproblems.com/1152
- The supplied manuscript cites *Some of Paul's Favorite Problems*, Budapest, July 1999, Problem 2.42, at https://web.math.pmf.unizg.hr/~vjekovac/EP/Some_of_Pauls_favorite_problems.pdf .
- The source package points to https://zenodo.org/records/22549777 ; the fixed supplied ZIP was obtained on 2026-09-24.

The exact mathematical statement below follows the supplied source package and manuscript. The current public page text and Zenodo creator/version metadata have not been independently revalidated for this edition; the linked records identify the stated sources. Attribution and the fixed supplied-file hashes are recorded in [ATTRIBUTION.md](ATTRIBUTION.md).

## Mathematical scope in the supplied source

For every array of finite sets X_N ⊆ [-1,1], each containing N distinct nodes, and every nonnegative integer sequence r_N with r_N/N → 0, there is a continuous real function f on [-1,1] such that **every** polynomial sequence satisfying

```text
degree(p_N) ≤ N + r_N
p_N(x) = f(x) for every x in X_N
```

has limsup_N |p_N(x)| = +∞ for Lebesgue-almost every x in [-1,1].

The supplied `paper/PROOF.tex` and PDF state this as **Theorem 1**, label `thm:main`, Section 1, **page 1**. The PDF has 16 pages; page 16 explicitly calls the original Lean code partial. Its author and date fields are empty. The exact PDF file hash is in [ATTRIBUTION.md](ATTRIBUTION.md); “obtained 2026-09-24” is a package acquisition date, not an invented publication date. This identifies a claimed result; it does not certify every proof step in that manuscript or the later replacement route.

## Exact current Lean candidate

```lean
theorem Erdos1152.V5.ae_limsup_eq_top
    (X : Erdos1152.NodeArray) (r : ℕ → ℕ)
    (hr : Tendsto (fun n => (r n : ℝ)/(n+1 : ℝ)) atTop (𝓝 0)) :
    ∃ f : Erdos1152.ContinuousFunction, ∀ p : ℕ → ℝ[X],
      (∀ n, X.Interpolates r f n (p n)) →
      ∀ᵐ x ∂volume.restrict Erdos1152.Segment,
        limsup (fun n => ((|(p n).eval x| : ℝ) : EReal)) atTop = ⊤
```

This display expands namespace qualification for reading; the authoritative source is `Erdos1152/V5/Main.lean` at `412bf5f3bdff311fcd485459a394aadbcee8a103`. The theorem is defined and proved in `Erdos1152/V5/Main.lean`, imported by `JSP957Final.lean`. The proposed statement has not been approved by prize maintainers.

| Mathematical notion | Source definition / meaning |
| --- | --- |
| [-1,1] | `Segment := Set.Icc (-1 : ℝ) 1` |
| Real continuous f | `ContinuousFunction := C(Segment, ℝ)` |
| N distinct nodes | `NodeArray.node n : Fin (n+1) → Segment` and rowwise injectivity |
| Reindexing | Engineering row n corresponds to N=n+1; r(n)=r_(n+1) |
| Degree bound | `p.natDegree ≤ n+1+r n` |
| Interpolation | Equality at every node, with its subtype coordinate coerced to ℝ |
| Sublinear excess | `Tendsto (fun n => (r n : ℝ)/(n+1 : ℝ)) atTop (𝓝 0)` |
| Almost everywhere | Lebesgue measure restricted to the closed segment |
| Unbounded limsup | Absolute values embedded into EReal, limsup equals its top element |

Every positive row size is represented. There is no restriction to a special node array, subsequence of arrays, positive density, or uniform spacing in the final source signature. The degree convention includes the zero polynomial: its natural degree is zero, and the allowed bound is at least one.

The quantifier order is ∀ X ∀ r, sublinearity → ∃ f ∀ p, interpolation → a.e. divergence. The same f is chosen before all admissible polynomial sequences. The null set may depend on p. This does not claim a common exceptional set for all sequences.

Only X, r and sublinearity appear as explicit parameters of this candidate. Its proof invokes the constructed canonical minimal input and the V4 terminal. This is a source fact; absence of explicit extra parameters does not itself prove that the full chain elaborates or has an acceptable axiom set. `checks/FinalStatement.lean` and `checks/FinalAxioms.lean` must be run.

## Strict relative degree formulation

For ε_N → 0, define for N≥1

```text
r_N = max(0, ceil(N ε_N) - 1).
```

This is a nonnegative integer. If an integer degree d satisfies d < N(1+ε_N), then the integer d-N is strictly smaller than Nε_N and hence at most ceil(Nε_N)-1. Thus d ≤ N+r_N. The zero polynomial is automatically covered by the natural-degree bound. Moreover,

```text
0 ≤ r_N/N ≤ max(ε_N,0) + 1/N → 0.
```

The integer-excess theorem therefore implies the strict relative-degree formulation mathematically. This reduction is also stated in the supplied manuscript immediately after Theorem 1 and motivates the explicit bridge below.

## Explicit strict-ε endpoint and zero polynomial

**Integration and complete verification: The strict endpoint is integrated in JSP957Final.lean. Its actual complete build, independent expected-type check and transitive axiom audit all passed in the same canonical run as the integer-excess endpoint..** Acceptance of a few arithmetic helpers does not establish the complete endpoint, which depends on the actual integer-excess terminal and its entire proof chain.

The full expected statement in `Erdos1152/V5/StrictEpsilon.lean` is:

```lean
theorem Erdos1152.V5.ae_limsup_eq_top_strict_epsilon
    (X : Erdos1152.NodeArray) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0)) :
    ∃ f : Erdos1152.ContinuousFunction, ∀ p : ℕ → ℝ[X],
      (∀ n,
        WithBot.map (fun d : ℕ => (d : ℝ)) (p n).degree <
          (↑((n + 1 : ℝ) * (1 + ε (n + 1))) : WithBot ℝ) ∧
        ∀ i, (p n).eval (X.node n i : ℝ) = f (X.node n i)) →
      ∀ᵐ x ∂volume.restrict Erdos1152.Segment,
        limsup (fun n => ((|(p n).eval x| : ℝ) : EReal)) atTop = ⊤
```

As above, the displayed declaration is namespace-qualified for reading. `checks/StrictEpsilonStatement.lean` must independently instantiate this full expected type, not merely confirm that a declaration with the same name exists.

| Point requiring correspondence | Exact treatment |
| --- | --- |
| Original row size | `N = n + 1`; every positive size occurs. |
| Excess indexing | The bound uses `ε (n + 1)`, not `ε n`; `ε 0` is irrelevant. |
| Sign of ε | No nonnegativity assumption is added. |
| Degree of zero | `Polynomial.degree` has value `⊥`; `WithBot.map` retains it as the degree \(-\infty\). |
| Initial nonpositive bounds | The strict degree predicate still correctly admits zero; no rows are discarded. |
| Universal polynomial choice | One `f` is selected before `∀ p`, just as in the integer-excess theorem. |
| Exceptional set | It may depend on the chosen sequence `p`. |
| Conclusion and measure | The same EReal limsup and Lebesgue measure restricted to `Segment`. |

The formal bridge uses a convenient larger majorant instead of the minimal rounding above:

\[
 r(n)=\left\lceil(n+1)|\varepsilon(n+1)|\right\rceil_{\mathbb N},
 \qquad
 0\le\frac{r(n)}{n+1}
 \le |\varepsilon(n+1)|+\frac1{n+1}\longrightarrow0.
\]

For a nonzero polynomial, its integer degree \(d\) satisfying the strict bound obeys

\[
 d<(n+1)(1+\varepsilon(n+1))
 \le(n+1)+(n+1)|\varepsilon(n+1)|
 \le(n+1)+r(n).
\]

For the zero polynomial, natural degree zero satisfies the latter nonnegative budget directly. Apply the integer-excess theorem once with this `r`, obtaining one `f`. Every sequence satisfying the strict predicate also satisfies `NodeArray.Interpolates r f`; applying the already chosen function's universal property gives the conclusion for every such sequence. Using a larger sublinear integer budget strengthens the intermediate interpolation class and does not weaken the strict endpoint.

The true-degree encoding matters at finite initial rows. For example, `N = 1` and `ε 1 = -2` give strict bound `-1`: the degree of zero is below that bound, but its `natDegree = 0` is not. Replacing the strict predicate by a strict natural-degree inequality would therefore omit a required case. The prepared endpoint avoids that change.

## Required release checks

The integer-excess endpoint remains independently checked by `checks/FinalStatement.lean` and `checks/FinalAxioms.lean`. The strict-ε endpoint adds `checks/StrictEpsilonStatement.lean` and `checks/StrictEpsilonAxioms.lean`. Final integration into `JSP957Final.lean` and the build driver must retain both pairs and the complete original build stages.

Actual integer-excess axiom output: `'Erdos1152.V5.ae_limsup_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound]`.

Actual strict-ε axiom output: `'Erdos1152.V5.ae_limsup_eq_top_strict_epsilon' depends on axioms: [propext, Classical.choice, Quot.sound]`.

Complete release receipt: `logs/v6/20260926T121829_907367Z/BUILD_RESULT.json`; receipt SHA-256: `899475250553c5acc4991fbc46477f544b8fcadaf60d7efe725b9b53c9bbaf99`. [REPRODUCE.md](REPRODUCE.md) specifies the real commands and source/dependency checks. A statement-level correspondence argument or a helper diagnostic cannot replace these execution results.


