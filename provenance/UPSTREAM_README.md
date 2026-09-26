# Erdős Problem #1152: almost everywhere divergence with sublinear excess degree

Lean 4 formalization for [Erdős Problem #1152](https://www.erdosproblems.com/1152),
in the stronger form of almost everywhere unboundedness.
[`Erdos1152.ae_limsup_eq_top_of_cardinalGrowth_minimal`](Erdos1152/Main.lean) proves the
conclusion from Remez's inequality, sublinear excess degree, and two analytic inputs that
remain hypotheses: cardinal-polynomial growth and the minimum-potential argument.
The [manuscript](paper/PROOF.pdf) contains the full argument.

## Build and check

With [Elan](https://github.com/leanprover/elan) installed, run from the repository root:

```sh
lake exe cache get
lake build
lake test
LEAN_NUM_THREADS=2 lake env leanchecker -v Erdos1152
```

## Proof correspondence

| Manuscript | Lean source |
|---|---|
| Lemma 3, the sign-change bound for polynomial corrections | [Intervals.lean](Erdos1152/Intervals.lean), `alternating_interval_bound` |
| Lemma 4, equilibrium density and the scalar integral | [EquilibriumDensity.lean](Erdos1152/EquilibriumDensity.lean), [CauchyIntegral.lean](Erdos1152/CauchyIntegral.lean) |
| Section 6.1, factorization and Remez amplification from a cardinal-polynomial growth estimate | [RemezAmplification.lean](Erdos1152/RemezAmplification.lean), `cardinal_factorization`, `eventually_cardinal_amplification_of_measure_convergence` |
| Section 6.1, density points and local interval data | [CardinalLocal.lean](Erdos1152/CardinalLocal.lean), `localAmplificationAbove_of_cardinalGrowthCover` |
| Combining the above-minimum and minimum-potential regions | [LocalRegions.lean](Erdos1152/LocalRegions.lean), `localAmplification_of_above_minimal` |
| Proposition 11, the finite construction | [Main.lean](Erdos1152/Main.lean), `finiteAmplification_of_localAmplification` |
| Section 8, Baire and the almost-everywhere conclusion | [Main.lean](Erdos1152/Main.lean), `ae_limsup_eq_top_of_localAmplification` |

[Statement.lean](checks/Statement.lean) expands the conditional statement and its three inputs.

## Use of generative AI

The author used GPT-5.6 and GPT-6 Astra in developing the arguments involving
polynomial corrections, local external fields, weighted kernels and finite
interpolation, and OpenAI Codex (GPT-6) for the Baire category argument and the Lean
formalization. The author checked the arguments and their use of the cited results
and is responsible for the content.
