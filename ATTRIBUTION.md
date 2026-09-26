# Attribution and source lineage

This record separates the supplied mathematical manuscript and partial formalization from later mathematical and Lean contributions. It does not claim independent verification, author identity, priority, upstream endorsement, or prize acceptance.

## Supplied manuscript and partial formalization

The supplied manuscript is *Almost everywhere divergence of polynomial interpolation with sublinear excess degree*, 16 pages. Its target is Theorem 1, Section 1, page 1; the strict relative-degree reduction follows on the same page. The supplied PDF and TeX have empty author/date fields. The files are associated with [Zenodo record 22549777](https://zenodo.org/records/22549777) and [DOI 10.5281/zenodo.22549777](https://doi.org/10.5281/zenodo.22549777) by the source record used for this project.

The fixed supplied archive was obtained on 2026-09-24; this is an acquisition date, not a claimed publication date. Its size is 214,659 bytes and its SHA-256 is `f4dd82480c10ad5bfc6c5f2eca9ab7de34ff50f83a750956fde6d6dec6e96285`. It contains 35 files, including 29 Lean files. The supplied PDF SHA-256 is `40813b67088192fad7eea72555c5cf7f4aa944f7c4d6faf5920ef22a3e4201ed`.

[PR1035](https://github.com/TheJustinSunPrize/awards/pull/1035) historically attributes an earlier v7 manuscript to **Qiyuan Gu**, with a September 6, 2026 version date. The supplied files do not themselves establish that identity, and a later recorded metadata observation names **Anonymous**. Current authoritative creator/version/license metadata has not been reconciled for this release. These records must not be collapsed into a verified named authorship or an assertion that the differently dated versions are identical.

A citation that matches the evidence is:

> Author not stated in the supplied file. *Almost everywhere divergence of polynomial interpolation with sublinear excess degree*. Supplied manuscript associated with Zenodo record 22549777, obtained 2026-09-24; Theorem 1, Section 1, p. 1. Earlier public attribution to Qiyuan Gu is recorded in PR1035; identity/version reconciliation remains pending.

The upstream manuscript presents a full mathematical argument, but page 16 and the [retained upstream README](provenance/UPSTREAM_README.md) explicitly describe the original Lean code as partial. The original endpoint `Erdos1152.ae_limsup_eq_top_of_cardinalGrowth_minimal` retains Remez's inequality, cardinal growth and the minimum-region amplification input as hypotheses. Credit the upstream source for the manuscript and the retained finite interpolation, root counting, compatible finite-data construction and Baire-category machinery. Later import or compatibility changes do not transfer authorship of that work.

The manuscript's references credit Erdős–Vértesi for earlier Lagrange divergence and cite Olevskii–Ulanovskii and KSSV for analytic ingredients. The continuation's finite Bernstein construction specifically identifies the Fejér/Privalov route of Olevskii–Ulanovskii, OWP2013-16. Those mathematical source credits remain distinct from authorship of the new implementation.

## Later contribution

The continuation develops a coarse Remez route, empirical weak-limit and logarithmic-potential analysis, minimum-region local-field estimates, finite Bernstein witnesses, contour sampling, Gamma/sinc identities, polynomial tilts and weighted peak assembly. It reuses the upstream finite/category arguments while replacing the original weighted-kernel implementation route. [PROOF_GUIDE.md](PROOF_GUIDE.md) describes this replacement argument in full; it should not be attributed to the upstream author without evidence.

Further work includes Lean API and proof-script repairs, explicit import maintenance, movement of three pure-definition blocks into separate modules without changing their names or expressions, reproducible build/audit tooling, and the explicit strict-ε statement bridge. The successful release build refers to the selected proof-source commit and does not by itself identify a mathematical discoverer.

The submitting contribution account is [peilinliu66-dev](https://github.com/peilinliu66-dev). Public contribution evidence must identify that account's actual added work rather than claim ownership of retained upstream files:

| Contribution evidence | Reference |
| --- | --- |
| Public source repository | `https://github.com/peilinliu66-dev/jsp957-erdos1152-formalization` |
| Selected full source commit | `5f77404a2c8869efa1797a93862d5da170925977` |
| Attributable contribution history | `https://github.com/peilinliu66-dev/jsp957-erdos1152-formalization/commit/5f77404a2c8869efa1797a93862d5da170925977` |
| Final file-level upstream/continuation comparison | `provenance/SOURCE_LINEAGE.json` |

## AI assistance and review

The upstream README discloses GPT-5.6, GPT-6 Astra and OpenAI Codex assistance, and assigns responsibility to its unnamed author. Later research, implementation repairs and preparation also used ChatGPT Pro and Codex/ChatGPT Work. These model names do not identify a human author or an independent verifier. Neither assistance nor source compilation is a substitute for a complete mathematical review.

- Complete Lean verification: `FULL_FINAL_ELABORATED_STANDARD_AXIOMS`.
- Mathematical review: `NOT INDEPENDENTLY REVIEWED; submitted argument requires review`.
- Independent verifier: none claimed.

## Notices and license

The supplied archive has no standalone `LICENSE` file. Existing source and manuscript notices are retained. These documents add no license, relicense no upstream material, and make no unsupported claim about the current Zenodo license. Any applicable upstream rights or permissions must be supported by their actual notices or authoritative evidence before publication.

The local Git commits use `Codex <codex@openai.com>` to identify the automated assistant that wrote this checkout. This is not a claim that Codex is the human applicant or the upstream mathematical author. The submitting account must identify its own contribution and responsibility when publishing.
