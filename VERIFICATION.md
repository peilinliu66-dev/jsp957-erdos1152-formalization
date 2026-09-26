# Verification record

The complete seven-stage Lake build and all seven checks succeeded on the selected source bytes. Both full-type regression checks and exact-name transitive axiom audits passed. All nine dependency checkouts matched the locked revisions and were clean before and after the run; all driver-hashed source files remained unchanged. This is Lean verification by the build environment, not an independent mathematical review.

Selected proof-source commit: `412bf5f3bdff311fcd485459a394aadbcee8a103`. The later documentation/evidence commit preserves every one of the 145 driver-hashed source inputs byte-for-byte.

Completed UTC: `2026-09-26T12:24:35.638381+00:00`.

Actual receipt: [logs/v6/20260926T121829_907367Z/BUILD_RESULT.json](logs/v6/20260926T121829_907367Z/BUILD_RESULT.json); SHA-256 `899475250553c5acc4991fbc46477f544b8fcadaf60d7efe725b9b53c9bbaf99`.

## Actual endpoint axioms

```text
'Erdos1152.V5.ae_limsup_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1152.V5.ae_limsup_eq_top_strict_epsilon' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Reproduction and trust

The project was rebuilt in a fresh project build directory using the exact official Lean 4.33.0 source-built runtime and the nine clean pinned dependency trees. The dependency sources had already completed their genuine build; no project diagnostic olean files were copied into this final build directory.

The host required a scoped executable-path readlink adapter and compiler process scheduling. These change host path resolution and resource scheduling, not Lean source or proof checking. Their precise scope and hashes are recorded in [provenance/VERIFIED_SOURCE.json](provenance/VERIFIED_SOURCE.json). Ordinary installations can use the release toolchain with the commands in [REPRODUCE.md](REPRODUCE.md).

The result relies on this Lean implementation, the native compiler/runtime and imported dependencies. No second independent kernel checker or external mathematical reviewer is claimed. Authorship, priority and prize acceptance remain outside this build result.
