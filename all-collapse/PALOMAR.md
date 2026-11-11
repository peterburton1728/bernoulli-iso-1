# Verification status and Palomar preparation

Compared statement: `AllCollapse.all_bernoulli_shifts_isomorphic`, modules `Challenge` and
`Solution`, configuration `all-collapse/comparator.json`, project path `all-collapse`. The
Challenge theorem ends in a deliberate `by sorry`; there is no other `sorry` and no axiom
beyond `propext`, `Classical.choice`, `Quot.sound`.

## Checks made before submission (macOS arm64, 11 November 2026)

Recorded in `verification/`. They were run in this folder of a fresh clone:

- `lake exe cache get`, then `lake build Solution Challenge` from scratch;
- `python3 check_package.py .`;
- axiom audit of the compared theorem;
- export with `leanexport`, accepted by stock NanoDa 0.4.19 (four threads, default 16 MiB
  worker stack, unpermitted axioms as a hard error).

Comparator was not run on this layout. `lake comparator --config comparator.json
--inadvisably-no-sandbox` (statement comparison, NanoDa, Lean kernel) passed earlier the same
day on the same Lean sources laid out at a repository root; since then `Challenge.lean`,
`Solution.lean` and `comparator.json` are byte-identical and only comments changed in
`Collapse/`. It is an unsandboxed diagnostic and needs `nanoda_bin`, from the toolchain's `bin`
directory, on the PATH.

These are local checks, not Palomar's hosted verification, and they cannot report it: this
file is part of the commit that Palomar verifies.

## Hosted preflight

`.github/workflows/palomar-preflight-all-collapse.yml`, at the repository root, calls
Palomar's reusable workflow at pipeline commit `14aa8d6b3c2f14a8540605e37144560b9a00e7e7` with
`mode: full`. It is started by hand on the exact public commit to be submitted. Submission
and registration are separate acts of the human author.

The older workflow `palomar-preflight.yml` belongs to the registered entry in `lean/` and is
left as it was.
