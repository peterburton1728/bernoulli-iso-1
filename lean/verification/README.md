# Verification of the 27 October revision

The complete package builds with Lean 4.35.0. Comparator reports `Your solution
is okay!`: statement comparison passes, the final proof uses only the permitted
standard axioms, and the full export is accepted by Lean and stock NanoDa 0.4.19.
NanoDa used four workers and its unmodified default 16 MiB worker stack.

See `revised-build.log`, `revised-comparator.log`, and
`local-verification-2026-10-27.json` for results, hashes, and checker identity.
The optional con-ron replay uses the 4.36.0-rc1 release and the pipeline's
`--jobs=2 --verified` flags. It was voluntarily interrupted locally after an
extended run, with exit 130: its result is stopped/inconclusive. This is not a
Palomar capacity decline or evidence of con-ron acceptance/rejection. Its log
and exact command are retained. Palomar's pinned hosted pipeline allows its own
recognized capacity/support declines after the mandatory kernels pass.

The original prime certificate reproduces a NanoDa stack overflow. The revised
certificate passes independently and as part of the complete exported proof.
The generator reproduces the certificate byte for byte. Its decimal data are
all checked by the kernels; Python supplies no trusted facts.

These checks ran on macOS arm64 without a Linux sandbox. They establish local
mathematical/checker acceptance, not a protected hosted mechanical report or
registry acceptance. The exact revised source commit still needs a full
Palomar hosted preflight before submission. Reports under
`previous-submission-2026-10-25/` describe the old source only.

## Reproduce on a normal Lean installation

From the project root with the pinned toolchain and dependencies:

```sh
lake exe cache get
lake build Solution Audit Challenge
python3 check_package.py .
lake comparator --config comparator.json
```

The last command requires Linux bubblewrap. For a trusted local diagnostic on
macOS, the command actually executed here is:

```sh
lake comparator --config comparator.json --inadvisably-no-sandbox
```

For the protected hosted workflow and exact-source-commit requirement, see
`../PALOMAR.md`. No checker stack settings, permitted axioms, or compared
statements have been weakened.
