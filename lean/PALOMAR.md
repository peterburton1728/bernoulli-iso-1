# Statement comparison and Palomar preparation

The intended registry statement is the finite-uniform measurable conjugacy in
`Challenge.lean`, not every theorem claimed by the accompanying PDF.
`Solution.lean` provides the proof. Its repeated definitions deliberately have
the same qualified names and mathematical bodies in a separate module; the
modules must not import each other. Comparator compares the selected theorem's
type and the constants its statement depends on.

The Challenge uses a theorem with a deliberate `by sorry` statement hole.
Do not replace it with an axiom: Lean 4.35 Comparator requires matching
constant kinds, and the Solution endpoint is a theorem. No proof-development
placeholder or additional axiom is permitted in the Solution closure. The
only permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

## Recorded local status (27 October 2026 revision)

The source build and axiom audits pass. The original monolithic prime
certificate reproduces the NanoDa stack overflow locally. Its replacement uses
340 opaque Lucas–Lehmer checkpoints, each with at most 64 iterations verified by
reflexivity. The same stock NanoDa 0.4.19 accepts the revised complete solution.
Local Comparator also passes statement comparison, axiom checks, and the Lean
standalone kernel check. The optional con-ron replay was stopped locally and
is inconclusive; this is not a hosted capacity-decline verdict.
The statement and concrete witnesses are unchanged.

Local checks use the official macOS arm64 toolchain and do not execute the
Linux sandbox, hosted resource controls, license/provenance service, or registry
intake. Logs and outcomes are in `verification/`; the old reports are clearly
separated under `verification/previous-submission-2026-10-25/`. A fresh hosted
full preflight is required for the exact commit ultimately submitted.

## Local checks

Run these commands from the `lean/` directory.

```sh
python3 check_package.py .
lake update
lake exe cache get
lake build Solution
lake build Audit
lake comparator --config comparator.json
```

The package scanner checks source formatting and obvious placeholders;
it does not parse Lean or inspect proof terms. The axiom audit and Comparator
are necessary complementary checks. Keep complete logs, exact source hashes,
toolchain/dependency pins and outcomes for every claim made about verification.
A source-only review is not an executed build; a build is not Comparator; a
local Comparator run is not the complete registry workflow. Sandbox commands
may require Linux tooling and privileges unavailable on macOS. Do not relabel
an unsandboxed local diagnostic as a protected mechanical check.

## Full Linux mechanical preflight

Use Palomar's reusable workflow at the exact pinned pipeline revision below,
with the actual public GitHub repository and immutable release commit. No
repository identity has been fabricated in these instructions.

```yaml
jobs:
  palomar-preflight:
    uses: PalomarRegistry/PalomarSubmission/.github/workflows/submission.yml@c02bbeaed888df45c4e28c4e99dba540ad21552a
    with:
      repository: ${{ github.repository }}
      commit: ${{ github.sha }}
      pipeline_commit: c02bbeaed888df45c4e28c4e99dba540ad21552a
      request_id: preflight002
      mode: full
      execution_profile: palomar-standard-v1
      options: '{"project_path":"lean","comparator_config_path":"lean/comparator.json","formalization_metadata_path":"lean/formalization.yaml","authorization_relationship":"I am a responsible author or maintainer"}'
```

The relationship declaration is a permanent claim about the human submitter;
use it only when truthful and authorized. Both pipeline SHA fields must match.
Paths are repository-relative. This repository uses `project_path: lean`,
`comparator_config_path: lean/comparator.json`, and
`formalization_metadata_path: lean/formalization.yaml`. The executable workflow
is at repository-root `.github/workflows/palomar-preflight.yml`. This workflow must run on the exact
commit intended for submission and return a passing full mechanical report.
Source changes require checking the new commit.

The pinned verifier accepts Lean releases at least v4.35.0-rc2. This project
uses v4.35.0 and its bundled `lake comparator`, exporter, Lean kernel and NanoDa.
The pipeline selects its own protected configuration, sandbox and checker
revisions; user configuration cannot weaken these. For this toolchain the pinned
pipeline selects con-ron from Lean v4.36.0-rc1 and attempts replay after the
mandatory Lean/NanoDa checks. Record the actual reports and binary digests;
do not infer successful kernel checks from the configuration alone.

Palomar's CONTRIBUTING prose and some older Comparator instructions describe an
older standalone tool arrangement. The exact pipeline implementation and report
must be retained when documenting which checks actually ran. A full preflight
is predictive mechanical evidence, not editorial review or registration.

## Before public submission

Ensure every committed Lean source uses the module system and is at most
10,000 physical lines, including unused sources and contained packages. Challenge
has the tighter 1,000-line/100-KiB cap. Commit only the final source and metadata,
not compiled proof artifacts outside `.lake`; the service discards supplied
`.lake` state. Keep the checkout at most 500 MiB, avoid submodules/LFS pointers,
and retain canonical pinned Git dependencies, the root SPDX license and upstream
provenance. `formalization.yaml` must accurately describe scope, sources,
human authorship, AI contributions and the review actually completed.

Read the current official [policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
and [submission-service contract](https://submit.palomar-registry.org/llms.txt)
before intake. Agent-driven submission requires prior agreement on the actual
repository, exact source commit, Comparator path and relationship claim. Agents
must not perform browser sign-in for the user. Registration is a separate
publication decision tied to the exact review digest, and creates durable public
records. These instructions perform neither submission nor registration.

## Repository layout for GitHub Desktop

The top-level mathematical deliverables are `lean/` and `bernoulli-iso.pdf`.
The canonical Apache-2.0 `LICENSE` is also at repository root, as Palomar
requires even for a nested Lean project. The existing license copy inside
`lean/` is retained for source-package tooling. The hidden `.github/` directory
contains the manual full mechanical preflight workflow.

On the Palomar form, select project path `lean`, Comparator path
`lean/comparator.json`, and metadata path `lean/formalization.yaml`. Submit the
exact public commit that completed the full hosted preflight.
