# A countable group all of whose nontrivial Bernoulli shifts are isomorphic

**Theorem** (`AllCollapse.all_bernoulli_shifts_isomorphic` in `Challenge.lean`). There is a
countable group G with the following property. Let L and L′ be standard Borel spaces with
probability measures λ and λ′, neither of which is a point mass. Then the Bernoulli shifts
of G on (L^G, λ^G) and (L′^G, λ′^G) are isomorphic: there are shift-invariant measurable sets
of full measure and a bijection between them which commutes with the shift, preserves the
measures, and is measurable in both directions.

No condition is put on the entropies of the bases, which may differ and may be infinite.
`Challenge.lean` has 55 lines and imports only Mathlib. `Solution.lean` repeats the statement
and proves it from the library `Collapse/` (28 files). The group is G = N × (ℤ/2 ≀ ℤ), where N
is the group of OpenAI's characteristic-two construction (pinned at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`).

## Context

- Over ℤ, and over every countably infinite amenable group, two Bernoulli shifts are
  isomorphic exactly when their bases have the same Shannon entropy (Kolmogorov and Sinai;
  Ornstein, 1970; Ornstein and Weiss, 1987).
- Over every sofic group, Bernoulli shifts whose bases have different entropy are not
  isomorphic (L. Bowen, 2010; Kerr and Li, 2011, for bases of infinite entropy).
- Over every countably infinite group, Bernoulli shifts whose bases have the same entropy
  are isomorphic (Ornstein; Stepin; L. Bowen, 2012; Seward, 2022).
- So the theorem can hold only for a group which is not sofic, and it shows that base entropy
  is not an isomorphism invariant of Bernoulli shifts over every countable group. The group N
  comes from a counterexample to Kaplansky's direct-finiteness conjecture; by a theorem of Elek
  and Szabó (2004) the group of such a counterexample is not sofic.
- Earlier public work of the author in this repository: the draft `../bernoulli-iso.pdf`
  (27 October 2026) states an all-base theorem with finitary conjugacies, and the registered
  entry PALOMAR-2026-10-27-000030 (`../lean/`) certifies the case of two finite uniform bases
  A and A × A. The present development certifies the measurable isomorphism for all bases.

This account was drafted with AI assistance; the references are given from memory by author
and year and were not re-read for it. An AI-assisted, non-exhaustive literature search on
10 November 2026 found no other proof of such a statement. Beyond that search, novelty is
unknown.

## Outline of the proof

1. *Algebraic input.* A finite field K, a countable group N, finite subgroups of a common
   order κ with their averages p_v (v ∈ V), and matrices U, T over K[N] with U·diag(p) = U,
   diag(p)·T = T, U·T = 1 of size m, and |V| < κm. This is supplied by the pinned OpenAI
   proofs and is restricted to the prime field 𝔽₂ (`Collapse/RestrictScalars.lean`).
2. *Local kernels.* For a free Borel action, matrices over the orbit relation with finite rows
   and columns form a calculus without any measure; the isomorphism classes of the associated
   local spaces form a monoid with countable sums (`Kernel`, `LocalSpace`, `SigmaMonoid`).
3. *Collapse.* Marker sets D_k of a tower of finite subgroups satisfy three relations in that
   monoid; the third comes from the transform defined by U and T. An absorption lemma then
   gives a · D_n ≅ ∞ · X₀ for every a ≥ 1, where X₀ is the invariant set of full measure on
   which the markers live (`Markers`, `Relations`, `Transform`, `Collapse`).
4. *Dictionary.* Sets with isomorphic local spaces have isomorphic bundles, which are
   measure-preserving extensions of the system (`Bundle`, `Dictionary`, `Hopf`,
   `RelativeCollapse`).
5. *Pairing.* For an element f of order 2, the sites γ and γf are paired. This passes from
   one base to all bases without the Ornstein–Weiss isomorphism theorem (`Pairing*`, `Main`).

The module docstrings give the precise statements.

## Scope and limits

- Measurable isomorphism only. Finitary or continuous conjugacy is not formalized.
- One group. Nothing is claimed about other groups, and entropy does not occur in the Lean
  statement.
- The algebraic input (`UpstreamFoundation`, `UpstreamConstruction`, `CertifiedInput`,
  `BernoulliIso/CheckpointPrimeCertificate`) and the ten other files of `BernoulliIso/` are
  reused byte for byte from `../lean/`. They are machine-checked here again.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`. The Challenge theorem ends in a
  deliberate `by sorry`; there is no other `sorry`.

## Authorship and review

Peter Burton is the responsible human author and maintainer. He chose the target, approved
the wording of the compared statement, and directed the work. The definitions, statements
and proofs of `Collapse/` were written by AI systems, and no human has reviewed the proofs;
see `formalization.yaml`. Upstream sources: `provenance/` and `NOTICE`. Licence: Apache-2.0.

## Reproduce

```sh
cd all-collapse
lake exe cache get
lake build Solution Challenge
python3 check_package.py .
lake comparator --config comparator.json
```

Lean 4.35.0 (`lean-toolchain`), Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. Do not run
`lake update`. The last command needs Linux `bwrap`. `PALOMAR.md` says what has been checked.
