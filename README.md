# Isomorphism of Bernoulli shifts over a countable group: Lean certificates

This repository holds two Lean 4 developments and an expository note.

## 1. All nontrivial Bernoulli shifts are isomorphic

Folder [all-collapse/](all-collapse/). There is a countable group G such that the Bernoulli shifts of G over any two standard probability spaces, neither of which is a point mass, are isomorphic: there is an equivariant, measure-preserving bijection, measurable in both directions, between shift-invariant measurable sets of full measure. The bases may have different entropy, finite or infinite.

The statement, its context, an outline of the proof and its limits are in [all-collapse/README.md](all-collapse/README.md). Registered on 12 November 2026 (UTC) as [PALOMAR-2026-11-12-000001, version 1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-12-000001&version=1). The exact registered source commit is `a8df55ed454edfc197296f98155d67a49f3e5eed`, released as [v2.0.0](https://github.com/peterburton1728/bernoulli-iso-1/releases/tag/v2.0.0). Palomar's mechanical verification passed, including Lean kernel checking and independent NanoDa replay, and its automated editorial review identified no problems. This is automated verification and review, not human peer review. Later updates on the main branch are not part of that verified snapshot.

As of 11 November 2026 a human-facing version of these results is actively being prepared as part of the upcoming article "Lossless undersampling by the coprime Radon transform: nonsoficity and paradoxical ergodic theory" by Peter Burton with AI assistance.

## 2. Finite uniform Bernoulli shifts with unequal base entropy

Folder [lean/](lean/). There exist a countable group G and a nontrivial finite alphabet A such that the ordinary left Bernoulli shifts on A and A×A, equipped with uniform product probability measures, are measurably conjugate. The conjugacy is equivariant, preserves probability, and has a measurable inverse on invariant conull measurable subsets. The two uniform bases have different cardinalities and hence different base Shannon entropies.

- [Lean development and build instructions](lean/)
- [Palomar-registered release v1.0.0](https://github.com/peterburton1728/bernoulli-iso-1/releases/tag/v1.0.0)

Registered on 27 October 2026 as [PALOMAR-2026-10-27-000030, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-27-000030&version=1).

The exact registered source commit is:

`80241ef9354deaa4e787431f5e0692d8d757308e`

Palomar's mechanical verification passed, including Lean kernel checking and independent NanoDa replay. Its automated editorial review identified no blocking problems. This is automated verification and review, not human peer review.

The registered snapshot and release remain fixed at that commit. Later updates on the main branch, including the folder `all-collapse/`, are not part of that verified snapshot. Verification-status notes within the snapshot were written before the hosted checks completed and should be read in that historical context.

## Expository note

[bernoulli-iso.pdf](bernoulli-iso.pdf), unchanged since release v1.0.0. It discusses the finite-uniform statement of development 2 and broader all-base, finitary, finitely presented, and graph formulations. Development 1 certifies the measurable isomorphism for all bases, by a different proof. The finitary, finitely presented, and graph formulations are not formalized, and neither development formalizes a general entropy classification theorem.

## Provenance

The algebraic existence input is due to OpenAI's characteristic-two construction. Both developments construct the dynamical isomorphisms from the checked algebraic input.

Peter Burton is the responsible human author and maintainer. AI contributions, source references, and upstream attribution are disclosed in each development's `formalization.yaml` ([all-collapse](all-collapse/formalization.yaml), [lean](lean/formalization.yaml)) and provenance materials ([all-collapse](all-collapse/provenance/), [lean](lean/provenance/)).

The Lean code and build materials are licensed under [Apache-2.0](LICENSE); retain the accompanying upstream notices.
