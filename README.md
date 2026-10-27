# Finite uniform Bernoulli shifts with unequal base entropy

There exist a countable group G and a nontrivial finite alphabet A such that the ordinary left Bernoulli shifts on A and A×A, equipped with uniform product probability measures, are measurably conjugate. The conjugacy is equivariant, preserves probability, and has a measurable inverse on invariant conull measurable subsets. The two uniform bases have different cardinalities and hence different base Shannon entropies.

## Proof and exposition

- [Expository note](bernoulli-iso.pdf)
- [Lean development and build instructions](lean/)
- [Palomar-registered release v1.0.0](https://github.com/peterburton1728/bernoulli-iso-1/releases/tag/v1.0.0)

## Palomar registration

Registered on 27 October 2026 as [PALOMAR-2026-10-27-000030, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-27-000030&version=1).

The exact registered source commit is:

`80241ef9354deaa4e787431f5e0692d8d757308e`

Palomar's mechanical verification passed, including Lean kernel checking and independent NanoDa replay. Its automated editorial review identified no blocking problems. This is automated verification and review, not human peer review.

The registered snapshot and release remain fixed at that commit. Later documentation updates on the main branch are not part of that verified snapshot. Verification-status notes within the snapshot were written before the hosted checks completed and should be read in that historical context.

## Scope

The formal certificate concerns finite-uniform measurable conjugacy. Broader all-base, finitary, finitely presented, and graph formulations discussed in the expository note are outside its scope. The certificate does not formalize a general entropy classification theorem.

## Provenance

The algebraic existence input is due to OpenAI's characteristic-two construction. This development constructs the dynamical conjugacy from the checked algebraic input.

Peter Burton is the responsible human author and maintainer. AI contributions, source references, and upstream attribution are disclosed in [formalization.yaml](lean/formalization.yaml) and the [provenance materials](lean/provenance/).

The Lean code and build materials are licensed under [Apache-2.0](LICENSE); retain the accompanying upstream notices.
