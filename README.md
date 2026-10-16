# Identification, semantic coarsening, and certified inversion in sparse multi-view latent class models

**English** · [繁體中文](README.zh-TW.md)

- **Read:** [Article PDF](paper/sparse-multiview-latent-class-models.pdf)
- **Explore:** [Lean proofs](lean/) · [Formal coverage](docs/formal-coverage.md)
- **Reproduce:** [Build instructions](BUILD.md) · [Pinned dependencies](DEPENDENCIES.md) · [Exact examples](examples/)

## Overview

This project develops a mathematical theory of identification and certified
inversion for finite latent class models observed through sparse, overlapping
views. It connects the structure of the observation design to the recovery of
latent components, their scientific interpretation, and quantitative statistical
guarantees.

The starting point is a collection of joint distributions for overlapping triples
of groups. Shared kernels and componentwise mixture weights connect these local
views. The theory describes every parameter configuration compatible with the
observations, then determines how additional semantic information identifies a
fixed binary coarsening of the latent states.

## Main results

- **Global identification from local views.** A complete observational-fiber
  description expresses the remaining ambiguity through compatible edge
  permutations and weight-sensitive overlap stabilizers. Kruskal's rank condition
  on the observed triples gives a componentwise permutation-orbit characterization.
- **Exact semantic identification.** A surviving-permutation criterion determines
  when a fixed binary interpretation is identified. For the diagonal family at a
  fixed state count, finite enumeration gives sharp, attained sensitivity,
  specificity and prevalence images.
- **Certified quantitative inversion.** Explicit derivative and curvature bounds
  yield local inverse estimates. On admitted conditioned inputs, an exact
  rational interval-cover algorithm eventually returns an independently
  checkable positive separation certificate, which supplies global inverse
  bounds.
- **Statistical guarantees.** Valid separation bounds lead to finite-sample
  subclass parameter error bounds. The analysis also provides gold-direction
  certification and
  confidence sets under bounded conditional-dependence error.
- **Computational limits.** A leaf-count lower bound for the explicit product-box
  certificate format and exact rational examples quantify certificate size and
  the conservatism of the stated sufficient sample prescription.

## Formalization and reproducibility

The Lean development covers the core identification, semantic, conditioning,
statistical and certificate-correctness results. The geometric certificate-size
bound and selected worked examples are supported by conventional proofs and
exact arithmetic. The [formal coverage map](docs/formal-coverage.md) gives the
correspondence between the article and individual declarations.

The repository includes the article, **475 Lean input files**, audit sources,
dependency pins and build tools. Lean **4.32.0** and nine dependency revisions are
fixed. The [2026-10-09 verification receipt](verification/VERIFICATION_RECEIPT.json)
records a full workflow covering **159 source modules**; the published Lean
inputs retain those source hashes. [Verification details](verification/README.md)
and [build instructions](BUILD.md) describe the checks and how to reproduce them.

Run the independent exact examples with:

```bash
python3 -I examples/verify_examples.py
```

## Dedication and assistance

*Dedicated to those who fight harder when everything is turning against them.*

The article records assistance from OpenAI Astra in dots, GPT-6 Astra Pro and
Claude Opus 5.5 max, with their roles described in its assistance disclosure.

[Third-party notices](THIRD_PARTY_NOTICES.md)
