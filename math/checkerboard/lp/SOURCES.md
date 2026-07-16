# Upstream certificate sources

The published odd-fat continuum dual certificate is arXiv:2605.09215v1.

Official ancillary files:

- [README](https://arxiv.org/src/2605.09215v1/anc/odd_fat_certificate/README.md)
- [Constants](https://arxiv.org/src/2605.09215v1/anc/odd_fat_certificate/constants.tsv)
- [Sign checks](https://arxiv.org/src/2605.09215v1/anc/odd_fat_certificate/sign_checks.tsv)
- [Triangles](https://arxiv.org/src/2605.09215v1/anc/odd_fat_certificate/triangles.tsv)
- [Bernstein coefficients](https://arxiv.org/src/2605.09215v1/anc/odd_fat_certificate/bernstein_coefficients.tsv)
- [Independent verifier](https://arxiv.org/src/2605.09215v1/anc/odd_fat_certificate/verify_odd_fat_certificate.py)

The repository formalization translates these exact records into Lean data and
checks them in the kernel. The Python verifier is retained only as an independent
cross-check; it is not part of the trusted proof base.
