# Search043 paper

[Paper source](paper.md) · [PDF](build/paper.pdf)

This paper describes the search043 certified result, the level-four search campaign
that produced it, adaptive model-width comparisons and the explicit CN/combination-loss
trust boundary.

Build from this directory with `bash build.sh`, or from the repository root:

```sh
bash certifications/l4-2026-10-04-search043/paper/build.sh
```

The build uses the shared bibliography and LaTeX infrastructure in root
`papers/`. Figures and their aggregate data are local to this paper; `data/manifest.json`
binds their identities. They are descriptive search observations, not additional
premises of the certificate theorem. The parent directory contains the exact
certificate's assurance, source and verification instructions.
