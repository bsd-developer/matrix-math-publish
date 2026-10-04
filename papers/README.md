# Papers

| Paper | Source | PDF | Result |
|---|---|---|---|
| Improving the matrix multiplication exponent with a MacBook and a proof assistant | [Markdown](../certifications/l4-2026-10-04-search043/paper/paper.md) | [PDF](../certifications/l4-2026-10-04-search043/paper/build/paper.pdf) | [search043](../certifications/l4-2026-10-04-search043/README.md) |
| A Machine-Checked Level-Four Bound on the Matrix Multiplication Exponent: A Tie-Manifold Search Case Study | [Markdown](../certifications/l4-2026-10-01-best015/paper/search-methods.md) | [PDF](../certifications/l4-2026-10-01-best015/paper/build/search-methods.pdf) | [best015](../certifications/l4-2026-10-01-best015/README.md) |
| Best015 search supplement | [Markdown](../certifications/l4-2026-10-01-best015/paper/search-methods-supplement.md) | [PDF](../certifications/l4-2026-10-01-best015/paper/build/search-methods-supplement.pdf) | best015 |
| Improving a Matrix Multiplication Bound with a MacBook and a Proof Assistant | [Markdown](certificate-verification/main.md) | [PDF](certificate-verification/build/main.pdf) | Historical level-three certificate in `artifacts/` |
| What the Equations Are Saying: A Notation Companion to Proof-Guided Branch-Aware Search | [Markdown](notation-companion/notation-companion.md) | [PDF](notation-companion/build/notation-companion.pdf) | Expository companion |

Build search043 with:

```sh
bash certifications/l4-2026-10-04-search043/paper/build.sh
```

Each paper keeps its source, figures, aggregate data and PDF together. All use
`papers/build.sh`, `papers/shared/preamble.tex` and the shared bibliography.
Historical papers retain their original claims and trust disclosures; the
latest result and its independent verification instructions are in search043.
