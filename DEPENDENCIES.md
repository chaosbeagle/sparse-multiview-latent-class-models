# Pinned dependencies

Lean **4.32.0**, compiler commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
Use Git, Python 3.9+ and Linux/macOS/WSL for the full proof build.

| Package | Git revision | Upstream |
|---|---|---|
| mathlib | `81a5d257c8e410db227a6665ed08f64fea08e997` | [mathlib](https://github.com/leanprover-community/mathlib4.git) |
| plausible | `e12c1910fe855cbfc38803cd4e55543906d5fa62` | [plausible](https://github.com/leanprover-community/plausible) |
| LeanSearchClient | `c5d5b8fe6e5158def25cd28eb94e4141ad97c843` | [LeanSearchClient](https://github.com/leanprover-community/LeanSearchClient) |
| importGraph | `7e9612bf0b9ee66db3cb5b9988a35afc706f5a12` | [importGraph](https://github.com/leanprover-community/import-graph) |
| proofwidgets | `6e311e2a844da9b2cc3971187df2fe0066947b93` | [proofwidgets](https://github.com/leanprover-community/ProofWidgets4) |
| aesop | `a7dbf0c63b694e47f425f3dcddbc0e178bb432d3` | [aesop](https://github.com/leanprover-community/aesop) |
| Qq | `38d591e778f100aec9762bb582f9c7f55f50e9dc` | [Qq](https://github.com/leanprover-community/quote4) |
| batteries | `023ce7d62a0531e22a5331e20b587817a80d49ff` | [batteries](https://github.com/leanprover-community/batteries) |
| Cli | `88679d088c9720c27ebdf2ba4dafe17341747f94` | [Cli](https://github.com/leanprover/lean4-cli) |

The authoritative lock is [dependency-pins.json](lean/dependency-pins.json). Obtain each repository at exactly the listed revision and the matching compiled artifacts for that same Lean version. Dependencies are not bundled. The build checks tracked-source cleanliness and revisions and does not download, update or modify them.
