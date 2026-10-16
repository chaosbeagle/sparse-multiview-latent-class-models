# Verification evidence and scope

The dated receipt records the completed **2026-10-09** source compilation and
axiom audit. The 475 Lean input files in this repository are byte-identical to
that receipt's inventory. This publication performs source-identity, dependency,
package and PDF checks; it does not claim a new independent semantic review or
fresh full Lean/kernel rebuild.

The original module and declaration names are deliberately preserved so the PDF,
coverage map and source hashes refer to the same objects. Historical identifiers
inside the code are source API names, not additional published projects.

The recorded run covers 159 source modules, 8,174 distinct declarations and 37
designated computable roots. Only `propext`, `Classical.choice` and `Quot.sound`
were observed. Third-party compiled dependency artifacts were reused. Neither
the entire compiler/runtime nor every argument in the article is verified by
that receipt. See [formal scope](../docs/formal-coverage.md).
