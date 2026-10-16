# Reproduce the proofs and exact examples

The mathematical source files are unchanged. The public build wrapper replaces
machine-specific paths with explicit arguments and uses the safe private-output
overlay adaptation described by the historical verification receipt.

## Verify source and dependency identity

Install the compiler and exact [dependency revisions](DEPENDENCIES.md). Each
package directory must have a clean tracked Git tree and the matching compiled
Lean artifacts. Then, from this repository root:

```bash
python3 lean/build.py --toolchain /path/to/lean-4.32.0   --packages /path/to/pinned/packages --verify-only
```

This identity check also works on Windows when native pinned artifacts are
available. It does not compile proofs.

## Full proof build and audits (Linux/macOS/WSL)

```bash
python3 lean/build.py --toolchain /path/to/lean-4.32.0   --packages /path/to/pinned/packages --work /path/to/new-private-build
```

The work directory must not exist and must be outside this repository, the
toolchain and dependency directories. The wrapper first checks all 475 source
hashes, compiler commit and nine Git pins. It copies the source to that private
directory and invokes `lake build` through the pinned runtime wrapper. The
default target compiles the 159-module import closure, runs the complete
declaration/axiom inventories and designated computability/C dependency checks.
`lean/AxiomAudit.lean` indexes the generated per-module audit directives. The
workflow writes `full_build.log`, `REBUILD_RESULT.json` and `build_logs/final/` in
the private output; all listed checks must finish with exit zero. Shared
dependency artifacts remain read-only. The historical full workflow took about
an hour in its environment; this is not a runtime guarantee.

This is a source-only rebuild of the project using compiled external
dependencies, not a compiler or complete Mathlib rebuild. Lean's `-M 4096`
setting is not an OS-level memory guarantee. Finite-fuel and termination theorems
do not establish practical full-model certification.

## Exact manuscript examples

```bash
python3 -I examples/verify_examples.py
```

No third-party Python package is needed. Do not use `-O` or `-OO`. These checks
verify the stated rational examples and counts, not the general paper-only
volume theorem or any real-data result.

## PDF

The public repository distributes the compiled article. Its editable manuscript
sources remain in the author's local delivery package and are not required for
checking the Lean project or exact examples.
