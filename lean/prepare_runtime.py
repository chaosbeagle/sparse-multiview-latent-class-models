"""Link pinned runtime artifacts read-only into this output's module namespace.
Missing modules are compiled locally. Never follow a destination symlink for output.
"""
from pathlib import Path
import os
RUNTIME=Path(os.environ['LEAN_PACKAGES'])/'mathlib/.lake/build/lib/lean/Mathlib'
DEST=Path(__file__).resolve().parent/'.lake/build/lib/lean/Mathlib'
for source in RUNTIME.rglob('*'):
    if source.is_file():
        relative = source.relative_to(RUNTIME)
        own_source = Path(__file__).resolve().parent/'Mathlib'/relative.with_name(relative.name.split('.')[0] + '.lean')
        if own_source.is_file():
            continue  # compile supplied Mathlib sources into regular private outputs
        target=DEST/relative
        target.parent.mkdir(parents=True,exist_ok=True)
        if not target.exists():
            target.symlink_to(source)
