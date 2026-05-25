# GL-character

Lean 4 formalization project for Ge--Lin character related statements.

## Local development

Install the Lean 4 VS Code extension, open this repository as the workspace root, and run:

```powershell
lake exe cache get
lake build
```

The Lean server reads `lean-toolchain` and `lakefile.toml` from the repository root.

## Documentation

HTML documentation is generated with `doc-gen4`:

```powershell
cd docbuild
$env:MATHLIB_NO_CACHE_ON_UPDATE='1'
lake update
lake build GLCharacter:docs
```

The generated site is under `docbuild/.lake/build/doc/`. GitHub Pages is deployed by `.github/workflows/docs.yml`.
