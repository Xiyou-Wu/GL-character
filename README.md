# GL-character

[![Compile blueprint](https://github.com/Xiyou-Wu/GL-character/actions/workflows/blueprint.yml/badge.svg)](https://github.com/Xiyou-Wu/GL-character/actions/workflows/blueprint.yml)

Lean 4 formalization and blueprint for average character criteria for Thurston circle packings.

## Local build

```powershell
lake exe cache get
lake build
```

The blueprint source is in `blueprint/src`.

## Blueprint

GitHub Actions builds and publishes:

- Web blueprint: `https://xiyou-wu.github.io/GL-character/blueprint/`
- PDF blueprint: `https://xiyou-wu.github.io/GL-character/blueprint.pdf`
- API docs: `https://xiyou-wu.github.io/GL-character/docs/`

For local blueprint builds, install `leanblueprint` and run:

```powershell
leanblueprint all
```
