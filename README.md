# Rudin — Functional Analysis (2nd ed.) in Lean 4

Formalisation of Walter Rudin, *Functional Analysis*, 2nd edition, using
[Lean 4](https://lean-lang.org/) and [mathlib](https://github.com/leanprover-community/mathlib4).

Strategy: reuse mathlib's existing analysis scaffolding wherever possible
and introduce new definitions only for topics not yet covered upstream.

## Layout

| File | Book chapter |
| ---- | ------------ |
| [Rudin/Ch01_TopologicalVectorSpaces.lean](Rudin/Ch01_TopologicalVectorSpaces.lean) | 1. Topological Vector Spaces |
| [Rudin/Ch02_Completeness.lean](Rudin/Ch02_Completeness.lean) | 2. Completeness |
| [Rudin/Ch03_Convexity.lean](Rudin/Ch03_Convexity.lean) | 3. Convexity |
| [Rudin/Ch04_DualityInBanachSpaces.lean](Rudin/Ch04_DualityInBanachSpaces.lean) | 4. Duality in Banach Spaces |
| [Rudin/Ch05_SomeApplications.lean](Rudin/Ch05_SomeApplications.lean) | 5. Some Applications |
| [Rudin/Ch06_TestFunctionsAndDistributions.lean](Rudin/Ch06_TestFunctionsAndDistributions.lean) | 6. Test Functions and Distributions |
| [Rudin/Ch07_FourierTransforms.lean](Rudin/Ch07_FourierTransforms.lean) | 7. Fourier Transforms |
| [Rudin/Ch08_ApplicationsToDifferentialEquations.lean](Rudin/Ch08_ApplicationsToDifferentialEquations.lean) | 8. Applications to Differential Equations |
| [Rudin/Ch09_TauberianTheory.lean](Rudin/Ch09_TauberianTheory.lean) | 9. Tauberian Theory |
| [Rudin/Ch10_BanachAlgebras.lean](Rudin/Ch10_BanachAlgebras.lean) | 10. Banach Algebras |
| [Rudin/Ch11_CommutativeBanachAlgebras.lean](Rudin/Ch11_CommutativeBanachAlgebras.lean) | 11. Commutative Banach Algebras |
| [Rudin/Ch12_BoundedOperatorsOnAHilbertSpace.lean](Rudin/Ch12_BoundedOperatorsOnAHilbertSpace.lean) | 12. Bounded Operators on a Hilbert Space |
| [Rudin/Ch13_UnboundedOperators.lean](Rudin/Ch13_UnboundedOperators.lean) | 13. Unbounded Operators |

## Build

```sh
lake exe cache get    # fetch mathlib's pre-built oleans
lake build
```

Requires the Lean toolchain pinned in [lean-toolchain](lean-toolchain)
(`elan` will install it automatically).

### Blueprint and API docs

```sh
leanblueprint web                       # regenerate blueprint HTML
DOCGEN_SRC=file lake build Rudin:docs   # regenerate API docs
# symlink docs into blueprint/web/docs/ so docs/find/#doc/... resolves:
mkdir -p blueprint/web/docs
( cd blueprint/web/docs && \
  for e in /Users/so/Repos/rudin-lean/.lake/build/doc/*; do \
    name=$(basename "$e"); [ -e "$name" ] || ln -s "$e" "$name"; \
  done )
leanblueprint serve                     # browse at http://localhost:8000/
```

The `DOCGEN_SRC=file` env var makes doc-gen4 use `file://` source URIs
(required when there is no GitHub remote for the repo).

### Hosted blueprint (GitHub Pages)

The [Blueprint workflow](.github/workflows/blueprint.yml) builds the
blueprint HTML, the `print.pdf`, and the doc-gen4 API docs on every push
to `main` and deploys them together to GitHub Pages. The blueprint lives
at the site root; the API docs are served from `/docs/` so that the
blueprint's `\lean{...}` cross-references (which render as
`docs/find/#doc/<fq-name>`) resolve correctly.

To enable it on a fresh clone: push the repo to GitHub, then in
*Settings → Pages* set **Source** to *GitHub Actions*.

## Status

Only a seed theorem (Rudin 1.6 — translation and scalar-multiplication
homeomorphisms) is filled in so far; the remaining chapters are stub
files with mathlib-import pointers.
