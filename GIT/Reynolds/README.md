# `GIT/Reynolds/` — the Reynolds operator development

This directory contains a per-section split of the Reynolds-operator construction. Importing
[`GIT.ReynoldsOperator`](../ReynoldsOperator.lean) (the umbrella file) brings in everything;
importing individual files brings in just the corresponding chunk.

---

## 1. Math overview

A group `G` is **linearly reductive** over a field `k` when every finite-dimensional
representation `M : Rep k G` is semisimple. The **Reynolds operator** on `M` is the canonical
`G`-equivariant projection `πₘ : M → Mᴳ` onto the invariants. We construct it in three stages:

1. **Finite-dimensional case.** Semisimplicity supplies a `G`-stable complement `W` to the
   invariants; the projection along `W` is `πₘ`. It is natural in `M` and unique.
2. **Locally finite case.** When `G` acts on `R` so that every `r` lies in a finite-dimensional
   `G`-stable submodule `V(r)`, we apply the f.d. construction to each `V(r)` and glue. The
   "naturality on overlaps" lemma guarantees the values agree, giving a global linear map.
3. **Algebra case.** When `R` is a `k`-algebra and `G` acts by ring automorphisms, the Reynolds
   operator is automatically `Rᴳ`-linear: `π(a · r) = a · π(r)` for every `a ∈ Rᴳ`. This is the
   Reynolds identity underlying Hilbert finiteness in GIT.

---

## 2. File-by-file dependency graph

```
                Mathlib                    Mathlib
                   │                          │
                   ▼                          ▼
        LocallyFiniteActions          LinearReductivity
                   │                          │
                   │                          ▼
                   │              FiniteDimensionalReynolds
                   │                          │
                   └────────────┬─────────────┘
                                ▼
                    LocallyFiniteReynolds
                                │
                                ▼
                       AlgebraReynolds
```

| File | One-line synopsis |
| --- | --- |
| [`LocallyFiniteActions.lean`](LocallyFiniteActions.lean) | `Representation.IsLocallyFinite` and the lemma that finite-monoid actions are locally finite. |
| [`LinearReductivity.lean`](LinearReductivity.lean) | `IsLinearlyReductive` class, Maschke instance, invariants as a subrep, `Rep.mkHom` family, `Subrepresentation.toSubmodule_isCompl`. |
| [`FiniteDimensionalReynolds.lean`](FiniteDimensionalReynolds.lean) | Finite-dim **existence** (`exists_reynolds`), **naturality** (`reynolds_natural`), **uniqueness** (`reynolds_unique`). |
| [`LocallyFiniteReynolds.lean`](LocallyFiniteReynolds.lean) | Glue helpers (`subrepInclusion`, `wrapLocalProj`, `local_proj_agree_on_overlap`), private `LRD` bundle, **existence** (`exists_reynolds_of_isLocallyFinite`), **uniqueness** (`reynolds_unique_of_isLocallyFinite`). |
| [`AlgebraReynolds.lean`](AlgebraReynolds.lean) | `Representation.leftMulHom`, private `reynoldsDefect` machinery, `Rᴳ`-linearity (`exists_reynolds_mulCompat_of_isLocallyFinite`). |

The `import` lines in each file mirror this graph exactly.

---

## 3. Public API surface

| File | Public theorem / def | Statement (informal) |
| --- | --- | --- |
| `LocallyFiniteActions` | `Representation.IsLocallyFinite` | Predicate: every `r` lies in a f.d. `G`-stable submodule. |
| `LocallyFiniteActions` | `Representation.isLocallyFinite_of_finite` | Finite-monoid actions are locally finite. |
| `LinearReductivity` | `IsLinearlyReductive` | Class: every f.d. rep is semisimple. |
| `LinearReductivity` | `IsLinearlyReductive.of_fintype` | Maschke: finite group with `|G|` invertible in `k` is l.r. |
| `LinearReductivity` | `Representation.invariantsSubrepresentation` | `ρ.invariants` as a `Subrepresentation ρ`. |
| `LinearReductivity` | `Subrepresentation.toSubmodule_isCompl` | `IsCompl` on subreps transfers to submodules. |
| `LinearReductivity` | `Rep.mkHom`, `Rep.mkHom_hom`, `Rep.isProj_invariants_apply_rho` | Reusable `Rep`-morphism plumbing. |
| `FiniteDimensionalReynolds` | `IsLinearlyReductive.exists_reynolds` | F.d.: ∃ `Rep`-morphism projecting onto `Mᴳ`. |
| `FiniteDimensionalReynolds` | `IsLinearlyReductive.reynolds_natural` | The projection commutes with every `Rep`-morphism `I : M₁ ⟶ M₂`. |
| `FiniteDimensionalReynolds` | `IsLinearlyReductive.reynolds_unique` | Any two such `Rep`-morphism projections coincide. |
| `LocallyFiniteReynolds` | `Representation.sup_le_comap_of_stable` | Sup of `G`-stable submodules is `G`-stable. |
| `LocallyFiniteReynolds` | `Rep.subrepInclusion` | Submodule inclusion as a `Rep`-morphism. |
| `LocallyFiniteReynolds` | `Rep.wrapLocalProj` | Wrap an orbit-constant local projection as a `Rep`-morphism. |
| `LocallyFiniteReynolds` | `IsLinearlyReductive.exists_reynolds_of_isLocallyFinite` | Loc. finite: ∃ `Rep`-morphism projecting onto `Rᴳ`. |
| `LocallyFiniteReynolds` | `IsLinearlyReductive.reynolds_unique_of_isLocallyFinite` | Two such projections coincide. |
| `AlgebraReynolds` | `Representation.leftMulHom` | `s ↦ a · s` as a `k`-linear endomorphism. |
| `AlgebraReynolds` | `IsLinearlyReductive.exists_reynolds_mulCompat_of_isLocallyFinite` | The Reynolds projection satisfies `π(a · r) = a · π r` for every invariant `a`. |

Private auxiliary lemmas (visible only inside their host file) are listed in §4 below as
"helper" entries; they are not part of the API.

---

## 4. Proof-chain index

For each public theorem, the helpers it ultimately depends on. Helpers within the same file are
indented; cross-file dependencies are tagged with the file name.

### `IsLinearlyReductive.exists_reynolds` *(FiniteDimensionalReynolds)*

```
exists_reynolds
├── exists_isCompl_invariants
│   ├── IsLinearlyReductive.isSemisimple                (LinearReductivity)
│   ├── Representation.invariantsSubrepresentation      (LinearReductivity)
│   └── Subrepresentation.toSubmodule_isCompl           (LinearReductivity)
├── Representation.reynoldsOfIsCompl                    [def]
├── Representation.isProj_reynoldsOfIsCompl
├── Representation.reynoldsOfIsCompl_apply_of_mem
├── Representation.reynoldsOfIsCompl_apply_rho          (uses _apply_of_mem)
└── Rep.mkHom                                            (LinearReductivity)
```

### `IsLinearlyReductive.reynolds_natural` *(FiniteDimensionalReynolds)*

```
reynolds_natural
├── Rep.ker_isProj_stable          ← Rep.isProj_invariants_apply_rho (LinearReductivity)
├── Rep.hom_apply_mem_invariants   ← Rep.hom_comm_apply (Mathlib)
├── reynoldsNaturalL               [private def, depends on Rep.ker_isProj_stable]
├── cocycle_mem_reynoldsNaturalL   [private]
├── reynoldsNaturalT_eq_bot        [private; uses cocycle_mem_reynoldsNaturalL +
│                                   Subrepresentation.toSubmodule_isCompl
│                                   (LinearReductivity, via h₁.isCompl)]
└── reynoldsNaturalL_eq_top        [private; uses _T_eq_bot and IsLinearlyReductive.isSemisimple]
```

### `IsLinearlyReductive.reynolds_unique` *(FiniteDimensionalReynolds)*

```
reynolds_unique
└── reynolds_natural (specialized to I = 𝟙 M)
```

### `IsLinearlyReductive.exists_reynolds_of_isLocallyFinite` *(LocallyFiniteReynolds)*

```
exists_reynolds_of_isLocallyFinite
├── LRD.of_isLocallyFinite                              [private noncomputable def]
│   └── IsLinearlyReductive.exists_reynolds             (FiniteDimensionalReynolds)
├── LRD.f                                                [private def]
├── LRD.f_add, LRD.f_smul     [each uses LRD.f_eq + exists_reynolds + sup_le_comap_of_stable]
├── LRD.f_eq                                             [uses local_proj_agree_on_overlap]
│   └── local_proj_agree_on_overlap                      [private; uses reynolds_natural +
│                                                          subrepInclusion + wrapLocalProj +
│                                                          sup_le_comap_of_stable]
├── LRD.f_mapMem, LRD.f_mapId                           [direct from D.isProj.map_{mem,id}]
└── LRD.f_apply_rho                                      [uses LRD.f_eq + D.apply_rho]
                                                          → final assembly via Rep.mkHom
                                                          (LinearReductivity)
```

### `IsLinearlyReductive.reynolds_unique_of_isLocallyFinite` *(LocallyFiniteReynolds)*

```
reynolds_unique_of_isLocallyFinite
└── reynolds_unique_at                                   [private; for each r ∈ R]
    ├── IsLocallyFinite           (LocallyFiniteActions) [pick a f.d. G-stable witness V ∋ r]
    ├── finite_submodule_map      [private; M.Finite (Submodule.map p V)]
    ├── commonWitness             [private def: W := V ⊔ p₁(V) ⊔ p₂(V)]
    ├── commonWitness_stable      [private; uses map_le_invariants + le_invariants_comap]
    │   ├── map_le_invariants     [private]
    │   └── le_invariants_comap   [private]
    ├── commonWitness_maps_self   [private; p sends W into W when p is a proj. onto invariants]
    ├── restrictHom               [private noncomputable def]
    ├── restrictHom_isProj        [private]
    └── reynolds_unique           (FiniteDimensionalReynolds; applied to W as ambient)
```

### `IsLinearlyReductive.exists_reynolds_mulCompat_of_isLocallyFinite` *(AlgebraReynolds)*

```
exists_reynolds_mulCompat_of_isLocallyFinite
├── exists_reynolds_of_isLocallyFinite                  (LocallyFiniteReynolds)
├── Representation.leftMulHom                            [def]
├── reynoldsDefect                                       [private noncomputable def, uses leftMulHom]
├── reynoldsDefect_equiv                                 [private; uses Rep.hom_comm_apply]
├── reynoldsDefect_mem_invariants                        [private]
├── reynoldsDefect_vanishes_on_invariants                [private]
├── reynoldsAddDefect                                    [private noncomputable def]
│   └── Rep.mkHom                                        (LinearReductivity)
├── reynoldsAddDefect_isProj                             [private]
└── reynolds_unique_of_isLocallyFinite                  (LocallyFiniteReynolds)
                                                          [forces δ + π = π ⟹ δ = 0]
```

---

## 5. Naming conventions

Following [Mathlib's naming guide](https://leanprover-community.github.io/contribute/naming.html):

* **`camelCase`** for definitions and structure fields: `reynoldsOfIsCompl`, `wrapLocalProj`,
  `commonWitness`, `reynoldsAddDefect`, `LRD.f`, `LRD.V`, …
* **`snake_case`** for theorems and lemmas with embedded `camelCase` for type-like fragments:
  `exists_reynolds`, `reynolds_unique`, `reynolds_unique_of_isLocallyFinite`,
  `commonWitness_maps_self`, …
* The qualifier **`_of_`** introduces a hypothesis: `exists_reynolds_of_isLocallyFinite`,
  `isLocallyFinite_of_finite`, `IsLinearlyReductive.of_fintype`.
* Each public theorem has a docstring with a bold one-line tag in `**…**`, a `Math statement`
  line, and a `Proof idea` paragraph.
* Theorem bodies are kept strictly under 15 lines; longer proofs are decomposed into named
  helpers.

### Namespaces used

| Namespace | Lives in |
| --- | --- |
| `Representation` | `LocallyFiniteActions`, `LinearReductivity`, `FiniteDimensionalReynolds`, `LocallyFiniteReynolds`, `AlgebraReynolds` |
| `Rep` | `LinearReductivity`, `FiniteDimensionalReynolds`, `LocallyFiniteReynolds` |
| `Subrepresentation` | `LinearReductivity` |
| `IsLinearlyReductive` | `LinearReductivity` (class + Maschke), then theorems in every later file |
| `IsLinearlyReductive.LRD` | `LocallyFiniteReynolds` (private structure + its method namespace) |
