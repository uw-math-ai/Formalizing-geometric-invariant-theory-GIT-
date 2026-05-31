# `GIT/GitMain.lean` and `GIT/Invariants/` — Hilbert finiteness for GIT

This document mirrors [RO_abbrev.md](RO_abbrev.md): it describes the file split applied to
[GIT/GitMain.lean](GIT/GitMain.lean), the dependency graph, the per-file public API, and the
proof-chain index for the main theorem `GIT.GIT_finiteType_invariants`.

---

## 1. Math overview

Let `G` be a *linearly reductive* group over a field `k`, acting on a finitely generated
`ℕ`-graded `k`-algebra `R` by *grading-preserving* `k`-algebra automorphisms, with the action
*locally finite*. The Hilbert / Mumford theorem says the invariant subalgebra `R^G` is again
finitely generated as a `k`-algebra. The proof assembles four ingredients:

1. **Inherited grading.** `R^G` decomposes as the direct sum of its homogeneous pieces:
   `R^G = ⨁_d (𝒜 d ∩ R^G)`.
2. **F.g. from f.g. irrelevant ideal.** A graded algebra whose irrelevant ideal `R₊` is f.g. as
   an *ideal* is f.g. as a `(𝒜 0)`-algebra; with `𝒜 0` itself f.g. over `k`, transitivity gives
   `Algebra.FiniteType k R`.
3. **Reynolds ideal machinery.** Using a multiplicative Reynolds projection `ρ : R → R^G`, the
   irrelevant ideal of `R^G` is f.g. as an ideal of `R^G`.
4. **Assembly.** Combine the above with the multiplicative Reynolds projection coming from the
   `GIT/Reynolds/` package (`IsLinearlyReductive.exists_reynolds_mulCompat_of_isLocallyFinite`).

---

## 2. File-by-file dependency graph

```
              Mathlib                                  Mathlib + GIT/Reynolds umbrella
                 │                                                   │
                 ▼                                                   │
    Invariants/InheritedGrading                                      │
                 │                                                   │
                 ▼                                                   │
    Invariants/GradedFiniteType                                      │
                 │                                                   │
                 ▼                                                   │
    Invariants/ReynoldsIdeal                                         │
                 │                                                   │
                 └────────────────┬──────────────────────────────────┘
                                  ▼
                       Invariants/MainAssembly
                                  │
                                  ▼
                              GitMain
```

| File | One-line synopsis |
| --- | --- |
| [`Invariants/InheritedGrading.lean`](GIT/Invariants/InheritedGrading.lean) | `PreservesGrading`, `FixedSubalgebra k G R = R^G`, `FixedPieceInFixedSubalgebra G 𝒜 d`, and the direct-sum decomposition `fixedSubalgebra_decomposes`. |
| [`Invariants/GradedFiniteType.lean`](GIT/Invariants/GradedFiniteType.lean) | F.g.-from-irrelevant-fg over `𝒜 0` and over `k`, the deg-0 commutativity `AlgHom.map_decompose_zero`, and `fixedSubalgebra_finiteType`. |
| [`Invariants/ReynoldsIdeal.lean`](GIT/Invariants/ReynoldsIdeal.lean) | `ReynoldsGITSpanProperty`, `RGplusA_fg_of_reynolds`, the `reynolds_rewrite` family, finite-presentation extraction, `reynoldsGITSpanProperty_of_reynolds`. |
| [`Invariants/MainAssembly.lean`](GIT/Invariants/MainAssembly.lean) | Bridge: `extendedRGplus_le_irrelevant`, `RGplusA_eq_comap`, `exists_generators_of_irrelevant`, `ReynoldsLin` / `ReynoldsLin.of_isLocallyFinite`. |
| [`GitMain.lean`](GIT/GitMain.lean) | Umbrella: imports `MainAssembly`; contains *only* the main theorem `GIT_finiteType_invariants`. |

`MainAssembly.lean` is the only file that needs `GIT/Reynolds/` (via `import GIT.ReynoldsOperator`).

---

## 3. Public API surface

| File | Public symbol | Statement (informal) |
| --- | --- | --- |
| `InheritedGrading` | `PreservesGrading G 𝒜` | Predicate: every `g : G` maps `𝒜 d → 𝒜 d`. |
| `InheritedGrading` | `FixedSubalgebra k G R` | The invariant subalgebra `R^G` as a `Subalgebra k R`. |
| `InheritedGrading` | `FixedPieceInFixedSubalgebra G 𝒜 d` | The degree-`d` piece in `R^G`. |
| `InheritedGrading` | `fixed_component_mem_degree` | `(decompose 𝒜 x) d ∈ 𝒜 d` for `x ∈ R^G`. |
| `InheritedGrading` | `proj_commutes_of_preservesGrading` | `g`-action commutes with `proj_d`. |
| `InheritedGrading` | `fixed_component_is_fixed` | Components of an invariant are invariant. |
| `InheritedGrading` | `fixedPieceForget`, `fixedPieceForget_injective` | The forget `R^G ∩ 𝒜 d → 𝒜 d` and its injectivity. |
| `InheritedGrading` | `fixedSubalgebra_decomposes` | `R^G = ⨁_d (𝒜 d ∩ R^G)` as an internal direct sum. |
| `GradedFiniteType` | `irrelevantIdeal` | Abbreviation for `(HomogeneousIdeal.irrelevant 𝒜).toIdeal`. |
| `GradedFiniteType` | `exists_finset_homogeneous_pos_generators` | F.g.-ness of `R₊` ⇒ finite homogeneous positive-degree generators. |
| `GradedFiniteType` | `homogeneous_mem_adjoin_of_irrelevant_eq_span` | Every homogeneous element lies in `(𝒜 0)`-adjoin `T`. |
| `GradedFiniteType` | `finiteType_degreeZero_of_irrelevant_fg` | F.g. of `R` over `𝒜 0`. |
| `GradedFiniteType` | `finiteType_of_finitely_generated_irrelevant_ideal` | Convenience form. |
| `GradedFiniteType` | `finiteType_k_of_finitely_generated_irrelevant_ideal` | F.g. over `k` via transitivity. |
| `GradedFiniteType` | `AlgHom.map_decompose_zero` | Grading-preserving algebra maps commute with deg-`0` projection. |
| `GradedFiniteType` | `fixedSubalgebra_finiteType` | Specialization to `R^G`. |
| `ReynoldsIdeal` | `extendedRGplus_fg` | Noether: extended ideal is f.g. |
| `ReynoldsIdeal` | `exists_generators_extendedRGplus_from_RGplus` | Choose finite generators inside the given span. |
| `ReynoldsIdeal` | `ReynoldsGITSpanProperty` | `toR f ∈ span s` ⇒ `f ∈ span (ρ '' s)`. |
| `ReynoldsIdeal` | `mem_span_of_reynolds_generators` | Membership form of the Reynolds spanning property. |
| `ReynoldsIdeal` | `RGplusA_fg_of_reynolds` | `(R^G)₊` is f.g. as an ideal of `R^G`. |
| `ReynoldsIdeal` | `reynolds_rewrite` | Apply `ρ` to a relation `toR f = Σ x · a x`. |
| `ReynoldsIdeal` | `mem_ideal_span_lift_of_reynolds` | Ideal-membership form. |
| `ReynoldsIdeal` | `exists_finset_presentation_of_mem_span` | Extract a finite presentation from `Ideal.span`. |
| `ReynoldsIdeal` | `reynoldsGITSpanProperty_of_reynolds` | Reynolds ⇒ spanning property. |
| `MainAssembly` | `extendedRGplus_le_irrelevant` | Extension is contained in `R₊`. |
| `MainAssembly` | `RGplusA_eq_comap` | `(R^G)₊ = comap (R^G).val (extension)`. |
| `MainAssembly` | `exists_generators_of_irrelevant` | Finite generators of the extended ideal living in `R^G`. |
| `MainAssembly` | `ReynoldsLin` | Bundle `(ρ : R → R^G, id, mul)`. |
| `MainAssembly` | `ReynoldsLin.of_isLocallyFinite` | Build the bundle from `IsLinearlyReductive + IsLocallyFinite`. |
| `GitMain` | `GIT_finiteType_invariants` | **The main theorem.** |

Private helpers (visible only inside their host file) appear in §4 below as indented entries;
they are not part of the API surface.

---

## 4. Proof-chain index

For each major theorem, the helpers it ultimately depends on. Cross-file dependencies are
tagged with the host file. Helpers within the same file are indented.

### `GIT_finiteType_invariants` *(GitMain)*

```
GIT_finiteType_invariants
├── Algebra.FiniteType.isNoetherianRing               (Mathlib)
├── fixedSubalgebra_finiteType                        (GradedFiniteType)
│   └── finiteType_k_of_finitely_generated_irrelevant_ideal
│       └── finiteType_of_finitely_generated_irrelevant_ideal
│           └── finiteType_degreeZero_of_irrelevant_fg
│               ├── exists_finset_homogeneous_pos_generators
│               │   ├── irrelevant_eq_span_pos        [private]
│               │   └── fg_submodule_span_pos_of_irrelevant_fg [private]
│               └── homogeneous_mem_adjoin_of_irrelevant_eq_span
│                   ├── degreeProj                    [private def]
│                   ├── degreeProj_id_on_grade        [private]
│                   ├── degreeProj_sum_expansion      [private]
│                   ├── summand_in_adjoin_le          [private]
│                   ├── summand_eq_zero_not_le        [private]
│                   └── homogeneous_mem_adjoin_step   [private]
├── exists_generators_of_irrelevant                   (MainAssembly)
│   └── exists_generators_extendedRGplus_from_RGplus   (ReynoldsIdeal)
│       ├── extendedRGplus_fg
│       └── fg_submodule_span_of_ideal_span           [private]
├── RGplusA_eq_comap                                  (MainAssembly)
│   └── extendedRGplus_le_irrelevant
│       └── AlgHom.map_decompose_zero                  (GradedFiniteType)
│           ├── map_decompose_zero_same               [private]
│           └── map_decompose_zero_ne                 [private]
├── ReynoldsLin.of_isLocallyFinite                    (MainAssembly)
│   └── IsLinearlyReductive.exists_reynolds_mulCompat_of_isLocallyFinite
│                                                     (GIT/Reynolds/AlgebraReynolds)
├── RGplusA_fg_of_reynolds                            (ReynoldsIdeal)
│   └── mem_span_of_reynolds_generators
└── reynoldsGITSpanProperty_of_reynolds               (ReynoldsIdeal)
    ├── exists_finset_presentation_of_mem_span
    │   ├── exists_finset_presentation_mem            [private]
    │   ├── exists_finset_presentation_add            [private]
    │   └── exists_finset_presentation_smul           [private]
    ├── mem_ideal_span_lift_of_reynolds
    │   └── reynolds_rewrite
    ├── rho_eq_lift_on_s                              [private]
    └── lift_image_eq_rho_image                       [private]
```

### `fixedSubalgebra_decomposes` *(InheritedGrading)*

```
fixedSubalgebra_decomposes
├── decomposes_injective                              [private]
│   ├── fixedPieceForget_injective
│   └── DirectSum.Decomposition.isInternal            (Mathlib)
└── decomposes_surjective                             [private]
    ├── decomposesWitness                             [private noncomputable def]
    │   ├── fixed_component_is_fixed
    │   │   └── proj_commutes_of_preservesGrading
    │   │       ├── proj_commutes_same                [private]
    │   │       └── proj_commutes_ne                  [private]
    │   └── fixed_component_mem_degree
    └── decomposesWitness_map_forget                  [private]
```

### `RGplusA_fg_of_reynolds` *(ReynoldsIdeal)*

```
RGplusA_fg_of_reynolds
└── mem_span_of_reynolds_generators
    └── ReynoldsGITSpanProperty                       [def]
```

### `reynoldsGITSpanProperty_of_reynolds` *(ReynoldsIdeal)*

```
reynoldsGITSpanProperty_of_reynolds
├── exists_finset_presentation_of_mem_span             [4 private sub-helpers; see above]
├── mem_ideal_span_lift_of_reynolds
│   └── reynolds_rewrite
└── lift_image_eq_rho_image
    └── rho_eq_lift_on_s
```

---

## 5. Naming conventions

Following [Mathlib's naming guide](https://leanprover-community.github.io/contribute/naming.html):

* **`camelCase`** for definitions and structure fields: `FixedSubalgebra`,
  `FixedPieceInFixedSubalgebra`, `irrelevantIdeal`, `degreeProj`, `commonWitness`,
  `ReynoldsLin`, `ReynoldsGITSpanProperty`, …
* **`snake_case`** for theorems/lemmas with embedded `camelCase` for type-like fragments:
  `fixedSubalgebra_decomposes`, `finiteType_degreeZero_of_irrelevant_fg`,
  `homogeneous_mem_adjoin_of_irrelevant_eq_span`, `RGplusA_fg_of_reynolds`,
  `reynoldsGITSpanProperty_of_reynolds`, `GIT_finiteType_invariants`.
* The qualifier **`_of_`** introduces a hypothesis:
  `finiteType_k_of_finitely_generated_irrelevant_ideal`, `RGplusA_fg_of_reynolds`,
  `ReynoldsLin.of_isLocallyFinite`, `exists_generators_extendedRGplus_from_RGplus`.
* Every public declaration carries a `**…**` Math-statement / `Proof idea` docstring.
* Every theorem body is kept strictly under 15 lines; longer proofs are decomposed into named
  private helpers (each itself ≤14 lines).

### Namespaces used

| Namespace | Lives in |
| --- | --- |
| `GIT` | All five files. |
| `GIT.AlgHom` (`AlgHom.map_decompose_zero`) | `GradedFiniteType` |
| Re-used Mathlib namespaces (`HomogeneousIdeal`, `Submodule`, `Ideal`, `Algebra`, `DirectSum`, `Subsemiring`, …) | as appropriate |
