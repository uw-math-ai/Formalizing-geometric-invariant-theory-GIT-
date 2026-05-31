# Refactor `GIT/ReynoldsOperator.lean` to meet Mathlib-PR standards

## Context

The current `ReynoldsOperator.lean` is mathematically correct and lint-clean, but the four core theorems are long monolithic proofs (40, 75, 185, 123, 114 lines). Mathlib PRs prefer:

- **Naming** per <https://leanprover-community.github.io/contribute/naming.html>: namespaced, `camelCase` for defs and `snake_case` for theorems, with embedded `camelCase` for types; consistent `_of_` qualifiers.
- **Granularity**: each theorem strictly **< 15 lines** of body, with helper lemmas for re-usable algebraic facts.
- **Documentation**: every `def`/`theorem`/`lemma` carries a docstring stating the math content and proof idea.

Goal: refactor without changing the public API behaviour. Existence/uniqueness statements survive (possibly renamed), and downstream `GitMain.lean` continues to compile.

## Naming changes

| Current | New (Mathlib-style) |
| --- | --- |
| `Rep.mkHom` / `Rep.mkHom_hom` | keep — already idiomatic |
| `Rep.isProj_invariants_apply_rho` | `Rep.IsProj.apply_rho` |
| `Representation.IsLocallyFinite` | keep |
| `Representation.isLocallyFinite_of_finite` | keep |
| `IsLinearlyReductive` | keep |
| `IsLinearlyReductive.of_fintype` | keep |
| `Representation.invariantSubrepresentation` | `Representation.invariantsSubrepresentation` (plural, matches `ρ.invariants`) |
| `IsLinearlyReductive.exists_reynolds_projection` | `IsLinearlyReductive.exists_reynolds` |
| `IsLinearlyReductive.reynolds_natural` | `IsLinearlyReductive.reynolds_natural` (keep) |
| `IsLinearlyReductive.reynolds_unique` | keep |
| `exists_reynolds_of_locallyFinite` | `IsLinearlyReductive.exists_reynolds_of_isLocallyFinite` |
| `IsLinearlyReductive.reynolds_unique_locallyFinite` | `IsLinearlyReductive.reynolds_unique_of_isLocallyFinite` |
| `exists_reynolds_mul_compat_of_locallyFinite` | `IsLinearlyReductive.exists_reynolds_mulCompat_of_isLocallyFinite` |

All new helper lemmas live in either `Rep`, `Representation`, `Subrepresentation`, or `IsLinearlyReductive` namespaces.

## Decomposition plan

Every lemma below has a docstring of the form:
```
/-- **<one-line math statement>.**
<2–4 sentences of proof sketch>. -/
```
and a body strictly **< 15 lines**.

### A. Locally-finite preliminaries

- `Representation.IsLocallyFinite` *(def, keep)* — definition unchanged.
- **New helper** `Representation.span_orbit_stable` *(lemma, ~10 lines)*  
  Math: for `r : R` and `g : G`, `g • Submodule.span k (G • r) ⊆ Submodule.span k (G • r)`.  
  Proof: `Submodule.span_induction`, using `g • (g' • r) = (g * g') • r`.
- `Representation.isLocallyFinite_of_finite` *(theorem, ≤ 10 lines)* — refactored using `span_orbit_stable`.

### B. Linear reductivity (mostly unchanged)

- `IsLinearlyReductive` *(class, keep)*.
- `IsLinearlyReductive.of_fintype` *(instance, keep, ≤ 10 lines)*.
- `Representation.invariantsSubrepresentation` *(def, ≤ 10 lines)*.
- **New helper** `Subrepresentation.toSubmodule_isCompl` *(lemma, ≤ 8 lines)*  
  Math: `IsCompl (S T : Subrepresentation ρ) → IsCompl S.toSubmodule T.toSubmodule`.  
  Proof: unfold `IsCompl` and use `Subrepresentation.toSubmodule_inf` / `_sup` simp-lemmas; this is the lines 156–163 block extracted.

### C. Reynolds projection: finite-dimensional case

Split `exists_reynolds` (currently 40 lines) into:

- **New** `IsLinearlyReductive.exists_invariants_isCompl` *(lemma, ≤ 8 lines)*  
  Math: `∃ W : Subrepresentation M.ρ, IsCompl M.ρ.invariants W.toSubmodule`.  
  Proof: `IsSemisimpleRepresentation.exists_isCompl` + `Subrepresentation.toSubmodule_isCompl`.
- **New** `Representation.reynoldsOfIsCompl` *(noncomputable def, ≤ 6 lines)*  
  Math: given `hc : IsCompl ρ.invariants W`, the linear map `ρ.invariants.subtype ∘ₗ linearProjOfIsCompl …`.
- **New** `Representation.isProj_reynoldsOfIsCompl` *(lemma, ≤ 10 lines)*  
  Math: `reynoldsOfIsCompl hc` is a projection onto `ρ.invariants`.  
  Proof: direct from `Submodule.linearProjOfIsCompl_apply_left`.
- **New** `Representation.reynoldsOfIsCompl_apply_invariant` *(lemma, ≤ 6 lines)*  
  Math: on `v ∈ ρ.invariants`, `reynoldsOfIsCompl hc v = v`; this is a corollary of `isProj.map_id`.
- **New** `Representation.reynoldsOfIsCompl_apply_W` *(lemma, ≤ 6 lines)*  
  Math: on `v ∈ W`, `reynoldsOfIsCompl hc v = 0`.
- **New** `Representation.reynoldsOfIsCompl_equiv` *(lemma, ≤ 14 lines)*  
  Math: assuming the complement `W` is `G`-stable, `reynoldsOfIsCompl hc (ρ g v) = reynoldsOfIsCompl hc v`.  
  Proof: decompose `v = vi + vw`, use the two `_apply_*` lemmas plus invariance of `vi` and stability of `W`.
- `IsLinearlyReductive.exists_reynolds` *(theorem, ≤ 12 lines)*  
  Assembly: combine `exists_invariants_isCompl` + `Rep.mkHom` + the four helper lemmas.

Split `reynolds_natural` (currently 75 lines) into:

- **New** `Rep.ker_hom_stable` *(lemma, ≤ 6 lines)*  
  Math: the kernel of `P.hom.hom` (for `P : M ⟶ M` a projection onto invariants) is `G`-stable.  
  Proof: `P (ρ g v) = P v` (from `Rep.IsProj.apply_rho`), so `v ∈ ker P → P (ρ g v) = 0`.
- **New** `Rep.map_invariant_of_isProj` *(lemma, ≤ 6 lines)*  
  Math: if `P` is a Rep-projection onto invariants and `v ∈ ker P`'s ambient space, then `I.hom.hom (P v) ∈ M₂.ρ.invariants`.
- **New** `IsLinearlyReductive.reynoldsKernel` *(def, ≤ 5 lines)*  
  Math: package `ker π₁` as a `Rep k G`.
- **New** `IsLinearlyReductive.reynolds_L_subrep` *(def, ≤ 8 lines)*  
  Math: the `Subrepresentation` `L = {w ∈ ker π₁ | π₂(ι w) = 0}`.
- **New** `IsLinearlyReductive.reynolds_cocycle_mem_L` *(lemma, ≤ 6 lines)*  
  Math: for any `x ∈ ker π₁`, `ρ g x - x ∈ L`.  
  Proof: `π₂(ι(ρ g x)) = ρ g (π₂(ι x)) = π₂(ι x)` since `π₂(ι x) ∈ invariants` (lemma above).
- **New** `IsLinearlyReductive.reynolds_complement_eq_bot` *(lemma, ≤ 14 lines)*  
  Math: any `Subrepresentation`-complement `T` of `L` inside `reynoldsKernel` is `⊥`.  
  Proof: each `t ∈ T` is invariant (its cocycles vanish in `L ⊓ T = ⊥`), but invariants ∩ ker π₁ = `⊥`.
- **New** `IsLinearlyReductive.reynolds_L_eq_top` *(lemma, ≤ 6 lines)*  
  Math: `L = ⊤`. Corollary of `_complement_eq_bot`.
- `IsLinearlyReductive.reynolds_natural` *(theorem, ≤ 14 lines)*  
  Assembly: decompose `v = π₁ v + w`, push the first piece through `map_id`, conclude via `reynolds_L_eq_top` applied to `w`.
- `IsLinearlyReductive.reynolds_unique` *(theorem, ≤ 10 lines)* — unchanged structurally, just rename references.

### D. Reynolds projection: locally-finite case

Split `exists_reynolds_of_isLocallyFinite` (currently 185 lines) into:

- **New** `Representation.localReynoldsHyp` *(structure, ≤ 8 lines)*  
  Math: bundles `(V, hV_fin, hV_stable, hV_comap, hV_mem)` for the locally-finite witness around an element.  
  *(Optional — only if structure makes the helpers cleaner; otherwise replicate fields.)*
- **New** `Representation.localReynolds` *(noncomputable def, ≤ 10 lines)*  
  Math: for each `r : R` choose a local Reynolds projection on `V r` using `exists_reynolds` on the finite-dim subrep.
- **New** `Representation.localReynolds_isProj` *(lemma, ≤ 6 lines)*  
  Spec from the existential.
- **New** `Representation.localReynolds_apply_rho` *(lemma, ≤ 6 lines)*  
  Pulled via `Rep.IsProj.apply_rho`.
- **New** `Representation.subrep_inclusion_mkHom` *(def, ≤ 10 lines)*  
  Math: `Submodule.inclusion (W₁ ≤ W)` as a `Rep` morphism between the corresponding subrepresentations.  
  Proof: built via `Rep.mkHom` with a one-line `ext; simp [Submodule.inclusion]` commutativity proof.
- **New** `Representation.mkLocalReynolds_hom` *(def, ≤ 10 lines)*  
  Math: wrap a given local-projection linear map `π : ↥W →ₗ[k] ↥W` (with its orbit-constancy) as a `Rep` self-morphism on the subrepresentation `Mamb.subrepresentation W _`.
- **New** `IsLinearlyReductive.localReynolds_agree_on_sup` *(lemma, ≤ 14 lines)*  
  Math: for two G-stable f.d. submodules `W₁, W₂` with respective local Reynolds projections `π₁, π₂`, and `r ∈ W₁ ∩ W₂`, `(π₁ ⟨r,_⟩ : R) = (π₂ ⟨r,_⟩ : R)`.  
  Proof: pick `W := W₁ ⊔ W₂`, find a Reynolds projection `π_W` there, apply `reynolds_natural` to the inclusions `W_i ↪ W`, chain three equalities.
- **New** `IsLinearlyReductive.localReynoldsFun` *(noncomputable def, ≤ 6 lines)*  
  Math: `f : R → R, r ↦ (localReynolds r : R)`.
- **New** `IsLinearlyReductive.localReynoldsFun_eq` *(lemma, ≤ 10 lines)*  
  Math: for *any* f.d. G-stable `W ∋ r` with a Reynolds projection `πW`, `f r = (πW ⟨r,_⟩ : R)`.  
  Proof: direct application of `localReynolds_agree_on_sup`.
- **New** `IsLinearlyReductive.localReynoldsFun_add` *(lemma, ≤ 12 lines)*.
- **New** `IsLinearlyReductive.localReynoldsFun_smul` *(lemma, ≤ 10 lines)*.
- **New** `IsLinearlyReductive.localReynoldsFun_map_mem` *(lemma, ≤ 8 lines)*.
- **New** `IsLinearlyReductive.localReynoldsFun_map_id` *(lemma, ≤ 10 lines)*.
- **New** `IsLinearlyReductive.localReynoldsFun_equiv` *(lemma, ≤ 12 lines)*.
- `IsLinearlyReductive.exists_reynolds_of_isLocallyFinite` *(theorem, ≤ 14 lines)*  
  Assembly: package the `localReynoldsFun` as a linear map, then a `Rep` morphism.

Split `reynolds_unique_of_isLocallyFinite` (currently 123 lines) into:

- **New** `Representation.map_le_invariants_of_isProj` *(lemma, ≤ 6 lines)*  
  Math: image of a projection onto invariants lies in invariants.
- **New** `Representation.invariants_stable` *(lemma, ≤ 6 lines)*  
  Math: any `S ≤ ρ.invariants` is G-stable (`S ≤ S.comap (ρ g)`).
- **New** `IsLinearlyReductive.commonWitness` *(noncomputable def, ≤ 8 lines)*  
  Math: `W := V ⊔ map p₁ V ⊔ map p₂ V`, packaged with its stability proof, where `V` is the f.d. witness for `r`.
- **New** `IsLinearlyReductive.commonWitness_finiteDimensional` *(instance, ≤ 8 lines)*  
  via `Module.Finite.of_surjective` on `Submodule.map p V`, then `Submodule.finiteDimensional_sup`.
- **New** `IsLinearlyReductive.commonWitness_maps_to_self` *(lemma, ≤ 14 lines)*  
  Math: for `p ∈ {p₁, p₂}`, `p` maps `W` into `W`.  
  Proof: case-split using `Submodule.mem_sup`, three cases (V, p₁ V, p₂ V).
- **New** `IsLinearlyReductive.commonWitness_restrict_isProj` *(lemma, ≤ 12 lines)*  
  Math: the restriction of an invariants-projection to the stable subspace `W` is again a projection onto `(MW.ρ).invariants`.
- `IsLinearlyReductive.reynolds_unique_of_isLocallyFinite` *(theorem, ≤ 14 lines)*  
  Assembly: build `MW`, restrict both `p₁, p₂` to it, apply f.d. uniqueness, read off equality at `r`.

### E. Reynolds projection on algebras

Split `exists_reynolds_mulCompat_of_isLocallyFinite` (currently 114 lines) into:

- **New** `Representation.leftMulHom` *(def, ≤ 8 lines)*  
  Math: for `a : R`, the `k`-linear map `s ↦ a * s` (built via `mul_smul_comm`).
- **New** `Representation.invariants_mul_invariants` *(lemma, ≤ 8 lines)*  
  Math: if `a, s ∈ σ.invariants` then `a * s ∈ σ.invariants`. (Uses `smul_mul'`.)
- **New** `IsLinearlyReductive.reynoldsDefect` *(noncomputable def, ≤ 6 lines)*  
  Math: `δ_a r := π(a r) - a * π r`, as a `k`-linear map (for any fixed invariant `a`).
- **New** `IsLinearlyReductive.reynoldsDefect_equiv` *(lemma, ≤ 12 lines)*  
  Math: `δ_a (g • r) = g • δ_a r`. Proof: split into the two summands.
- **New** `IsLinearlyReductive.reynoldsDefect_mem_invariants` *(lemma, ≤ 12 lines)*.
- **New** `IsLinearlyReductive.reynoldsDefect_vanishes_on_invariants` *(lemma, ≤ 10 lines)*.
- **New** `IsLinearlyReductive.reynoldsAddDefect_isProj` *(lemma, ≤ 12 lines)*  
  Math: `δ_a + π` is again a projection onto invariants.
- **New** `IsLinearlyReductive.reynoldsAddDefect_equiv` *(lemma, ≤ 8 lines)*  
  Math: `δ_a + π` is G-equivariant ⇒ assembles as a Rep morphism.
- `IsLinearlyReductive.exists_reynolds_mulCompat_of_isLocallyFinite` *(theorem, ≤ 14 lines)*  
  Assembly: apply `reynolds_unique_of_isLocallyFinite` to `(δ_a + π)` vs. `π`, conclude `δ_a = 0`.

## Files modified

Only one file: [GIT/ReynoldsOperator.lean](GIT/ReynoldsOperator.lean).

`GitMain.lean` references `exists_reynolds_of_locallyFinite` and `exists_reynolds_mul_compat_of_locallyFinite` — I'll verify it still compiles or update the call sites if renamed.

## Verification

1. Build the module: `lake build GIT.ReynoldsOperator`.
2. Build dependents: `lake build GIT.GitMain` to confirm no downstream breakage.
3. Inspect file: every theorem body fits in < 15 lines (`awk` / manual count by `theorem ... by` blocks).
4. Re-run `lake env lean --run` style sanity checks if available; otherwise rely on `lake build` succeeding with no `sorry`, no warnings, no `linter` issues.
