import GIT.Invariants.MainAssembly

/-!
# Hilbert finiteness theorem for invariants of a linearly reductive group

This umbrella file states and proves the main result:

* `GIT.GIT_finiteType_invariants` — `R^G` is finitely generated as a `k`-algebra, given that
  `R` is a finitely generated graded `k`-algebra, the action of `G` is locally finite,
  grading-preserving, and `G` is linearly reductive (with `𝒜G 0` itself f.g. over `k`).

All auxiliary content (inherited grading, finite generation from the irrelevant ideal, Reynolds
ideal machinery, main-theorem assembly helpers) lives in `GIT/Invariants/`. See
[`git_abbrev.md`](../git_abbrev.md) for the file dependency graph and proof-chain index.
-/

open Algebra HomogeneousIdeal

universe u

namespace GIT

variable {k : Type u} [Field k]
variable {G : Type u} [Group G]
variable {R : Type u} [CommRing R] [Algebra k R]
variable [MulSemiringAction G R] [SMulCommClass G k R]
variable {𝒜 : ℕ → Submodule k R} [GradedAlgebra 𝒜]
variable {𝒜G : ℕ → Submodule k (FixedSubalgebra k G R)} [GradedAlgebra 𝒜G]

/-- **GIT.** Let `G` be a linearly reductive group over a field `k`
acting on a finitely generated graded `k`-algebra `R` by grading-preserving `k`-algebra
automorphisms with the action locally finite. Then the invariant subalgebra `R^G` is finitely
generated as a `k`-algebra.

Math statement: `Algebra.FiniteType k (FixedSubalgebra k G R)`.

Proof idea: by `fixedSubalgebra_finiteType` it suffices that `(R^G)₊` is finitely generated as
an ideal of `R^G`. `R` is Noetherian (Hilbert basis), so `exists_generators_of_irrelevant` picks
finitely many generators of the extension `R · (R^G)₊` inside `R^G`. Lift these along the
inclusion, pull back via the multiplicative Reynolds projection
(`ReynoldsLin.of_isLocallyFinite`), and combine via `RGplusA_fg_of_reynolds` and
`reynoldsGITSpanProperty_of_reynolds`. -/
theorem GIT_finiteType_invariants
    [FiniteType k R] [FiniteType k (𝒜G 0)]
    (hlr : IsLinearlyReductive k G)
    (hlf : Representation.IsLocallyFinite k G R)
    (h𝒜G : ∀ (d : ℕ) (a : FixedSubalgebra k G R),
      a ∈ 𝒜G d → (a : R) ∈ 𝒜 d) :
    FiniteType k (FixedSubalgebra k G R) := by
  classical
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  refine fixedSubalgebra_finiteType 𝒜G ?_
  obtain ⟨s, hs_sub, hs_span⟩ := GIT.exists_generators_of_irrelevant (𝒜G := 𝒜G)
  choose lift hlift_mem hlift_eq using hs_sub
  let liftFn : R → FixedSubalgebra k G R := fun x => if hx : x ∈ s then lift x hx else 0
  have hlift_fn : ∀ x ∈ s, (FixedSubalgebra k G R).val (liftFn x) = x :=
    fun x hx => by simp only [liftFn, dif_pos hx]; exact hlift_eq x hx
  let ρ := ReynoldsLin.of_isLocallyFinite hlr hlf
  refine RGplusA_fg_of_reynolds hs_span (RGplusA_eq_comap h𝒜G)
    (fun x hx => by rw [← hlift_eq x hx, ρ.id]; exact hlift_mem x hx)
    (reynoldsGITSpanProperty_of_reynolds _ ρ.ρ s liftFn hlift_fn ρ.id ρ.mul)

end GIT
