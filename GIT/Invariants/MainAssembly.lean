import GIT.Invariants.ReynoldsIdeal
import GIT.ReynoldsOperator

/-!
# Assembly helpers for `GIT_finiteType_invariants`

Bridge file collecting the setup work that the main Hilbert finiteness proof needs in addition
to the three section files (`InheritedGrading`, `GradedFiniteType`, `ReynoldsIdeal`):

* `GIT.extendedRGplus_le_irrelevant` — the extension `R · (R^G)₊ ≤ R₊`.
* `GIT.RGplusA_eq_comap` — `(R^G)₊` is the preimage of the extension under `R^G ↪ R`.
* `GIT.ReynoldsLin` — bundle of `(ρ_lin : R →ₗ[k] R^G, hρ_id, hρ_mul)` derived from
  `IsLinearlyReductive + IsLocallyFinite`.
* `GIT.ReynoldsLin.of_isLocallyFinite` — builder via
  `exists_reynolds_mulCompat_of_isLocallyFinite`.
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

/-- **The extended ideal lies in the ambient irrelevant ideal.**

Math statement: `Ideal.map ((R^G).val) (irrelevant 𝒜G) ≤ (irrelevant 𝒜).toIdeal`, assuming the
inclusion `(R^G) ↪ R` is grading-preserving.

Proof idea: by `Ideal.map_le_iff_le_comap`, suffices that the image of each `a ∈ irrelevant 𝒜G`
lies in `irrelevant 𝒜`. The degree-`0` part of `a` is `0` in `R^G`; pushed through the
inclusion via `AlgHom.map_decompose_zero` it stays `0` in `R`. -/
lemma extendedRGplus_le_irrelevant
    (h𝒜G : ∀ (d : ℕ) (a : FixedSubalgebra k G R),
      a ∈ 𝒜G d → (a : R) ∈ 𝒜 d) :
    Ideal.map ((FixedSubalgebra k G R).val : _ →+* R)
        ((HomogeneousIdeal.irrelevant 𝒜G).toIdeal) ≤
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
  refine Ideal.map_le_iff_le_comap.mpr ?_
  intro a ha
  have h0A : ((DirectSum.decompose 𝒜G a) 0 : FixedSubalgebra k G R) = 0 := by
    have hp := (HomogeneousIdeal.mem_irrelevant_iff (𝒜 := 𝒜G) a).mp ha
    simpa [GradedRing.proj_apply] using hp
  change (FixedSubalgebra k G R).val a ∈ HomogeneousIdeal.irrelevant 𝒜
  rw [HomogeneousIdeal.mem_irrelevant_iff]
  have hcompat := AlgHom.map_decompose_zero (k := k) (FixedSubalgebra k G R).val 𝒜G 𝒜 h𝒜G a
  rw [h0A] at hcompat
  simp only [ZeroMemClass.coe_zero] at hcompat
  simpa [GradedRing.proj_apply] using hcompat.symm

/-- **`(R^G)₊` is the comap of `extendedRGplus`.**

Math statement: `(HomogeneousIdeal.irrelevant 𝒜G).toIdeal =
  Ideal.comap (FixedSubalgebra k G R).val (Ideal.map (FixedSubalgebra k G R).val
    (HomogeneousIdeal.irrelevant 𝒜G).toIdeal)`.

Proof idea: `≤` is `Ideal.le_comap_map`. For `≥`, an `x ∈ comap` has `(R^G).val x` with
vanishing degree-`0` part (from `extendedRGplus_le_irrelevant`); by `AlgHom.map_decompose_zero`
and injectivity of the inclusion (`Subtype.val_injective`), the degree-`0` part of `x` itself
vanishes, so `x ∈ irrelevant 𝒜G`. -/
lemma RGplusA_eq_comap
    (h𝒜G : ∀ (d : ℕ) (a : FixedSubalgebra k G R),
      a ∈ 𝒜G d → (a : R) ∈ 𝒜 d) :
    (HomogeneousIdeal.irrelevant 𝒜G).toIdeal =
      Ideal.comap ((FixedSubalgebra k G R).val : _ →+* R)
        (Ideal.map ((FixedSubalgebra k G R).val : _ →+* R)
          (HomogeneousIdeal.irrelevant 𝒜G).toIdeal) := by
  apply le_antisymm Ideal.le_comap_map
  intro x hx
  have htoR_x : (FixedSubalgebra k G R).val x ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal :=
    extendedRGplus_le_irrelevant (𝒜 := 𝒜) (𝒜G := 𝒜G) h𝒜G hx
  have h0R : ((DirectSum.decompose 𝒜 ((FixedSubalgebra k G R).val x)) 0 : R) = 0 := by
    have hp := (HomogeneousIdeal.mem_irrelevant_iff (𝒜 := 𝒜) _).mp htoR_x
    simpa [GradedRing.proj_apply] using hp
  have hRA0 : (((DirectSum.decompose 𝒜G x) 0 : FixedSubalgebra k G R) : R) = 0 := by
    show (FixedSubalgebra k G R).val
      (((DirectSum.decompose 𝒜G x) 0 : FixedSubalgebra k G R)) = 0
    rw [AlgHom.map_decompose_zero (k := k) (FixedSubalgebra k G R).val 𝒜G 𝒜 h𝒜G x]; exact h0R
  have h0A : ((DirectSum.decompose 𝒜G x) 0 : FixedSubalgebra k G R) = 0 := Subtype.ext hRA0
  change x ∈ HomogeneousIdeal.irrelevant 𝒜G
  rw [HomogeneousIdeal.mem_irrelevant_iff]
  simpa [GradedRing.proj_apply] using h0A

/-- **Finite generators of the extended ideal `R · (R^G)₊`.**

Math statement: there is a finset `s ⊆ R` whose elements all come from the inclusion
`R^G ↪ R` of an element of `(R^G)₊`, and whose ideal-span equals `Ideal.map (R^G).val (R^G)₊`.

Proof idea: combine `extendedRGplus_fg` (Noether) with
`exists_generators_extendedRGplus_from_RGplus`. -/
lemma exists_generators_of_irrelevant [IsNoetherianRing R] :
    ∃ s : Finset R,
      (∀ x ∈ s, x ∈ ((FixedSubalgebra k G R).val : FixedSubalgebra k G R → R) ''
        ((HomogeneousIdeal.irrelevant 𝒜G).toIdeal : Set (FixedSubalgebra k G R))) ∧
      Ideal.span (↑s : Set R) =
        Ideal.map ((FixedSubalgebra k G R).val : _ →+* R)
          (HomogeneousIdeal.irrelevant 𝒜G).toIdeal := by
  refine exists_generators_extendedRGplus_from_RGplus ?_ (extendedRGplus_fg _)
  change Ideal.span (((FixedSubalgebra k G R).val : FixedSubalgebra k G R → R) ''
      ((HomogeneousIdeal.irrelevant 𝒜G).toIdeal : Set (FixedSubalgebra k G R))) =
    Ideal.map ((FixedSubalgebra k G R).val : _ →+* R)
      (HomogeneousIdeal.irrelevant 𝒜G).toIdeal
  rfl

/-- **Bundle of Reynolds-projection data** valued in `R^G`: a `k`-linear map `ρ : R → R^G`
together with the two identities used in the GIT proof — `ρ ∘ ((R^G).val) = id` on `R^G` and
`ρ ((R^G).val a · r) = a · ρ r` for `a ∈ R^G`, `r ∈ R`. -/
structure ReynoldsLin
    (k : Type u) [Field k] (G : Type u) [Group G]
    (R : Type u) [CommRing R] [Algebra k R]
    [MulSemiringAction G R] [SMulCommClass G k R] where
  ρ : R →ₗ[k] FixedSubalgebra k G R
  id : ∀ a : FixedSubalgebra k G R, ρ ((FixedSubalgebra k G R).val a) = a
  mul : ∀ (a : FixedSubalgebra k G R) (r : R),
    ρ ((FixedSubalgebra k G R).val a * r) = a * ρ r

/-- **Build the Reynolds bundle** from `IsLinearlyReductive + IsLocallyFinite`.

Proof idea: invoke `exists_reynolds_mulCompat_of_isLocallyFinite` to get
`π : Rep.of σ ⟶ Rep.of σ` that projects onto `σ.invariants` and is multiplicative against
invariants. Since `σ.invariants` and `R^G` share the carrier `{r | ∀ g, g • r = r}`, the
underlying `π_lin : R →ₗ[k] R` co-restricts to `R^G` via `LinearMap.codRestrict`. -/
noncomputable def ReynoldsLin.of_isLocallyFinite
    (hlr : IsLinearlyReductive k G)
    (hlf : Representation.IsLocallyFinite k G R) : ReynoldsLin k G R := by
  classical
  let h := IsLinearlyReductive.exists_reynolds_mulCompat_of_isLocallyFinite hlr R hlf
  let π' := h.choose
  obtain ⟨hπ'_proj, hπ'_mul⟩ := h.choose_spec
  have hA_inv : ∀ {a : FixedSubalgebra k G R},
      (a : R) ∈ (Representation.ofDistribMulAction k G R).invariants :=
    fun {a} => (Representation.mem_invariants _ _).mpr a.property
  have hπ'_to_A : ∀ r : R, π'.hom.hom r ∈ (FixedSubalgebra k G R).toSubmodule := fun r g =>
    ((Representation.ofDistribMulAction k G R).mem_invariants _).mp (hπ'_proj.map_mem r) g
  refine ⟨LinearMap.codRestrict (FixedSubalgebra k G R).toSubmodule π'.hom.hom hπ'_to_A,
    fun a => Subtype.ext (hπ'_proj.map_id (a : R) hA_inv),
    fun a r => Subtype.ext (hπ'_mul hA_inv r)⟩

end GIT
