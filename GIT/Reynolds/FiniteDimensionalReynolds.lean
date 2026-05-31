import GIT.Reynolds.LinearReductivity

/-!
# Reynolds projection: finite-dimensional case

For a linearly reductive group `G` and a finite-dimensional `Rep k G` `M`, this file proves:

* `IsLinearlyReductive.exists_reynolds` — existence of a `Rep`-morphism projection onto
  `M.ρ.invariants`.
* `IsLinearlyReductive.reynolds_natural` — naturality of the projection along any morphism
  `I : M₁ ⟶ M₂`.
* `IsLinearlyReductive.reynolds_unique` — uniqueness (corollary of naturality at `𝟙 M`).

The construction goes via a `G`-stable complement to the invariants
(`exists_isCompl_invariants`) and the projection along it (`Representation.reynoldsOfIsCompl`).
Naturality is proved by an inner argument: the "L-subrepresentation" of `ker P₁` whose elements
`x` satisfy `P₂(I x) = 0` is shown to be all of `ker P₁` via a cocycle / complement argument.
-/

universe u

open Monoid MonoidAlgebra Representation

/-- **A `G`-stable complement to the invariants exists.** For a finite-dimensional representation
`M` of a linearly reductive group, the invariants admit a `G`-stable submodule complement.

Math statement: `∃ W : Subrepresentation M.ρ, IsCompl M.ρ.invariants W.toSubmodule`.

Proof idea: linear reductivity gives semisimplicity of `M.ρ`; the invariants packaged as a
`Subrepresentation` (`invariantsSubrepresentation`) therefore admit a `Subrepresentation`
complement `W`, and `Subrepresentation.toSubmodule_isCompl` transfers the complementarity to the
underlying submodules. -/
lemma IsLinearlyReductive.exists_isCompl_invariants
    {k : Type u} [Field k] {G : Type u} [Group G]
    (hlr : IsLinearlyReductive k G) (M : Rep k G) [FiniteDimensional k M] :
    ∃ W : Subrepresentation M.ρ, IsCompl M.ρ.invariants W.toSubmodule := by
  obtain ⟨W, hW⟩ := (hlr.isSemisimple M).exists_isCompl M.ρ.invariantsSubrepresentation
  exact ⟨W, Subrepresentation.toSubmodule_isCompl hW⟩

/-- **Reynolds projection from a complement.** Given `hc : IsCompl ρ.invariants W`, the linear
map projecting onto `ρ.invariants` along `W`.

Math: `v = vi + vw ↦ vi`, where `vi ∈ ρ.invariants`, `vw ∈ W` are the unique direct-sum
components of `v`. -/
noncomputable def Representation.reynoldsOfIsCompl
    {k : Type u} [Field k] {G : Type u} [Group G]
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    {W : Submodule k V} (hc : IsCompl ρ.invariants W) : V →ₗ[k] V :=
  ρ.invariants.subtype ∘ₗ ρ.invariants.linearProjOfIsCompl W hc

/-- **`reynoldsOfIsCompl` is a projection onto `ρ.invariants`.**

Math statement: `LinearMap.IsProj ρ.invariants (ρ.reynoldsOfIsCompl hc)`.

Proof idea: `map_mem` is immediate from the `Submodule.subtype` factor; `map_id` on
`vi ∈ ρ.invariants` follows from `Submodule.linearProjOfIsCompl_apply_left`. -/
lemma Representation.isProj_reynoldsOfIsCompl
    {k : Type u} [Field k] {G : Type u} [Group G]
    {V : Type*} [AddCommGroup V] [Module k V] {ρ : Representation k G V}
    {W : Submodule k V} (hc : IsCompl ρ.invariants W) :
    LinearMap.IsProj ρ.invariants (ρ.reynoldsOfIsCompl hc) :=
  ⟨fun x => (ρ.invariants.linearProjOfIsCompl W hc x).property,
   fun x hx => by
     have := Submodule.linearProjOfIsCompl_apply_left hc ⟨x, hx⟩
     simp [Representation.reynoldsOfIsCompl, this]⟩

/-- **`reynoldsOfIsCompl` vanishes on the complement.** On `vw ∈ W`, the projection along `W`
returns zero. Direct from `Submodule.linearProjOfIsCompl_apply_right'`. -/
lemma Representation.reynoldsOfIsCompl_apply_of_mem
    {k : Type u} [Field k] {G : Type u} [Group G]
    {V : Type*} [AddCommGroup V] [Module k V] {ρ : Representation k G V}
    {W : Submodule k V} (hc : IsCompl ρ.invariants W) {v : V} (hv : v ∈ W) :
    ρ.reynoldsOfIsCompl hc v = 0 := by
  simp [Representation.reynoldsOfIsCompl, Submodule.linearProjOfIsCompl_apply_right' hc v hv]

/-- **`reynoldsOfIsCompl` is constant on `G`-orbits when `W` is `G`-stable.**

Math statement: if every `ρ g` maps `W` into `W`, then `π(ρ g v) = π v`.

Proof idea: decompose `v = vi + vw` with `vi ∈ ρ.invariants`, `vw ∈ W`. Then `ρ g vi = vi`
(invariance) and `ρ g vw ∈ W` (stability); the first summand contributes `π vi` on both sides
and the second contributes `0` by `reynoldsOfIsCompl_apply_of_mem`. -/
lemma Representation.reynoldsOfIsCompl_apply_rho
    {k : Type u} [Field k] {G : Type u} [Group G]
    {V : Type*} [AddCommGroup V] [Module k V] {ρ : Representation k G V}
    {W : Submodule k V} (hc : IsCompl ρ.invariants W)
    (hWst : ∀ g, W ≤ W.comap (ρ g)) (g : G) (v : V) :
    ρ.reynoldsOfIsCompl hc (ρ g v) = ρ.reynoldsOfIsCompl hc v := by
  obtain ⟨vi, hvi, vw, hvw, rfl⟩ :=
    Submodule.mem_sup.mp (show v ∈ ρ.invariants ⊔ W from hc.sup_eq_top ▸ Submodule.mem_top)
  have hvi_inv : ρ g vi = vi := (ρ.mem_invariants vi).mp hvi g
  simp [map_add, hvi_inv,
    Representation.reynoldsOfIsCompl_apply_of_mem hc (hWst g hvw),
    Representation.reynoldsOfIsCompl_apply_of_mem hc hvw]

/-- **Existence of the Reynolds projection (finite-dimensional case).** For a finite-dimensional
representation `M` of a linearly reductive group, there is a `Rep`-morphism `π : M ⟶ M` whose
underlying linear map is a projection onto `M.ρ.invariants`.

Math statement: `∃ π : M ⟶ M, LinearMap.IsProj M.ρ.invariants π.hom.hom`.

Proof idea: pick a `G`-stable complement `W` to `M.ρ.invariants` via
`exists_isCompl_invariants`, build the projection `π := reynoldsOfIsCompl hc`. It projects onto
invariants (`isProj_reynoldsOfIsCompl`); equivariance comes from
`reynoldsOfIsCompl_apply_rho` plus the fact that `π v` is already invariant so `ρ g` fixes it.
The pair `(πlin, equivariance)` assembles into a `Rep` morphism via `Rep.mkHom`. -/
theorem IsLinearlyReductive.exists_reynolds
    {k : Type u} [Field k] {G : Type u} [Group G]
    (hlr : IsLinearlyReductive k G) (M : Rep k G) [FiniteDimensional k M] :
    ∃ π : M ⟶ M, LinearMap.IsProj M.ρ.invariants π.hom.hom := by
  obtain ⟨W, hc⟩ := hlr.exists_isCompl_invariants M
  have hWst : ∀ g, W.toSubmodule ≤ W.toSubmodule.comap (M.ρ g) :=
    fun g _ hx => W.apply_mem_toSubmodule g hx
  have hproj := Representation.isProj_reynoldsOfIsCompl hc
  refine ⟨Rep.mkHom (M.ρ.reynoldsOfIsCompl hc) fun g v => ?_, hproj⟩
  rw [Representation.reynoldsOfIsCompl_apply_rho hc hWst g v,
    ((M.ρ.mem_invariants _).mp (hproj.map_mem v)) g]

/-- **The kernel of a projection onto invariants is `G`-stable.**

Math statement: for `P : M ⟶ M` a `Rep`-morphism whose underlying linear map is a projection
onto `M.ρ.invariants`, we have `∀ g, ker P.hom.hom ≤ (ker P.hom.hom).comap (M.ρ g)`.

Proof idea: from `Rep.isProj_invariants_apply_rho`, `P (ρ g v) = P v`; thus if `P v = 0` then
`P (ρ g v) = 0` as well. -/
lemma Rep.ker_isProj_stable {k : Type u} [Field k] {G : Type u} [Group G] {M : Rep k G}
    {P : M ⟶ M} (h : LinearMap.IsProj M.ρ.invariants P.hom.hom) :
    ∀ g, LinearMap.ker P.hom.hom ≤ (LinearMap.ker P.hom.hom).comap (M.ρ g) := by
  intro g x hx
  simp only [Submodule.mem_comap, LinearMap.mem_ker] at hx ⊢
  rw [Rep.isProj_invariants_apply_rho h, hx]

/-- **`Rep`-morphisms preserve invariants.** If `I : M₁ ⟶ M₂` and `v ∈ M₁.ρ.invariants`, then
`I.hom.hom v ∈ M₂.ρ.invariants`.

Proof idea: `M₂.ρ g (I v) = I (M₁.ρ g v) = I v` by equivariance of `I` and `M₁.ρ`-invariance
of `v`. -/
lemma Rep.hom_apply_mem_invariants {k : Type u} [Field k] {G : Type u} [Group G]
    {M₁ M₂ : Rep k G} (I : M₁ ⟶ M₂) {v : M₁} (hv : v ∈ M₁.ρ.invariants) :
    I.hom.hom v ∈ M₂.ρ.invariants := by
  rw [Representation.mem_invariants]; intro g
  rw [← Rep.hom_comm_apply I g v, (M₁.ρ.mem_invariants v).mp hv g]

/-- **The L-subrepresentation for the naturality argument.** Inside the kernel-of-`P₁` viewed as
a `Rep k G`, the subspace `L := {x | P₂(I x) = 0}`.

`G`-stability: `P₂(I(ρ g x)) = P₂(ρ g (I x)) = P₂(I x) = 0` by equivariance of `I` and
orbit-constancy of `P₂`. -/
private noncomputable def IsLinearlyReductive.reynoldsNaturalL
    {k : Type u} [Field k] {G : Type u} [Group G]
    {M₁ M₂ : Rep k G} (I : M₁ ⟶ M₂) {P₁ : M₁ ⟶ M₁} {P₂ : M₂ ⟶ M₂}
    (h₁ : LinearMap.IsProj M₁.ρ.invariants P₁.hom.hom)
    (h₂ : LinearMap.IsProj M₂.ρ.invariants P₂.hom.hom) :
    Subrepresentation (M₁.subrepresentation _ (Rep.ker_isProj_stable h₁)).ρ where
  toSubmodule :=
    (LinearMap.ker (P₂.hom.hom ∘ₗ I.hom.hom)).comap (LinearMap.ker P₁.hom.hom).subtype
  apply_mem_toSubmodule g x hx := by
    simp only [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.comp_apply] at hx ⊢
    change P₂.hom.hom (I.hom.hom (M₁.ρ g (x : M₁))) = 0
    rw [Rep.hom_comm_apply I, Rep.isProj_invariants_apply_rho h₂]; exact hx

/-- **Coboundaries lie in `reynoldsNaturalL`.** For every `x ∈ ker P₁` and every `g : G`, the
difference `ρ g x - x` (taken in the kernel-subrepresentation) belongs to `reynoldsNaturalL`.

Proof: `P₂(I(ρ g x - x)) = P₂(ρ g (I x)) - P₂(I x) = P₂(I x) - P₂(I x) = 0`, using equivariance
of `I` and orbit-constancy of `P₂`. -/
private lemma IsLinearlyReductive.cocycle_mem_reynoldsNaturalL
    {k : Type u} [Field k] {G : Type u} [Group G]
    {M₁ M₂ : Rep k G} (I : M₁ ⟶ M₂) {P₁ : M₁ ⟶ M₁} {P₂ : M₂ ⟶ M₂}
    (h₁ : LinearMap.IsProj M₁.ρ.invariants P₁.hom.hom)
    (h₂ : LinearMap.IsProj M₂.ρ.invariants P₂.hom.hom)
    (g : G) (x : ↥(LinearMap.ker P₁.hom.hom)) :
    ((M₁.subrepresentation _ (Rep.ker_isProj_stable h₁)).ρ g x - x)
      ∈ (IsLinearlyReductive.reynoldsNaturalL I h₁ h₂).toSubmodule := by
  simp only [IsLinearlyReductive.reynoldsNaturalL, Submodule.mem_comap, LinearMap.mem_ker,
    LinearMap.comp_apply]
  change P₂.hom.hom (I.hom.hom (M₁.ρ g (x : M₁) - (x : M₁))) = 0
  simp [map_sub, Rep.hom_comm_apply I, Rep.isProj_invariants_apply_rho h₂]

/-- **Complements of `reynoldsNaturalL` are trivial.** If `T` is a complementary
subrepresentation of `reynoldsNaturalL` inside the kernel-`Rep`, then `T = ⊥`.

Proof: take `t ∈ T`. The cocycle `ρ g t - t` lies in `reynoldsNaturalL` (by
`cocycle_mem_reynoldsNaturalL`) and in `T` (by `G`-stability of `T`), hence in `L ⊓ T = ⊥`;
so `ρ g t = t` for all `g`, i.e. `t ∈ M₁.ρ.invariants`. But `t ∈ ker P₁ ⊓ invariants = ⊥` by
`h₁.isCompl`, forcing `t = 0`. -/
private lemma IsLinearlyReductive.reynoldsNaturalT_eq_bot
    {k : Type u} [Field k] {G : Type u} [Group G]
    {M₁ M₂ : Rep k G} (I : M₁ ⟶ M₂) {P₁ : M₁ ⟶ M₁} {P₂ : M₂ ⟶ M₂}
    (h₁ : LinearMap.IsProj M₁.ρ.invariants P₁.hom.hom)
    (h₂ : LinearMap.IsProj M₂.ρ.invariants P₂.hom.hom)
    {T : Subrepresentation (M₁.subrepresentation _ (Rep.ker_isProj_stable h₁)).ρ}
    (hLT : IsCompl (IsLinearlyReductive.reynoldsNaturalL I h₁ h₂) T) : T = ⊥ := by
  rw [eq_bot_iff]; rintro ⟨t, ht_ker⟩ ht_T; apply Subtype.ext
  suffices ht_inv : t ∈ M₁.ρ.invariants by
    have hmem : t ∈ M₁.ρ.invariants ⊓ LinearMap.ker P₁.hom.hom := ⟨ht_inv, ht_ker⟩
    rw [h₁.isCompl.disjoint.eq_bot] at hmem; exact (Submodule.mem_bot k).mp hmem
  rw [Representation.mem_invariants]; intro g
  have hL := IsLinearlyReductive.cocycle_mem_reynoldsNaturalL I h₁ h₂ g ⟨t, ht_ker⟩
  have hT := T.toSubmodule.sub_mem (T.apply_mem_toSubmodule g ht_T) ht_T
  have hbot : _ ∈ (IsLinearlyReductive.reynoldsNaturalL I h₁ h₂).toSubmodule ⊓ T.toSubmodule :=
    ⟨hL, hT⟩
  rw [← Subrepresentation.toSubmodule_inf, hLT.disjoint.eq_bot] at hbot
  exact congr_arg Subtype.val (sub_eq_zero.mp ((Submodule.mem_bot k).mp hbot))

/-- **`reynoldsNaturalL` fills the whole kernel.** Under linear reductivity, the underlying
submodule of `reynoldsNaturalL` equals `⊤` (the full `ker P₁`).

Proof: `IsSemisimpleRepresentation.exists_isCompl` yields a complement `T` of `L`; by
`reynoldsNaturalT_eq_bot`, `T = ⊥`, so `L ⊔ T = L = ⊤`. -/
private lemma IsLinearlyReductive.reynoldsNaturalL_eq_top
    {k : Type u} [Field k] {G : Type u} [Group G]
    (hlr : IsLinearlyReductive k G)
    {M₁ M₂ : Rep k G} [FiniteDimensional k M₁]
    (I : M₁ ⟶ M₂) {P₁ : M₁ ⟶ M₁} {P₂ : M₂ ⟶ M₂}
    (h₁ : LinearMap.IsProj M₁.ρ.invariants P₁.hom.hom)
    (h₂ : LinearMap.IsProj M₂.ρ.invariants P₂.hom.hom) :
    (IsLinearlyReductive.reynoldsNaturalL I h₁ h₂).toSubmodule = ⊤ := by
  haveI : FiniteDimensional k (LinearMap.ker P₁.hom.hom) :=
    Submodule.finiteDimensional_of_le le_top
  set M_W := M₁.subrepresentation _ (Rep.ker_isProj_stable h₁) with hMW
  haveI : FiniteDimensional k M_W := inferInstanceAs (FiniteDimensional k _)
  obtain ⟨T, hLT⟩ :=
    (hlr.isSemisimple M_W).exists_isCompl (IsLinearlyReductive.reynoldsNaturalL I h₁ h₂)
  have hT := IsLinearlyReductive.reynoldsNaturalT_eq_bot I h₁ h₂ hLT
  have h := hLT.sup_eq_top (α := Subrepresentation M_W.ρ)
  rw [hT, sup_bot_eq] at h
  exact congr_arg Subrepresentation.toSubmodule h

/-- **Naturality of the Reynolds projection.** Let `P₁ : M₁ ⟶ M₁` and `P₂ : M₂ ⟶ M₂` be
`Rep`-morphism projections onto the invariants, and `I : M₁ ⟶ M₂` any `Rep`-morphism. Then
`I ∘ P₁ = P₂ ∘ I` pointwise.

Math statement: `∀ v, I.hom.hom (P₁.hom.hom v) = P₂.hom.hom (I.hom.hom v)`.

Proof idea: decompose `v = P₁ v + w` with `w := v - P₁ v ∈ ker P₁`. On the invariant summand
`I (P₁ v) ∈ M₂.ρ.invariants` so `P₂` fixes it (`Rep.hom_apply_mem_invariants`). On the kernel
summand, `reynoldsNaturalL_eq_top` says every `w ∈ ker P₁` satisfies `P₂ (I w) = 0`. Adding
gives the result. -/
theorem IsLinearlyReductive.reynolds_natural
    {k : Type u} [Field k] {G : Type u} [Group G]
    (hlr : IsLinearlyReductive k G)
    (M₁ M₂ : Rep k G) [FiniteDimensional k M₁] [FiniteDimensional k M₂]
    (I : M₁ ⟶ M₂) (P₁ : M₁ ⟶ M₁) (P₂ : M₂ ⟶ M₂)
    (h₁ : LinearMap.IsProj M₁.ρ.invariants P₁.hom.hom)
    (h₂ : LinearMap.IsProj M₂.ρ.invariants P₂.hom.hom) :
    ∀ v : M₁, I.hom.hom (P₁.hom.hom v) = P₂.hom.hom (I.hom.hom v) := fun v => by
  have hw_ker : v - P₁.hom.hom v ∈ LinearMap.ker P₁.hom.hom := by
    rw [LinearMap.mem_ker]; simp [h₁.map_id (P₁.hom.hom v) (h₁.map_mem v)]
  have hwL : (⟨v - P₁.hom.hom v, hw_ker⟩ : ↥(LinearMap.ker P₁.hom.hom)) ∈
      (IsLinearlyReductive.reynoldsNaturalL I h₁ h₂).toSubmodule :=
    IsLinearlyReductive.reynoldsNaturalL_eq_top hlr I h₁ h₂ ▸ Submodule.mem_top
  have hvanish : P₂.hom.hom (I.hom.hom (v - P₁.hom.hom v)) = 0 := by
    simpa [IsLinearlyReductive.reynoldsNaturalL, Submodule.mem_comap, LinearMap.mem_ker] using hwL
  have hinv : I.hom.hom (P₁.hom.hom v) ∈ M₂.ρ.invariants :=
    Rep.hom_apply_mem_invariants I (h₁.map_mem v)
  rw [show I.hom.hom v = I.hom.hom (P₁.hom.hom v) + I.hom.hom (v - P₁.hom.hom v) by
        simp [map_sub, add_sub_cancel], map_add, h₂.map_id _ hinv, hvanish, add_zero]

/-- **Uniqueness of the Reynolds projection (finite-dimensional case).** Any two `Rep`-morphism
projections onto `ρ.invariants` of a finite-dimensional representation coincide.

Math statement: `π₁ = π₂` whenever both are `Rep`-morphism projections onto `M.ρ.invariants`.

Proof idea: invoke `reynolds_natural` with the identity intertwiner `𝟙 M : M ⟶ M`; its
underlying linear map is the identity, so `π₁ v = π₂ v` pointwise. Then promote pointwise
equality to equality of `Rep`-morphisms via `Action.hom_ext` and `ModuleCat.hom_ext`. -/
theorem IsLinearlyReductive.reynolds_unique
    {k : Type u} [Field k] {G : Type u} [Group G]
    (hlr : IsLinearlyReductive k G)
    (M : Rep k G) [FiniteDimensional k M]
    (π₁ π₂ : M ⟶ M)
    (h₁ : LinearMap.IsProj M.ρ.invariants π₁.hom.hom)
    (h₂ : LinearMap.IsProj M.ρ.invariants π₂.hom.hom) :
    π₁ = π₂ := by
  have h := IsLinearlyReductive.reynolds_natural hlr M M
    (CategoryTheory.CategoryStruct.id M) π₁ π₂ h₁ h₂
  apply Action.hom_ext; apply ModuleCat.hom_ext; ext v
  simpa using h v
