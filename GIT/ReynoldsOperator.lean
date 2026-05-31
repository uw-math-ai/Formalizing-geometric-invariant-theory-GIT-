import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Rep
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Semisimple

/-!
# The Reynolds operator for linearly reductive groups

This file constructs the *Reynolds operator* — a canonical `G`-equivariant projection onto the
invariants — for a linearly reductive group `G`, first for finite-dimensional representations and
then, via local finiteness, for arbitrary `k`-modules and `k`-algebras.

## Main definitions

* `Representation.IsLocallyFinite`: an action is locally finite if every element lies in a
  finite-dimensional `G`-stable submodule.
* `IsLinearlyReductive`: every finite-dimensional representation of `G` is semisimple.
* `Representation.invariantsSubrepresentation`: the invariants packaged as a `Subrepresentation`.

## Main results

* `IsLinearlyReductive.exists_reynolds`: existence of the Reynolds projection on a
  finite-dimensional representation.
* `IsLinearlyReductive.reynolds_natural`: the projection is natural in the representation.
* `IsLinearlyReductive.reynolds_unique`: it is unique (a corollary of naturality).
* `exists_reynolds_of_isLocallyFinite`, `IsLinearlyReductive.reynolds_unique_of_isLocallyFinite`:
  existence and uniqueness for locally finite actions.
* `exists_reynolds_mul_compat_of_locallyFinite`: on a `k`-algebra the Reynolds projection is
  `R^G`-linear.

## Sections

* A. Locally finite actions
* B. Linear reductivity
* C. Reynolds projection: finite-dimensional case
* D. Reynolds projection: locally finite case
* E. Reynolds projection on algebras
-/

universe u

variable {k : Type u} [Field k] (G : Type u) [Group G]

open Monoid MonoidAlgebra Representation

/-- Build a morphism of representations from a `G`-equivariant linear map, packaging the
boilerplate `{ hom := ModuleCat.ofHom f, comm := … }`. -/
def Rep.mkHom {k : Type u} [Field k] {G : Type u} [Group G] {M N : Rep k G} (f : M →ₗ[k] N)
    (hf : ∀ (g : G) (v : M), f (M.ρ g v) = N.ρ g (f v)) : M ⟶ N where
  hom := ModuleCat.ofHom f
  comm g := ModuleCat.hom_ext <| LinearMap.ext fun v => hf g v

@[simp] lemma Rep.mkHom_hom {k : Type u} [Field k] {G : Type u} [Group G] {M N : Rep k G}
    (f : M →ₗ[k] N) (hf : ∀ (g : G) (v : M), f (M.ρ g v) = N.ρ g (f v)) :
    (Rep.mkHom f hf).hom.hom = f := rfl

/-- A representation endomorphism whose underlying map projects onto the invariants is constant
on `G`-orbits: `P (ρ g v) = P v`. Indeed `P (ρ g v) = ρ g (P v)` by equivariance, and `ρ g` fixes
`P v ∈ invariants`. -/
lemma Rep.isProj_invariants_apply_rho {k : Type u} [Field k] {G : Type u} [Group G] {M : Rep k G}
    {P : M ⟶ M} (h : LinearMap.IsProj M.ρ.invariants P.hom.hom) (g : G) (v : M) :
    P.hom.hom (M.ρ g v) = P.hom.hom v := by
  rw [Rep.hom_comm_apply P g v]
  exact ((M.ρ.mem_invariants _).mp (h.map_mem v)) g

/-! ## A. Locally finite actions -/

section LocallyFinite

variable {k : Type*} [CommSemiring k] {G : Type*} [Monoid G]
    {R : Type*} [AddCommMonoid R] [Module k R] [DistribMulAction G R]

/-- A `DistribMulAction` of `G` on a `k`-module `R` is *locally finite* if every element `r : R`
is contained in a finite-dimensional `G`-stable `k`-submodule `V ≤ R`. -/
def Representation.IsLocallyFinite (k : Type*) [CommSemiring k] (G : Type*) [Monoid G]
    (R : Type*) [AddCommMonoid R] [Module k R] [DistribMulAction G R] : Prop :=
  ∀ r : R, ∃ V : Submodule k R, Module.Finite k V ∧
    (∀ (g : G) (v : V), (g • (v : R)) ∈ V) ∧ r ∈ V

/-- **`G`-stability of the `k`-span of an orbit.** The submodule `Submodule.span k (G • r)` is
sent into itself by `g • _`, for every `g : G`.

Math statement: `v ∈ span_k (G • r) ⟹ g • v ∈ span_k (G • r)`.

Proof idea: by `Submodule.span_induction`. The generators `g' • r` are sent to
`(g * g') • r`, again a generator; addition and the `k`-action commute with `g • _` via
`smul_add` and `smul_comm` (using `SMulCommClass G k R`). -/
lemma Representation.smul_mem_span_orbit [SMulCommClass G k R]
    (r : R) (g : G) {v : R}
    (hv : v ∈ Submodule.span k (Set.range fun g' : G => g' • r)) :
    g • v ∈ Submodule.span k (Set.range fun g' : G => g' • r) :=
  Submodule.span_induction
    (mem := fun _ ⟨g', hg'⟩ => hg' ▸ Submodule.subset_span ⟨g * g', mul_smul g g' r⟩)
    (zero := by simp)
    (add := fun _ _ _ _ hx hy => by rw [smul_add]; exact Submodule.add_mem _ hx hy)
    (smul := fun a _ _ hx => by rw [smul_comm]; exact Submodule.smul_mem _ a hx)
    hv

/-- **Finite monoid actions are locally finite.** For a finite monoid `G` acting on a `k`-module
`R`, every `r : R` lies in a finite-dimensional `G`-stable submodule.

Math statement: `IsLocallyFinite k G R` holds whenever `G` is finite.

Proof idea: take `V := Submodule.span k (G • r)`. It contains `r = 1 • r`, is finite-dimensional
since the orbit `G • r` is finite (so its span is f.g.), and is `G`-stable by
[[smul_mem_span_orbit]]. -/
theorem Representation.isLocallyFinite_of_finite (k : Type*) [CommSemiring k] (G : Type*)
    [Monoid G] [Finite G] (R : Type*) [AddCommMonoid R] [Module k R]
    [DistribMulAction G R] [SMulCommClass G k R] :
    Representation.IsLocallyFinite k G R := fun r =>
  ⟨Submodule.span k (Set.range fun g : G => g • r),
    Module.Finite.span_of_finite k (Set.finite_range _),
    fun g v => Representation.smul_mem_span_orbit r g v.property,
    Submodule.subset_span ⟨1, one_smul G r⟩⟩

end LocallyFinite

/-! ## B. Linear reductivity -/

section LinearReductivity

/-- **Linear reductivity.** A group `G` is *linearly reductive* over `k` if every
finite-dimensional representation of `G` over `k` is semisimple.

Math statement: every finite-dimensional `M : Rep k G` is a direct sum of irreducibles,
equivalently every subrepresentation admits a `G`-stable complement. -/
class IsLinearlyReductive (k G : Type u) [Field k] [Group G] : Prop where
  isSemisimple : ∀ (M : Rep k G) [FiniteDimensional k M], IsSemisimpleRepresentation M.ρ

/-- **Maschke's theorem.** A finite group `G` whose order is invertible in `k` is linearly
reductive over `k`.

Math statement: `[Fintype G] [Invertible (|G| : k)] ⟹ IsLinearlyReductive k G`.

Proof idea: a f.d. `M` is semisimple as a representation iff it is semisimple as a
`k[G]`-module (`isSemisimpleRepresentation_iff_isSemisimpleModule_asModule`); the latter holds
because `k[G]` is a semisimple ring when `|G|` is invertible in `k`. -/
instance IsLinearlyReductive.of_fintype (k G : Type u) [Field k] [Group G]
    [Fintype G] [Invertible (Fintype.card G : k)] :
    IsLinearlyReductive k G where
  isSemisimple M _ := by
    haveI : NeZero (Nat.card G : k) := by
      rw [Nat.card_eq_fintype_card]; exact ⟨Invertible.ne_zero (Fintype.card G : k)⟩
    exact M.ρ.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule.mpr inferInstance

/-- **Invariants as a subrepresentation.** The invariants `ρ.invariants = {v | ∀ g, ρ g v = v}`
packaged as a `Subrepresentation ρ`.

Math statement: `ρ.invariants` is a `G`-stable submodule.

Proof idea: if `v` is fixed by every `g'`, then for any single `g` we have `ρ g v = v`, which is
again fixed by every `g'`; hence the underlying submodule is closed under `ρ g`. -/
noncomputable def Representation.invariantsSubrepresentation
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V) :
    Subrepresentation ρ where
  toSubmodule := ρ.invariants
  apply_mem_toSubmodule g v hv := by
    rw [Representation.mem_invariants] at hv ⊢
    intro g'; rw [hv g, hv g']

/-- **Submodule-level `IsCompl` from a `Subrepresentation`-level `IsCompl`.** If two
subrepresentations `S, T` of `ρ` are complementary in the lattice of subrepresentations, then
their underlying submodules are complementary in the lattice of submodules.

Proof idea: `Subrepresentation.toSubmodule` preserves `⊓` and `⊔`
(`Subrepresentation.toSubmodule_inf`, `Subrepresentation.toSubmodule_sup`), so `disjoint` and
`codisjoint` transfer along it. -/
lemma Subrepresentation.toSubmodule_isCompl
    {k : Type u} [Field k] {G : Type u} [Group G] {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k G V} {S T : Subrepresentation ρ} (h : IsCompl S T) :
    IsCompl S.toSubmodule T.toSubmodule := by
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff]
    simpa [Subrepresentation.toSubmodule_inf] using
      congr_arg Subrepresentation.toSubmodule (disjoint_iff.mp h.disjoint)
  · rw [codisjoint_iff]
    simpa [Subrepresentation.toSubmodule_sup] using
      congr_arg Subrepresentation.toSubmodule (codisjoint_iff.mp h.codisjoint)

end LinearReductivity

/-! ## C. Reynolds projection: finite-dimensional case -/

section FiniteDimensionalReynolds

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

end FiniteDimensionalReynolds

/-! ## D. Reynolds projection: locally finite case -/

section LocallyFiniteReynolds

variable {k : Type u} [Field k] {G : Type u} [Group G]

/-- **The supremum of two `G`-stable submodules is `G`-stable.**

Math: if every `σ g` maps `W₁` (resp. `W₂`) into itself, then it maps `W₁ ⊔ W₂` into itself.

Proof: `sup_le` decomposes the goal `W₁ ⊔ W₂ ≤ (W₁ ⊔ W₂).comap (σ g)` into two pieces, each
followed by `Submodule.comap_mono le_sup_left` / `le_sup_right`. -/
lemma Representation.sup_le_comap_of_stable
    {V : Type*} [AddCommGroup V] [Module k V]
    {σ : Representation k G V} {W₁ W₂ : Submodule k V}
    (h₁ : ∀ g, W₁ ≤ W₁.comap (σ g)) (h₂ : ∀ g, W₂ ≤ W₂.comap (σ g)) :
    ∀ g, W₁ ⊔ W₂ ≤ (W₁ ⊔ W₂).comap (σ g) := fun g =>
  sup_le ((h₁ g).trans (Submodule.comap_mono le_sup_left))
         ((h₂ g).trans (Submodule.comap_mono le_sup_right))

/-- **Submodule inclusion as a representation morphism.** For `W₁ ≤ W₂` both `G`-stable under a
representation `ρ`, the canonical inclusion `↥W₁ → ↥W₂` lifts to a morphism between the
corresponding subrepresentations of `Rep.of ρ`.

Equivariance: both sides coerce to `ρ g v.val`. -/
noncomputable def Rep.subrepInclusion
    {V : Type u} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    {W₁ W₂ : Submodule k V} (hle : W₁ ≤ W₂)
    (h₁ : ∀ g, W₁ ≤ W₁.comap (ρ g)) (h₂ : ∀ g, W₂ ≤ W₂.comap (ρ g)) :
    (Rep.of ρ).subrepresentation W₁ h₁ ⟶ (Rep.of ρ).subrepresentation W₂ h₂ :=
  Rep.mkHom (Submodule.inclusion hle) fun g v => by
    ext; simp [Representation.subrepresentation, Submodule.inclusion]

/-- **Wrap a local linear projection as a representation morphism.** Given a `G`-stable submodule
`W` under a representation `ρ` and a linear projection `π : ↥W → ↥W` onto the invariants of
`ρ.subrepresentation W _` that is constant on `G`-orbits, package it as a `Rep`-morphism on
`(Rep.of ρ).subrepresentation W _`.

Equivariance: `π` is orbit-constant by hypothesis and its image lies in the invariants, so each
`ρ g` fixes `π v`. -/
noncomputable def Rep.wrapLocalProj
    {V : Type u} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    {W : Submodule k V} (hW : ∀ g, W ≤ W.comap (ρ g)) (π : ↥W →ₗ[k] ↥W)
    (hπ : LinearMap.IsProj (ρ.subrepresentation W hW).invariants π)
    (hπ_eq : ∀ (g : G) (v : ↥W), π ((ρ.subrepresentation W hW) g v) = π v) :
    (Rep.of ρ).subrepresentation W hW ⟶ (Rep.of ρ).subrepresentation W hW :=
  Rep.mkHom π fun g v => by
    rw [show ((Rep.of ρ).subrepresentation W hW).ρ g v = (ρ.subrepresentation W hW) g v from rfl,
      hπ_eq g v]
    exact ((((Rep.of ρ).subrepresentation W hW).ρ.mem_invariants _).mp (hπ.map_mem v) g).symm

variable {R : Type u} [AddCommGroup R] [Module k R] [DistribMulAction G R] [SMulCommClass G k R]

/-- **Local Reynolds projections agree on overlaps.** Let `W₁, W₂` be finite-dimensional
`G`-stable submodules of `R` carrying local Reynolds projections `π₁, π₂`. For `r ∈ W₁ ∩ W₂`,
the values `(π₁ ⟨r,·⟩ : R)` and `(π₂ ⟨r,·⟩ : R)` coincide.

Proof idea: form the common ambient `W := W₁ ⊔ W₂`, obtain a Reynolds projection `PW` on it via
`exists_reynolds`, and apply `reynolds_natural` to the inclusions `Wᵢ ↪ W` to get
`ιᵢ(πᵢ r) = PW(ιᵢ r)`. Since `ι₁ r = ι₂ r` inside `W`, the two right-hand sides agree, hence
so do the left-hand sides. -/
private lemma IsLinearlyReductive.local_proj_agree_on_overlap
    (hlr : IsLinearlyReductive k G)
    {W₁ W₂ : Submodule k R} [FiniteDimensional k ↥W₁] [FiniteDimensional k ↥W₂]
    (hW₁_st : ∀ g, W₁ ≤ W₁.comap (Representation.ofDistribMulAction k G R g))
    (hW₂_st : ∀ g, W₂ ≤ W₂.comap (Representation.ofDistribMulAction k G R g))
    {π₁ : ↥W₁ →ₗ[k] ↥W₁} {π₂ : ↥W₂ →ₗ[k] ↥W₂}
    (h₁ : LinearMap.IsProj
      ((Representation.ofDistribMulAction k G R).subrepresentation W₁ hW₁_st).invariants π₁)
    (h₁_eq : ∀ (g : G) (v : ↥W₁),
      π₁ (((Representation.ofDistribMulAction k G R).subrepresentation W₁ hW₁_st) g v) = π₁ v)
    (h₂ : LinearMap.IsProj
      ((Representation.ofDistribMulAction k G R).subrepresentation W₂ hW₂_st).invariants π₂)
    (h₂_eq : ∀ (g : G) (v : ↥W₂),
      π₂ (((Representation.ofDistribMulAction k G R).subrepresentation W₂ hW₂_st) g v) = π₂ v)
    {r : R} (hr₁ : r ∈ W₁) (hr₂ : r ∈ W₂) :
    W₁.subtype (π₁ ⟨r, hr₁⟩) = W₂.subtype (π₂ ⟨r, hr₂⟩) := by
  set σ := Representation.ofDistribMulAction k G R with hσ
  haveI : FiniteDimensional k ↥(W₁ ⊔ W₂) := Submodule.finiteDimensional_sup _ _
  set hSt := Representation.sup_le_comap_of_stable hW₁_st hW₂_st
  obtain ⟨PW, hπW⟩ := hlr.exists_reynolds ((Rep.of σ).subrepresentation (W₁ ⊔ W₂) hSt)
  have hn₁ := hlr.reynolds_natural _ _ (Rep.subrepInclusion σ le_sup_left hW₁_st hSt)
    (Rep.wrapLocalProj σ hW₁_st π₁ h₁ h₁_eq) PW h₁ hπW ⟨r, hr₁⟩
  have hn₂ := hlr.reynolds_natural _ _ (Rep.subrepInclusion σ le_sup_right hW₂_st hSt)
    (Rep.wrapLocalProj σ hW₂_st π₂ h₂ h₂_eq) PW h₂ hπW ⟨r, hr₂⟩
  simp only [Rep.subrepInclusion, Rep.wrapLocalProj, Rep.mkHom_hom] at hn₁ hn₂
  have hreq : (Submodule.inclusion (le_sup_left : W₁ ≤ W₁ ⊔ W₂) ⟨r, hr₁⟩ :
      ↥(W₁ ⊔ W₂)) = Submodule.inclusion le_sup_right ⟨r, hr₂⟩ := rfl
  exact congr_arg Subtype.val (hn₁.trans ((congr_arg PW.hom.hom hreq).trans hn₂.symm))

/-- (Private) **Bundle of local Reynolds data** on a locally finite action: a `G`-stable
finite-dimensional submodule `V r` around every point, together with a local Reynolds projection
`π r` on it that is orbit-constant. Produced by `LRD.of_isLocallyFinite`. -/
private structure IsLinearlyReductive.LRD
    (k : Type u) [Field k] (G : Type u) [Group G] (R : Type u)
    [AddCommGroup R] [Module k R] [DistribMulAction G R] [SMulCommClass G k R] where
  V : R → Submodule k R
  fin : ∀ r, Module.Finite k ↥(V r)
  comap : ∀ r g, V r ≤ (V r).comap (Representation.ofDistribMulAction k G R g)
  mem : ∀ r, r ∈ V r
  π : ∀ r, ↥(V r) →ₗ[k] ↥(V r)
  isProj : ∀ r, LinearMap.IsProj
    ((Representation.ofDistribMulAction k G R).subrepresentation (V r) (comap r)).invariants (π r)
  apply_rho : ∀ r g v, π r
    (((Representation.ofDistribMulAction k G R).subrepresentation (V r) (comap r)) g v) = π r v

namespace IsLinearlyReductive.LRD

variable {k : Type u} [Field k] {G : Type u} [Group G]
    {R : Type u} [AddCommGroup R] [Module k R] [DistribMulAction G R] [SMulCommClass G k R]

/-- **Local Reynolds data from local finiteness.** Pick the f.d. `G`-stable submodule `V r` from
`hlf`, then a local Reynolds projection on it via `exists_reynolds`. -/
private noncomputable def of_isLocallyFinite (hlr : IsLinearlyReductive k G)
    (hlf : Representation.IsLocallyFinite k G R) : IsLinearlyReductive.LRD k G R := by
  set σ := Representation.ofDistribMulAction k G R
  choose V hVf hVs hVm using hlf
  have hVc : ∀ r g, V r ≤ (V r).comap (σ g) := fun r g _ hv => hVs r g ⟨_, hv⟩
  haveI : ∀ r, FiniteDimensional k ↥(V r) := hVf
  have local_data : ∀ r, ∃ p : ↥(V r) →ₗ[k] ↥(V r),
      LinearMap.IsProj (σ.subrepresentation (V r) (hVc r)).invariants p ∧
      ∀ g v, p ((σ.subrepresentation (V r) (hVc r)) g v) = p v := fun r => by
    obtain ⟨P, hP⟩ := hlr.exists_reynolds ((Rep.of σ).subrepresentation (V r) (hVc r))
    exact ⟨P.hom.hom, hP, Rep.isProj_invariants_apply_rho hP⟩
  choose π hπp hπe using local_data
  exact ⟨V, hVf, hVc, hVm, π, hπp, hπe⟩

/-- **The global Reynolds function** `f : R → R`, defined by `r ↦ (π r) ⟨r, _⟩` interpreted in
`R` via the inclusion `V r ↪ R`. -/
private noncomputable def f (D : IsLinearlyReductive.LRD k G R) : R → R :=
  fun r => (D.V r).subtype (D.π r ⟨r, D.mem r⟩)

/-- **`D.f r` equals any other local projection at `r`.** Direct application of
`local_proj_agree_on_overlap`. -/
private lemma f_eq (hlr : IsLinearlyReductive k G) (D : IsLinearlyReductive.LRD k G R)
    {W : Submodule k R} [FiniteDimensional k ↥W]
    (hW_st : ∀ g, W ≤ W.comap (Representation.ofDistribMulAction k G R g))
    {πW : ↥W →ₗ[k] ↥W}
    (hπW : LinearMap.IsProj
      ((Representation.ofDistribMulAction k G R).subrepresentation W hW_st).invariants πW)
    (hπW_eq : ∀ (g : G) (v : ↥W),
      πW (((Representation.ofDistribMulAction k G R).subrepresentation W hW_st) g v) = πW v)
    (r : R) (hr : r ∈ W) : D.f r = W.subtype (πW ⟨r, hr⟩) := by
  haveI : FiniteDimensional k ↥(D.V r) := D.fin r
  exact hlr.local_proj_agree_on_overlap (D.comap r) hW_st (D.isProj r) (D.apply_rho r)
    hπW hπW_eq (D.mem r) hr

/-- **Additivity of `f`.** Use the common ambient `W := V r ⊔ V s` with a Reynolds projection
`PW` produced by `exists_reynolds`; both sides equal `W.subtype (PW (⟨r,_⟩ + ⟨s,_⟩))`. -/
private lemma f_add (hlr : IsLinearlyReductive k G) (D : IsLinearlyReductive.LRD k G R)
    (r s : R) : D.f (r + s) = D.f r + D.f s := by
  haveI : FiniteDimensional k ↥(D.V r) := D.fin r
  haveI : FiniteDimensional k ↥(D.V s) := D.fin s
  set σ := Representation.ofDistribMulAction k G R
  let W := D.V r ⊔ D.V s
  set hW_st := Representation.sup_le_comap_of_stable (D.comap r) (D.comap s)
  haveI : FiniteDimensional k ↥W := Submodule.finiteDimensional_sup _ _
  obtain ⟨PW, hπW⟩ := hlr.exists_reynolds ((Rep.of σ).subrepresentation W hW_st)
  have hπW_eq := Rep.isProj_invariants_apply_rho hπW
  have hr : r ∈ W := Submodule.mem_sup_left (D.mem r)
  have hs : s ∈ W := Submodule.mem_sup_right (D.mem s)
  rw [D.f_eq hlr hW_st hπW hπW_eq r hr, D.f_eq hlr hW_st hπW hπW_eq s hs,
    D.f_eq hlr hW_st hπW hπW_eq (r + s) (W.add_mem hr hs)]
  have : (⟨r + s, W.add_mem hr hs⟩ : ↥W) = ⟨r, hr⟩ + ⟨s, hs⟩ := rfl
  rw [this, map_add]; simp

/-- **Scalar-compatibility of `f`.** With `W = V r`, both sides equal
`(V r).subtype (π r (c • ⟨r,_⟩)) = c • (V r).subtype (π r ⟨r,_⟩)`. -/
private lemma f_smul (hlr : IsLinearlyReductive k G) (D : IsLinearlyReductive.LRD k G R)
    (c : k) (r : R) : D.f (c • r) = c • D.f r := by
  haveI : FiniteDimensional k ↥(D.V r) := D.fin r
  rw [D.f_eq hlr (D.comap r) (D.isProj r) (D.apply_rho r) (c • r)
        ((D.V r).smul_mem c (D.mem r)),
    D.f_eq hlr (D.comap r) (D.isProj r) (D.apply_rho r) r (D.mem r)]
  have : (⟨c • r, (D.V r).smul_mem c (D.mem r)⟩ : ↥(D.V r)) = c • ⟨r, D.mem r⟩ := rfl
  rw [this, map_smul]; simp

/-- **`f r` lies in the invariants.** Direct from `D.isProj r |>.map_mem`. -/
private lemma f_mapMem (D : IsLinearlyReductive.LRD k G R) (r : R) :
    D.f r ∈ (Representation.ofDistribMulAction k G R).invariants := by
  have hmem := (D.isProj r).map_mem ⟨r, D.mem r⟩
  rw [Representation.mem_invariants] at hmem ⊢
  intro g
  have := congr_arg (D.V r).subtype (hmem g)
  simpa only [Submodule.subtype_apply] using this

/-- **`f` fixes invariants.** Direct from `D.isProj r |>.map_id`. -/
private lemma f_mapId (D : IsLinearlyReductive.LRD k G R) {r : R}
    (hr : r ∈ (Representation.ofDistribMulAction k G R).invariants) : D.f r = r := by
  have hmem : (⟨r, D.mem r⟩ : ↥(D.V r)) ∈
      ((Representation.ofDistribMulAction k G R).subrepresentation
        (D.V r) (D.comap r)).invariants := by
    rw [Representation.mem_invariants]; intro g; ext
    simp only [Representation.subrepresentation_apply, LinearMap.restrict_coe_apply]
    exact ((Representation.ofDistribMulAction k G R).mem_invariants r).mp hr g
  have := congr_arg (D.V r).subtype ((D.isProj r).map_id ⟨r, D.mem r⟩ hmem)
  simpa using this

/-- **`f` is orbit-constant.** Use `W := V r`; `g • r ∈ V r` by stability; both projections
agree at `r` and at `g • r` via `D.apply_rho`. -/
private lemma f_apply_rho (hlr : IsLinearlyReductive k G) (D : IsLinearlyReductive.LRD k G R)
    (g : G) (r : R) :
    D.f (Representation.ofDistribMulAction k G R g r) = D.f r := by
  haveI : FiniteDimensional k ↥(D.V r) := D.fin r
  set σ := Representation.ofDistribMulAction k G R
  have hgr : σ g r ∈ D.V r := D.comap r g (D.mem r)
  rw [D.f_eq hlr (D.comap r) (D.isProj r) (D.apply_rho r) (σ g r) hgr,
    D.f_eq hlr (D.comap r) (D.isProj r) (D.apply_rho r) r (D.mem r)]
  congr 1
  have heq : (σ.subrepresentation (D.V r) (D.comap r)) g ⟨r, D.mem r⟩ = ⟨σ g r, hgr⟩ := rfl
  rw [← heq]
  exact D.apply_rho r g ⟨r, D.mem r⟩

end IsLinearlyReductive.LRD

/-- **Existence of the Reynolds projection, locally finite case.** A linearly reductive group `G`
acting locally finitely on a `k`-module `R` admits a `Rep`-morphism whose underlying linear map
projects onto the invariants.

Math statement: `∃ π : Rep.of σ ⟶ Rep.of σ, LinearMap.IsProj σ.invariants π.hom.hom`, where
`σ := Representation.ofDistribMulAction k G R`.

Proof idea: build `LRD.of_isLocallyFinite hlr hlf` — for each `r`, a f.d. `G`-stable submodule
`V r ∋ r` (from `hlf`) carrying a local Reynolds projection `π r` (from `exists_reynolds`). The
function `D.f r := (V r).subtype (π r ⟨r,·⟩)` is well-defined by `local_proj_agree_on_overlap`,
additive (`f_add`), scalar-linear (`f_smul`), projects to invariants (`f_mapMem`, `f_mapId`),
and orbit-constant (`f_apply_rho`); assemble these via `Rep.mkHom`. -/
theorem IsLinearlyReductive.exists_reynolds_of_isLocallyFinite
    (hlr : IsLinearlyReductive k G)
    (R : Type u) [AddCommGroup R] [Module k R] [DistribMulAction G R] [SMulCommClass G k R]
    (hlf : Representation.IsLocallyFinite k G R) :
    ∃ π : Rep.of (Representation.ofDistribMulAction k G R) ⟶
            Rep.of (Representation.ofDistribMulAction k G R),
      LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants π.hom.hom := by
  set σ := Representation.ofDistribMulAction k G R
  let D := IsLinearlyReductive.LRD.of_isLocallyFinite hlr hlf
  let π_lin : R →ₗ[k] R :=
    { toFun := D.f, map_add' := D.f_add hlr, map_smul' := D.f_smul hlr }
  have hproj : LinearMap.IsProj σ.invariants π_lin := ⟨D.f_mapMem, fun _ hr => D.f_mapId hr⟩
  refine ⟨Rep.mkHom π_lin fun g r => ?_, hproj⟩
  change D.f (σ g r) = σ g (D.f r)
  rw [D.f_apply_rho hlr g r]
  exact ((σ.mem_invariants _).mp (D.f_mapMem r) g).symm

/-- **Image of a submodule under a projection onto invariants lies in invariants.** -/
private lemma IsLinearlyReductive.map_le_invariants
    {p : R →ₗ[k] R}
    (hp : LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants p)
    (V : Submodule k R) :
    Submodule.map p V ≤ (Representation.ofDistribMulAction k G R).invariants := by
  rintro x ⟨v, _, rfl⟩; exact hp.map_mem v

/-- **A submodule sitting inside the invariants is `G`-stable.** -/
private lemma IsLinearlyReductive.le_invariants_comap
    {S : Submodule k R}
    (hS : S ≤ (Representation.ofDistribMulAction k G R).invariants) (g : G) :
    S ≤ S.comap (Representation.ofDistribMulAction k G R g) := fun x hx => by
  rw [Submodule.mem_comap,
    ((Representation.ofDistribMulAction k G R).mem_invariants x).mp (hS hx) g]
  exact hx

/-- **`Module.Finite` of `Submodule.map p V` from `Module.Finite k V`.**

Use the surjection `V → map p V`, `v ↦ p v.val`. -/
private lemma IsLinearlyReductive.finite_submodule_map (p : R →ₗ[k] R)
    {V : Submodule k R} [hV : Module.Finite k V] :
    Module.Finite k ↥(Submodule.map p V) := by
  let f : V →ₗ[k] ↥(Submodule.map p V) :=
    LinearMap.codRestrict (Submodule.map p V) (p ∘ₗ V.subtype)
      (fun v => Submodule.mem_map.mpr ⟨v.1, v.2, rfl⟩)
  refine Module.Finite.of_surjective f ?_
  rintro ⟨x, hx⟩
  obtain ⟨v, hv, hvx⟩ := Submodule.mem_map.mp hx
  exact ⟨⟨v, hv⟩, Subtype.ext hvx⟩

/-- **Common witness submodule** `W := V ⊔ p₁(V) ⊔ p₂(V)`. Used in the locally-finite uniqueness
proof to host both restrictions of `p₁, p₂` simultaneously. -/
private noncomputable def IsLinearlyReductive.commonWitness
    (V : Submodule k R) (p₁ p₂ : R →ₗ[k] R) : Submodule k R :=
  V ⊔ Submodule.map p₁ V ⊔ Submodule.map p₂ V

/-- **`commonWitness` is `G`-stable.** Reduces by `sup_le` to stability of `V` and to the fact
that `Submodule.map pᵢ V ⊆ invariants` (which is `G`-stable). -/
private lemma IsLinearlyReductive.commonWitness_stable
    {V : Submodule k R}
    (hV_st : ∀ g, V ≤ V.comap (Representation.ofDistribMulAction k G R g))
    {p₁ p₂ : R →ₗ[k] R}
    (hp₁ : LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants p₁)
    (hp₂ : LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants p₂) (g : G) :
    IsLinearlyReductive.commonWitness V p₁ p₂ ≤
      (IsLinearlyReductive.commonWitness V p₁ p₂).comap
        (Representation.ofDistribMulAction k G R g) :=
  sup_le
    (sup_le ((hV_st g).trans (Submodule.comap_mono (le_sup_of_le_left le_sup_left)))
      ((IsLinearlyReductive.le_invariants_comap
        (IsLinearlyReductive.map_le_invariants hp₁ V) g).trans
          (Submodule.comap_mono (le_sup_of_le_left le_sup_right))))
    ((IsLinearlyReductive.le_invariants_comap
      (IsLinearlyReductive.map_le_invariants hp₂ V) g).trans
        (Submodule.comap_mono le_sup_right))

/-- **A projection onto invariants maps `commonWitness` into itself.** Decompose `w ∈ W` via
`mem_sup` twice, and recombine using `map_id` on the invariant pieces. -/
private lemma IsLinearlyReductive.commonWitness_maps_self
    (V : Submodule k R) {p₁ p₂ : R →ₗ[k] R}
    (hp₁ : LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants p₁)
    (hp₂ : LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants p₂)
    {p : R →ₗ[k] R}
    (hp : LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants p)
    (hpV : Submodule.map p V ≤ IsLinearlyReductive.commonWitness V p₁ p₂) :
    ∀ w ∈ IsLinearlyReductive.commonWitness V p₁ p₂,
      p w ∈ IsLinearlyReductive.commonWitness V p₁ p₂ := by
  intro w hw
  unfold IsLinearlyReductive.commonWitness at hw ⊢
  rcases Submodule.mem_sup.mp hw with ⟨a, ha, c, hc, rfl⟩
  rcases Submodule.mem_sup.mp ha with ⟨a₁, ha₁, a₂, ha₂, rfl⟩
  rw [map_add, map_add]
  refine Submodule.add_mem _ (Submodule.add_mem _ (hpV ⟨a₁, ha₁, rfl⟩) ?_) ?_
  · rw [hp.map_id a₂ (IsLinearlyReductive.map_le_invariants hp₁ V ha₂)]
    exact Submodule.mem_sup_left (Submodule.mem_sup_right ha₂)
  · rw [hp.map_id c (IsLinearlyReductive.map_le_invariants hp₂ V hc)]
    exact Submodule.mem_sup_right hc

/-- **Restriction of a `Rep`-morphism on `Rep.of σ` to a `G`-stable subspace.** -/
private noncomputable def IsLinearlyReductive.restrictHom
    (W : Submodule k R)
    (hW_st : ∀ g, W ≤ W.comap (Representation.ofDistribMulAction k G R g))
    (π : Rep.of (Representation.ofDistribMulAction k G R) ⟶
         Rep.of (Representation.ofDistribMulAction k G R))
    (hπW : ∀ w ∈ W, π.hom.hom w ∈ W) :
    (Rep.of (Representation.ofDistribMulAction k G R)).subrepresentation W hW_st ⟶
      (Rep.of (Representation.ofDistribMulAction k G R)).subrepresentation W hW_st :=
  Rep.mkHom (LinearMap.restrict π.hom.hom hπW) fun g w => by
    apply Subtype.ext; exact Rep.hom_comm_apply π g w

/-- **Restriction of a projection onto invariants is a projection onto the sub-invariants.** -/
private lemma IsLinearlyReductive.restrictHom_isProj
    {W : Submodule k R}
    (hW_st : ∀ g, W ≤ W.comap (Representation.ofDistribMulAction k G R g))
    {π : Rep.of (Representation.ofDistribMulAction k G R) ⟶
         Rep.of (Representation.ofDistribMulAction k G R)}
    (hπ : LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants π.hom.hom)
    (hπW : ∀ w ∈ W, π.hom.hom w ∈ W) :
    LinearMap.IsProj
      ((Rep.of (Representation.ofDistribMulAction k G R)).subrepresentation W hW_st).ρ.invariants
      (LinearMap.restrict π.hom.hom hπW) := by
  set σ := Representation.ofDistribMulAction k G R
  set MW := (Rep.of σ).subrepresentation W hW_st
  refine ⟨fun w => ?_, fun w hw => ?_⟩
  · rw [Representation.mem_invariants]; intro g; apply Subtype.ext
    simp only [LinearMap.restrict_coe_apply]
    exact ((σ.mem_invariants _).mp (hπ.map_mem _)) g
  · apply Subtype.ext
    simp only [LinearMap.restrict_coe_apply]
    apply hπ.map_id; rw [Representation.mem_invariants]; intro g
    exact congr_arg Subtype.val (((MW.ρ.mem_invariants w).mp hw) g)

/-- **Locally-finite uniqueness, pointwise.** For each `r : R`, the two projections agree at `r`.
This is the heart of `reynolds_unique_of_isLocallyFinite`; the latter just promotes pointwise
equality to morphism equality via `Action.hom_ext`/`ModuleCat.hom_ext`. -/
private lemma IsLinearlyReductive.reynolds_unique_at
    (hlr : IsLinearlyReductive k G)
    (hlf : Representation.IsLocallyFinite k G R)
    (π₁ π₂ : Rep.of (Representation.ofDistribMulAction k G R) ⟶
              Rep.of (Representation.ofDistribMulAction k G R))
    (h₁ : LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants π₁.hom.hom)
    (h₂ : LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants π₂.hom.hom)
    (r : R) : π₁.hom.hom r = π₂.hom.hom r := by
  obtain ⟨V, hV_fin, hV_stable, hV_mem⟩ := hlf r
  have hV_c : ∀ g, V ≤ V.comap (Representation.ofDistribMulAction k G R g) :=
    fun g v hv => hV_stable g ⟨v, hv⟩
  haveI : FiniteDimensional k V := hV_fin
  haveI : Module.Finite k ↥(Submodule.map π₁.hom.hom V) := finite_submodule_map _
  haveI : Module.Finite k ↥(Submodule.map π₂.hom.hom V) := finite_submodule_map _
  haveI : FiniteDimensional k ↥(V ⊔ Submodule.map π₁.hom.hom V : Submodule k R) :=
    Submodule.finiteDimensional_sup _ _
  haveI : FiniteDimensional k ↥(commonWitness V π₁.hom.hom π₂.hom.hom) :=
    Submodule.finiteDimensional_sup _ _
  have hp₁W := commonWitness_maps_self V h₁ h₂ h₁ (le_sup_of_le_left le_sup_right)
  have hp₂W := commonWitness_maps_self V h₁ h₂ h₂ le_sup_right
  set W := commonWitness V π₁.hom.hom π₂.hom.hom
  set hW_st := commonWitness_stable hV_c h₁ h₂
  set MW : Rep k G := (Rep.of (Representation.ofDistribMulAction k G R)).subrepresentation W hW_st
  have hQ : restrictHom W hW_st π₁ hp₁W = restrictHom W hW_st π₂ hp₂W :=
    hlr.reynolds_unique MW _ _ (restrictHom_isProj _ h₁ hp₁W) (restrictHom_isProj _ h₂ hp₂W)
  have hrW : r ∈ W := Submodule.mem_sup_left (Submodule.mem_sup_left hV_mem)
  exact congr_arg Subtype.val
    (congr_arg (fun P : MW ⟶ MW => P.hom.hom ⟨r, hrW⟩) hQ)

/-- **Uniqueness of the Reynolds projection (locally finite case).** Any two `Rep`-morphism
projections onto `Rᴳ` are equal.

Math statement: `π₁ = π₂` whenever both are `Rep`-morphism projections onto
`(ofDistribMulAction k G R).invariants` and the action is locally finite.

Proof idea: by `Action.hom_ext`/`ModuleCat.hom_ext` it suffices to show pointwise equality, i.e.
`π₁.hom.hom r = π₂.hom.hom r` for every `r`, which is `reynolds_unique_at`. -/
theorem IsLinearlyReductive.reynolds_unique_of_isLocallyFinite
    (hlr : IsLinearlyReductive k G)
    (R : Type u) [AddCommGroup R] [Module k R] [DistribMulAction G R] [SMulCommClass G k R]
    (hlf : Representation.IsLocallyFinite k G R)
    (π₁ π₂ : Rep.of (Representation.ofDistribMulAction k G R) ⟶
              Rep.of (Representation.ofDistribMulAction k G R))
    (h₁ : LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants π₁.hom.hom)
    (h₂ : LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants π₂.hom.hom) :
    π₁ = π₂ := by
  apply Action.hom_ext; apply ModuleCat.hom_ext; ext r
  exact hlr.reynolds_unique_at hlf π₁ π₂ h₁ h₂ r

end LocallyFiniteReynolds

/-! ## E. Reynolds projection on algebras -/


section AlgebraReynolds

variable {k : Type u} [Field k] {G : Type u} [Group G]

/-- **Left multiplication by `a` as a `k`-linear map.** -/
noncomputable def Representation.leftMulHom {R : Type u} [CommRing R] [Algebra k R] (a : R) :
    R →ₗ[k] R where
  toFun := (a * ·)
  map_add' x y := mul_add a x y
  map_smul' c s := by simp only [RingHom.id_apply]; exact mul_smul_comm c a s

variable {R : Type u} [CommRing R] [Algebra k R] [MulSemiringAction G R] [SMulCommClass G k R]

/-- **The Reynolds defect** `δ r := π(a r) - a · π r`. Vanishes iff `π` is `Rᴳ`-linear at `a`. -/
private noncomputable def IsLinearlyReductive.reynoldsDefect
    (π : Rep.of (Representation.ofDistribMulAction k G R) ⟶
         Rep.of (Representation.ofDistribMulAction k G R)) (a : R) : R →ₗ[k] R :=
  π.hom.hom.comp (Representation.leftMulHom a) - (Representation.leftMulHom a).comp π.hom.hom

/-- **`reynoldsDefect` is `G`-equivariant.** Uses invariance of `a` and equivariance of `π`. -/
private lemma IsLinearlyReductive.reynoldsDefect_equiv
    (π : Rep.of (Representation.ofDistribMulAction k G R) ⟶
         Rep.of (Representation.ofDistribMulAction k G R))
    {a : R} (ha : a ∈ (Representation.ofDistribMulAction k G R).invariants) (g : G) (s : R) :
    IsLinearlyReductive.reynoldsDefect π a (g • s) =
      g • IsLinearlyReductive.reynoldsDefect π a s := by
  have ha_g : g • a = a := (Representation.mem_invariants _ a).mp ha g
  have hπ_eq : ∀ x : R, π.hom.hom (g • x) = g • π.hom.hom x := fun x => Rep.hom_comm_apply π g x
  change π.hom.hom (a * g • s) - a * π.hom.hom (g • s) =
    g • (π.hom.hom (a * s) - a * π.hom.hom s)
  rw [show a * g • s = g • (a * s) by rw [smul_mul', ha_g], hπ_eq, hπ_eq, smul_sub,
    show g • (a * π.hom.hom s) = a * (g • π.hom.hom s) by rw [smul_mul', ha_g]]

/-- **`reynoldsDefect` lands in invariants.** Both `π(a·s)` and `a · π(s)` are invariant
(the second uses that `a` and `π s` are both invariant), so their difference is. -/
private lemma IsLinearlyReductive.reynoldsDefect_mem_invariants
    {π : Rep.of (Representation.ofDistribMulAction k G R) ⟶
         Rep.of (Representation.ofDistribMulAction k G R)}
    (hπ : LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants π.hom.hom)
    {a : R} (ha : a ∈ (Representation.ofDistribMulAction k G R).invariants) (s : R) :
    IsLinearlyReductive.reynoldsDefect π a s ∈
      (Representation.ofDistribMulAction k G R).invariants := by
  have ha_g : ∀ g, g • a = a := (Representation.mem_invariants _ a).mp ha
  have h_a_πs : a * π.hom.hom s ∈
      (Representation.ofDistribMulAction k G R).invariants := by
    rw [Representation.mem_invariants]; intro g
    have hπs : g • π.hom.hom s = π.hom.hom s :=
      (Representation.mem_invariants _ _).mp (hπ.map_mem s) g
    change g • (a * π.hom.hom s) = a * π.hom.hom s
    rw [smul_mul', ha_g, hπs]
  change π.hom.hom (a * s) - a * π.hom.hom s ∈
    (Representation.ofDistribMulAction k G R).invariants
  exact Submodule.sub_mem _ (hπ.map_mem _) h_a_πs

/-- **`reynoldsDefect` vanishes on invariants.** For `s ∈ Rᴳ`, both `π(a·s)` and `a · π s` equal
`a · s` (since `a · s` is invariant and `π` fixes invariants), so their difference is `0`. -/
private lemma IsLinearlyReductive.reynoldsDefect_vanishes_on_invariants
    {π : Rep.of (Representation.ofDistribMulAction k G R) ⟶
         Rep.of (Representation.ofDistribMulAction k G R)}
    (hπ : LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants π.hom.hom)
    {a : R} (ha : a ∈ (Representation.ofDistribMulAction k G R).invariants)
    {s : R} (hs : s ∈ (Representation.ofDistribMulAction k G R).invariants) :
    IsLinearlyReductive.reynoldsDefect π a s = 0 := by
  have ha_g : ∀ g, g • a = a := (Representation.mem_invariants _ a).mp ha
  have hs_g : ∀ g, g • s = s := (Representation.mem_invariants _ s).mp hs
  have h_as : a * s ∈ (Representation.ofDistribMulAction k G R).invariants := by
    rw [Representation.mem_invariants]; intro g
    change g • (a * s) = a * s; rw [smul_mul', ha_g, hs_g]
  change π.hom.hom (a * s) - a * π.hom.hom s = 0
  rw [hπ.map_id (a * s) h_as, hπ.map_id s hs, sub_self]

/-- **`reynoldsDefect + π` as a representation morphism.** Wrap the linear sum as a `Rep`-morphism
via `Rep.mkHom`; equivariance follows from `reynoldsDefect_equiv` and equivariance of `π`. -/
private noncomputable def IsLinearlyReductive.reynoldsAddDefect
    (π : Rep.of (Representation.ofDistribMulAction k G R) ⟶
         Rep.of (Representation.ofDistribMulAction k G R))
    {a : R} (ha : a ∈ (Representation.ofDistribMulAction k G R).invariants) :
    Rep.of (Representation.ofDistribMulAction k G R) ⟶
      Rep.of (Representation.ofDistribMulAction k G R) :=
  Rep.mkHom (IsLinearlyReductive.reynoldsDefect π a + π.hom.hom) fun g s => by
    have hπ_eq : π.hom.hom (g • s) = g • π.hom.hom s := Rep.hom_comm_apply π g s
    change IsLinearlyReductive.reynoldsDefect π a (g • s) + π.hom.hom (g • s) =
      g • (IsLinearlyReductive.reynoldsDefect π a s + π.hom.hom s)
    rw [IsLinearlyReductive.reynoldsDefect_equiv π ha, hπ_eq, smul_add]

/-- **`reynoldsAddDefect` is a projection onto invariants.** Sum-component check:
`δ s ∈ invariants` and `π s ∈ invariants` give `(δ + π) s ∈ invariants`; for `s ∈ invariants`,
`δ s = 0` and `π s = s`, so `(δ + π) s = s`. -/
private lemma IsLinearlyReductive.reynoldsAddDefect_isProj
    {π : Rep.of (Representation.ofDistribMulAction k G R) ⟶
         Rep.of (Representation.ofDistribMulAction k G R)}
    (hπ : LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants π.hom.hom)
    {a : R} (ha : a ∈ (Representation.ofDistribMulAction k G R).invariants) :
    LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants
      (IsLinearlyReductive.reynoldsAddDefect π ha).hom.hom := by
  refine ⟨fun s => ?_, fun s hs => ?_⟩
  · simp only [reynoldsAddDefect, Rep.mkHom_hom, LinearMap.add_apply]
    exact Submodule.add_mem _ (reynoldsDefect_mem_invariants hπ ha s) (hπ.map_mem s)
  · simp only [reynoldsAddDefect, Rep.mkHom_hom, LinearMap.add_apply]
    rw [reynoldsDefect_vanishes_on_invariants hπ ha hs, zero_add, hπ.map_id s hs]

/-- **The Reynolds projection is `Rᴳ`-linear.** For a linearly reductive group `G` acting on a
`k`-algebra `R` by ring automorphisms with locally finite action, there is a Reynolds projection
`π` onto the invariants additionally satisfying `π (a * r) = a * π r` for every invariant
`a ∈ Rᴳ`. This is the Reynolds identity underlying Hilbert finiteness in GIT.

Math statement: same `π` as `exists_reynolds_of_isLocallyFinite` plus
`∀ {a} ∈ Rᴳ, ∀ r, π (a r) = a · π r`.

Proof idea: take `π` from `exists_reynolds_of_isLocallyFinite`. The defect
`δ r := π(a r) − a · π r` is `G`-equivariant (`reynoldsDefect_equiv`), lands in invariants
(`reynoldsDefect_mem_invariants`), and vanishes on invariants
(`reynoldsDefect_vanishes_on_invariants`). Hence `δ + π` is again a Rep-morphism projection onto
`Rᴳ` (`reynoldsAddDefect_isProj`); locally-finite uniqueness forces it to equal `π`, hence
`δ = 0`, which gives the desired identity at every `r`. -/
theorem IsLinearlyReductive.exists_reynolds_mulCompat_of_isLocallyFinite
    (hlr : IsLinearlyReductive k G)
    (R : Type u) [CommRing R] [Algebra k R] [MulSemiringAction G R] [SMulCommClass G k R]
    (hlf : Representation.IsLocallyFinite k G R) :
    ∃ π : Rep.of (Representation.ofDistribMulAction k G R) ⟶
            Rep.of (Representation.ofDistribMulAction k G R),
      LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants π.hom.hom ∧
      ∀ {a : R}, a ∈ (Representation.ofDistribMulAction k G R).invariants →
        ∀ r : R, π.hom.hom (a * r) = a * π.hom.hom r := by
  obtain ⟨πR, hπR⟩ := hlr.exists_reynolds_of_isLocallyFinite R hlf
  refine ⟨πR, hπR, ?_⟩
  intro a ha r
  have h_eq := hlr.reynolds_unique_of_isLocallyFinite R hlf
    (IsLinearlyReductive.reynoldsAddDefect πR ha) πR
    (IsLinearlyReductive.reynoldsAddDefect_isProj hπR ha) hπR
  have h_lin : IsLinearlyReductive.reynoldsDefect πR a + πR.hom.hom = πR.hom.hom :=
    congrArg (fun μ : Rep.of _ ⟶ Rep.of _ => μ.hom.hom) h_eq
  have hδ_zero : IsLinearlyReductive.reynoldsDefect πR a = 0 :=
    add_right_cancel (b := πR.hom.hom) (by rw [zero_add]; exact h_lin)
  have hδ_r : IsLinearlyReductive.reynoldsDefect πR a r = 0 := by rw [hδ_zero]; rfl
  exact sub_eq_zero.mp hδ_r

end AlgebraReynolds
