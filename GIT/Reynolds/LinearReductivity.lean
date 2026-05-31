import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Rep
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Linear reductivity

A group `G` is *linearly reductive* over a field `k` if every finite-dimensional `Rep k G` is
semisimple. This file packages:

* the class `IsLinearlyReductive k G`,
* Maschke's theorem as the instance `IsLinearlyReductive.of_fintype` (a finite group whose
  order is invertible in `k` is linearly reductive),
* the invariants `ρ.invariants` packaged as a `Subrepresentation` via
  `Representation.invariantsSubrepresentation`,
* the helper `Subrepresentation.toSubmodule_isCompl` (transfer of `IsCompl` from subreps to
  underlying submodules).

It also collects three reusable `Rep`-level building blocks used everywhere else:

* `Rep.mkHom` — assemble a `Rep`-morphism from a `G`-equivariant linear map.
* `Rep.mkHom_hom` — its `simp` companion.
* `Rep.isProj_invariants_apply_rho` — projections onto the invariants are orbit-constant.
-/

universe u

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

variable {k : Type u} [Field k] (G : Type u) [Group G]

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
