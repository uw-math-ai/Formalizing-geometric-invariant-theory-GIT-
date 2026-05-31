import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Locally finite actions

A `DistribMulAction` of a monoid `G` on a `k`-module `R` is *locally finite* if every element
of `R` lies in a finite-dimensional `G`-stable `k`-submodule.

This file defines `Representation.IsLocallyFinite` and proves the basic instance: every action
of a finite monoid is locally finite (take the `k`-span of the orbit).

## Main definitions

* `Representation.IsLocallyFinite`

## Main results

* `Representation.smul_mem_span_orbit`: `G`-stability of the `k`-span of a single orbit.
* `Representation.isLocallyFinite_of_finite`: actions of finite monoids are locally finite.
-/

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
