import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace Representation

variable {k : Type*} [CommSemiring k]
variable {G : Type*} [Monoid G]
variable {R : Type*}
variable [AddCommMonoid R] [Module k R]
variable [DistribMulAction G R]

/-- A `G`-action on `R` is locally finite if every element
lies in a finite-dimensional `G`-stable submodule. -/
def IsLocallyFinite
    (k : Type*) [CommSemiring k]
    (G : Type*) [Monoid G]
    (R : Type*)
    [AddCommMonoid R]
    [Module k R]
    [DistribMulAction G R] : Prop :=
  ∀ r : R,
    ∃ V : Submodule k R,
      Module.Finite k V ∧
      (∀ (g : G) (v : V), (g • (v : R)) ∈ V) ∧
      r ∈ V

/-- Every action of a finite monoid is locally finite. -/
theorem isLocallyFinite_of_finite
    (k : Type*) [CommSemiring k]
    (G : Type*) [Monoid G] [Finite G]
    (R : Type*)
    [AddCommMonoid R]
    [Module k R]
    [DistribMulAction G R]
    [SMulCommClass G k R] :
    IsLocallyFinite k G R := by
  intro r
  refine ⟨Submodule.span k (Set.range (fun g : G => g • r)), ?_, ?_, ?_⟩
  · exact Module.Finite.span_of_finite k (Set.finite_range _)
  · intro g v
    change g • (v : R) ∈
      Submodule.span k (Set.range (fun g' : G => g' • r))
    have hv :
        (v : R) ∈
          Submodule.span k (Set.range (fun g' : G => g' • r)) :=
      v.property
    exact Submodule.span_induction
      (mem := fun x ⟨g', hg'⟩ =>
        hg' ▸
        Submodule.subset_span
          ⟨g * g', mul_smul g g' r⟩)
      (zero := by simp)
      (add := fun x y _ _ hx hy => by
        rw [smul_add]
        exact Submodule.add_mem _ hx hy)
      (smul := fun a x _ hx => by
        rw [smul_comm]
        exact Submodule.smul_mem _ a hx)
      hv
  · exact Submodule.subset_span ⟨1, one_smul G r⟩

end Representation
