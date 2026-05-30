import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Algebra.Ring.Action.Basic

universe u

open Monoid MonoidAlgebra Representation

section ReynoldsOperator

variable (k : Type*) [CommSemiring k]
variable (G : Type*) [Group G] [Fintype G]
variable [Invertible (Fintype.card G : k)]

variable (R : Type*)
variable [AddCommMonoid R]
variable [Module k R]
variable [DistribMulAction G R]
variable [SMulCommClass G k R]

/-- Reynolds operator obtained by averaging over a finite group. -/
noncomputable def reynoldsOperator : R →ₗ[k] R :=
  (Representation.ofDistribMulAction k G R).averageMap

theorem reynoldsOperator_mem_invariants (r : R) :
    reynoldsOperator k G R r ∈
      (Representation.ofDistribMulAction k G R).invariants :=
  (Representation.ofDistribMulAction k G R).averageMap_invariant r

theorem reynoldsOperator_id (r : R)
    (hr :
      r ∈ (Representation.ofDistribMulAction k G R).invariants) :
    reynoldsOperator k G R r = r :=
  (Representation.ofDistribMulAction k G R).averageMap_id r hr

end ReynoldsOperator
