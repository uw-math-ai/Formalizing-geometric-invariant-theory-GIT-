import GIT.PRs.LinearlyReductive

universe u

open Representation

variable {k : Type u} [Field k]
variable {G : Type u} [Group G]

namespace Representation

/--
Uniqueness of a Reynolds operator.

This theorem is postponed until the categorical
naturality framework is developed.
-/
theorem IsLinearlyReductive.reynolds_unique
    (hlr : IsLinearlyReductive k G)
    (M : Rep k G)
    [FiniteDimensional k M]
    (π₁ π₂ : M →ₗ[k] M)
    (h₁ : LinearMap.IsProj M.ρ.invariants π₁)
    (h₁_eq : ∀ g v, π₁ (M.ρ g v) = π₁ v)
    (h₂ : LinearMap.IsProj M.ρ.invariants π₂)
    (h₂_eq : ∀ g v, π₂ (M.ρ g v) = π₂ v) :
    π₁ = π₂ := by
  sorry

/--
Naturality of Reynolds operators.

This theorem is postponed until the categorical
construction of Reynolds operators.
-/
theorem IsLinearlyReductive.reynolds_natural
    (hlr : IsLinearlyReductive k G)
    (M₁ M₂ : Rep k G)
    [FiniteDimensional k M₁]
    [FiniteDimensional k M₂]
    (ι : M₁ →ₗ[k] M₂)
    (hι : ∀ g v, ι (M₁.ρ g v) = M₂.ρ g (ι v))
    (π₁ : M₁ →ₗ[k] M₁)
    (π₂ : M₂ →ₗ[k] M₂)
    (h₁ : LinearMap.IsProj M₁.ρ.invariants π₁)
    (h₁_eq : ∀ g v, π₁ (M₁.ρ g v) = π₁ v)
    (h₂ : LinearMap.IsProj M₂.ρ.invariants π₂)
    (h₂_eq : ∀ g v, π₂ (M₂.ρ g v) = π₂ v) :
    ∀ v : M₁, ι (π₁ v) = π₂ (ι v) := by
  sorry

end Representation
