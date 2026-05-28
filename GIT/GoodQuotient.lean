/- definition of good quotient -/

import Mathlib.CategoryTheory.Action.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine

universe u

open AlgebraicGeometry CategoryTheory

namespace GoodQuotient_Definition

variable (G : Type u) [Group G]

/-- **Helper predicate: local `Spec A → Spec A^G` structure.**

For a morphism `φ : X ⟶ Action.trivial G Y` in `Action Scheme G` and a per-open
`G`-action `ρ` on the local sections of `X.V` over preimages `φ⁻¹U`, this
predicate asserts that for every affine open `U ⊆ Y`, the structure-sheaf
pullback `φ.hom.app U : Γ(U, 𝒪_Y) → Γ(φ⁻¹U, 𝒪_X)` is injective and its image
is exactly the `G`-invariant sections.

This is the substantive content of "good quotient" beyond just being an affine
`G`-invariant morphism — locally `φ` looks like `Spec A → Spec A^G`.

The `G`-action `ρ` on local sections is taken as a hypothesis here; in a
complete formalization it should be derived from `X.ρ` together with the
`G`-invariance of `φ⁻¹U` (which follows from the equivariance of `φ`). -/
def IsInvariantSections
    {G : Type u} [Group G]
    {X : Action Scheme.{u} G} {Y : Scheme.{u}}
    (φ : X ⟶ Action.trivial G Y)
    (ρ : ∀ U : Y.Opens, MulAction G (X.V.presheaf.obj ⟨φ.hom ⁻¹ᵁ U⟩)) : Prop :=
  ∀ (U : Y.Opens), IsAffineOpen U →
    Function.Injective (φ.hom.app U).hom ∧
    Set.range (φ.hom.app U).hom =
      MulAction.fixedPoints G (X.V.presheaf.obj ⟨φ.hom ⁻¹ᵁ U⟩)

/-- **Definition: Good Quotient (skeleton).**

For a `G`-scheme `X : Action Scheme G`, a *good quotient* of `X` is the data of:

* a scheme `Y`,
* a morphism `φ : X ⟶ Action.trivial G Y` in `Action Scheme G` (since `Y`
  carries the trivial `G`-action, the morphism's equivariance condition
  `X.ρ g ≫ φ.hom = φ.hom ≫ (trivial G Y).ρ g` simplifies to
  `X.ρ g ≫ φ.hom = φ.hom`, i.e. `φ` is automatically `G`-invariant),
* a per-open `G`-action `ρ` on local sections of `X.V` over preimages `φ⁻¹U`,

satisfying:

1. **`isAffine`** — `φ` is an affine morphism;
2. **`invariantSections`** — locally `φ` looks like `Spec A → Spec A^G`;
   see `IsInvariantSections`.

The classical full definition adds three further conditions — surjectivity,
closed-image of `G`-invariant closed subsets, and separation of disjoint
closed `G`-invariant subsets — which can be added as additional fields when
needed. -/
structure isGoodQuotient (X : Action Scheme.{u} G) where
  /-- The underlying quotient scheme. -/
  Y : Scheme.{u}
  /-- The quotient morphism, as a morphism in `Action Scheme G` to the
  trivially-acted-on `Y`. The category structure encodes `G`-equivariance,
  which (given the trivial action on `Y`) is `G`-invariance of the underlying
  scheme map. -/
  φ : X ⟶ Action.trivial G Y
  /-- Per-open `G`-action on local sections. Should be derivable from `X.ρ`
  plus the `G`-invariance of `φ⁻¹U`; taken as a hypothesis here. -/
  ρ : ∀ U : Y.Opens, MulAction G (X.V.presheaf.obj ⟨φ.hom ⁻¹ᵁ U⟩)

  /-- 1. `φ` is an affine morphism (G-invariance comes for free from the category). -/
  affine : IsAffineHom φ.hom
  /-- 2. Locally, `φ` looks like `Spec A → Spec A^G`: for every affine open
  `U ⊆ Y`, the pullback `φ* : Γ(U, 𝒪_Y) → Γ(φ⁻¹U, 𝒪_X)^G` is an isomorphism. -/
  invariantSections : IsInvariantSections φ ρ

/-Helper method: -/
/-- A subset `W ⊆ X` is G-invariant if it is stable under every `g : G`. -/
def IsGInvariantSubset {X : Action Scheme G} (W : Set X.V) : Prop :=
  ∀ (g : G), (X.ρ g).base '' W ⊆ W

--   /-- **Proposition 8.1.3(1a).** A good quotient is surjective. -/
-- theorem GoodQuotient.surjective : by sorry

-- /-- **Proposition 8.1.3(1b).** The image of a closed G-invariant subset is closed. -/
-- theorem GoodQuotient.image_isClosed : by sorry

-- /-- **Proposition 8.1.3(2).** For closed G-invariant subsets `Z₁ Z₂ ⊆ X`,
--     `im(Z₁ ∩ Z₂) = im(Z₁) ∩ im(Z₂)`.
--     Equivalently: `π(x₁) = π(x₂)` if and only if `G·x₁ ∩ G·x₂ ≠ ∅`. -/
-- theorem GoodQuotient.image_inter : by sorry

end GoodQuotient_Definition
