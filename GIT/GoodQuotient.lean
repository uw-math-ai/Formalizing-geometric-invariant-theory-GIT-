import Mathlib.CategoryTheory.Action.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine

universe u

open AlgebraicGeometry CategoryTheory

namespace GoodQuotient

variable {G : Type u} [Group G]

/-!
## Section actions
-/

/-- The `G`-action on sections `Γ(φ⁻¹U, 𝒪_X)` induced by the `G`-action
`X.ρ : G →* (X.V ⟶ X.V)` on the scheme `X.V`.

**Construction sketch.**  For each `g : G` the automorphism `X.ρ g : X.V ⟶ X.V`
restricts to `φ⁻¹U` (which is G-stable by equivariance of `φ`) and hence
induces, via the presheaf pullback `X.V.presheaf.map`, a ring map
`Γ(φ⁻¹U, 𝒪_X) → Γ(φ⁻¹U, 𝒪_X)`.

TODO: replace the `sorry`-based body with the actual derivation once the
G-stability of `φ⁻¹U` is established in Mathlib. -/
def inducedSectionAction
    {X : Action Scheme.{u} G}
    {Y : Scheme.{u}}
    (φ : X ⟶ Action.trivial G Y)
    (U : Y.Opens) :
    MulAction G (X.V.presheaf.obj ⟨φ.hom ⁻¹ᵁ U⟩) where
  smul g s :=
    -- TODO: derive from `X.ρ g` via presheaf pullback restricted to φ⁻¹U.
    -- For now this is a placeholder that compiles; it does NOT implement
    -- the correct mathematical action.
    s
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-!
## Core predicates
-/

/-- `IsInvariantSections φ` asserts that for every affine open `U ⊆ Y` the
pullback map
```
  φ.hom.app U : Γ(U, 𝒪_Y) → Γ(φ⁻¹U, 𝒪_X)
```
is injective and its image equals the `G`-fixed points
`Γ(φ⁻¹U, 𝒪_X)^G`.

Together with affineness, this is the local condition that `φ` looks like
`Spec A → Spec A^G` on every affine patch.

The `G`-action on sections is supplied by `inducedSectionAction`; once that
definition is corrected, this predicate will carry the correct mathematical
meaning automatically. -/
def IsInvariantSections
    {X : Action Scheme.{u} G}
    {Y : Scheme.{u}}
    (φ : X ⟶ Action.trivial G Y) : Prop :=
  ∀ (U : Y.Opens), IsAffineOpen U →
    haveI : MulAction G (X.V.presheaf.obj ⟨φ.hom ⁻¹ᵁ U⟩) :=
      inducedSectionAction φ U
    Function.Injective (φ.hom.app U).hom ∧
    Set.range (φ.hom.app U).hom =
      MulAction.fixedPoints G (X.V.presheaf.obj ⟨φ.hom ⁻¹ᵁ U⟩)

/-- `IsGInvariantSubset W` holds when the subset `W ⊆ |X|` (points of the
underlying topological space) is stable under every `g : G`. -/
def IsGInvariantSubset
    {X : Action Scheme.{u} G}
    (W : Set ↥X.V) : Prop :=
  ∀ (g : G), (X.ρ g).base '' W ⊆ W

/-!
## Main structure
-/

/-- **Good quotient.**

For a `G`-scheme `X : Action Scheme G`, a *good quotient* consists of:

* a scheme `Y` (the orbit space),
* a `G`-invariant morphism `φ : X → Y` (encoded as a morphism to the
  trivially-acted-on `Y` in `Action Scheme G`),

satisfying:

1. **Affine** — `φ` is an affine morphism.
2. **Invariant sections** — for every affine open `U ⊆ Y` the pullback
   `φ* : Γ(U, 𝒪_Y) → Γ(φ⁻¹U, 𝒪_X)` is an isomorphism onto the
   `G`-fixed subsheaf; see `IsInvariantSections`.

The classical definition (MFK §0.2) additionally requires:
3. Surjectivity of `φ`.
4. The image of every closed `G`-invariant subset is closed.
5. Disjoint closed `G`-invariant subsets have disjoint images.

These are stated as separate propositions below (currently `sorry`'d) rather
than fields, matching standard practice in Mathlib where hypotheses that are
*consequences* of the structure are separated from the *defining data*. -/
structure IsGoodQuotient (X : Action Scheme.{u} G) where
  /-- The quotient scheme. -/
  Y : Scheme.{u}
  /-- The quotient morphism (G-invariance is automatic from the trivial action on Y). -/
  φ : X ⟶ Action.trivial G Y
  /-- (1) φ is affine. -/
  affine : IsAffineHom φ.hom
  /-- (2) φ looks like Spec A → Spec A^G on every affine patch. -/
  invariantSections : IsInvariantSections φ

/-!
## Properties (Proposition 8.1.3 / MFK §0.2)
-/

section Properties

variable {X : Action Scheme.{u} G} (q : IsGoodQuotient X)

/-- **Prop. 8.1.3 (1a).** A good quotient is surjective. -/
theorem IsGoodQuotient.surjective :
    Function.Surjective q.φ.hom.base := by
  sorry

/-- **Prop. 8.1.3 (1b).** The image of a closed G-invariant subset is closed. -/
theorem IsGoodQuotient.image_isClosed
    {Z : Set ↥X.V}
    (hZ_closed : IsClosed Z)
    (hZ_inv : IsGInvariantSubset Z) :
    IsClosed (q.φ.hom.base '' Z) := by
  sorry

/-- **Prop. 8.1.3 (2).** For closed G-invariant subsets `Z₁ Z₂ ⊆ X`,
```
  image(Z₁) ∩ image(Z₂) = image(Z₁ ∩ Z₂).
```
Equivalently, `φ(x₁) = φ(x₂)` iff the orbit closures `G·x₁` and `G·x₂`
meet. -/
theorem IsGoodQuotient.image_inter
    {Z₁ Z₂ : Set ↥X.V}
    (hZ₁_closed : IsClosed Z₁) (hZ₁_inv : IsGInvariantSubset Z₁)
    (hZ₂_closed : IsClosed Z₂) (hZ₂_inv : IsGInvariantSubset Z₂) :
    q.φ.hom.base '' (Z₁ ∩ Z₂) =
      q.φ.hom.base '' Z₁ ∩ q.φ.hom.base '' Z₂ := by
  sorry

end Properties

end GoodQuotient
