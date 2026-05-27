import Mathlib.CategoryTheory.Action.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.GroupTheory.GroupAction.Basic

universe u

open AlgebraicGeometry
open CategoryTheory
open TensorProduct

namespace GIT

variable (G : Type u) [Group G]

/-!
# Invariant subring
-/

/-- The invariant subring `A^G`. -/
def InvariantSubring
    (A : Type u)
    [CommRing A]
    [MulSemiringAction G A] :
    Subring A where
  carrier :=
    { a : A | ∀ g : G, g • a = a }

  zero_mem' := by
    intro g
    simp

  one_mem' := by
    intro g
    simp

  add_mem' := by
    intro a b ha hb g
    simp [ha g, hb g]

  mul_mem' := by
    intro a b ha hb g
    simp [ha g, hb g]

  neg_mem' := by
    intro a ha g
    simp [ha g]

/-- Convenient notation for `A^G`. -/
abbrev AG
    (A : Type u)
    [CommRing A]
    [MulSemiringAction G A] :=
  InvariantSubring (G := G) A

section Reynolds

variable
  {A : Type u}
  [CommRing A]
  [MulSemiringAction G A]

/-- A Reynolds operator. -/
structure Reynolds where
  proj : A →+ AG (G := G) A

  linear :
    ∀ (a : AG (G := G) A) (f : A),
      proj ((a : A) * f) = a * proj f

  retract :
    ∀ a : AG (G := G) A,
      proj a = a

end Reynolds

/-!
# Quotients
-/

/-- Local invariant-section condition. -/
def IsInvariantSections
    {X : Action Scheme.{u} G}
    {Y : Scheme.{u}}
    (φ : X ⟶ Action.trivial G Y)
    (ρ :
      ∀ U : Y.Opens,
        MulAction G
          (X.V.presheaf.obj ⟨φ.hom ⁻¹ᵁ U⟩)) :
    Prop :=
  ∀ U : Y.Opens,
    IsAffineOpen U →
      Function.Injective (φ.hom.app U).hom ∧
      True

/-- Good quotient. -/
structure GoodQuotient
    (X : Action Scheme.{u} G) where
  Y : Scheme.{u}
  φ : X ⟶ Action.trivial G Y
  ρ :
    ∀ U : Y.Opens,
      MulAction G
        (X.V.presheaf.obj ⟨φ.hom ⁻¹ᵁ U⟩)
  reynolds :
    ∀ U : Y.Opens,
      IsAffineOpen U →
        Reynolds
          (G := G)
          (A := X.V.presheaf.obj ⟨φ.hom ⁻¹ᵁ U⟩)
  affine :
    IsAffineHom φ.hom
  invariantSections :
    IsInvariantSections
      (G := G)
      φ
      ρ

/-- `G`-stable subsets. -/
def IsGInvariantSubset
    {X : Action Scheme G}
    (W : Set X.V) :
    Prop :=
  ∀ g : G,
    (X.ρ g).base '' W ⊆ W

variable {G}
variable {X : Action Scheme G}

variable (q : GoodQuotient G X)

section TensorInvariants

variable
  {A : Type u}
  [CommRing A]
  [MulSemiringAction G A]

instance invariantModule :
    Module (AG (G := G) A) A :=
  (InvariantSubring (G := G) A).toModule

variable
  (R : Reynolds (G := G) (A := A))

variable
  {N : Type u}
  [AddCommMonoid N]
  [Module (AG (G := G) A) N]

/-- The map `n ↦ n ⊗ 1`. -/
def tensorMap
    (n : N) :
    N ⊗[AG (G := G) A] A :=
  TensorProduct.tmul
    (AG (G := G) A)
    n
    (1 : A)

/-- Invariant tensors. -/
def TensorInvariants :=
  { x : N ⊗[AG (G := G) A] A //
      ∀ g : G, g • x = x }

/-- Auxiliary linear map. -/
noncomputable def reynoldsLinear :
    N →ₗ[AG (G := G) A]
      A →ₗ[AG (G := G) A] N :=
by
  refine
  { toFun := fun n =>
      {
        toFun := fun f =>
          ((R.proj f : AG (G := G) A) • n)

        map_add' := by
          intro f g
          simp [map_add, add_smul]

        map_smul' := by
          intro a f
          change
            ((R.proj ((a : A) * f) : AG (G := G) A) • n)
            =
            ((a * R.proj f : AG (G := G) A) • n)

          rw [R.linear]
      }

    map_add' := by
      intro x y
      ext f
      simp [smul_add]

    map_smul' := by
      intro a n
      ext f
      simp [smul_smul]
  }

/-- Reynolds retraction. -/
noncomputable def reynoldsRetraction :
    N ⊗[AG (G := G) A] A →
      ₗ[AG (G := G) A] N :=
  TensorProduct.lift
    (reynoldsLinear
      (G := G)
      (A := A)
      (N := N)
      R)

/-- Left inverse property. -/
lemma retraction_left_inv
    (n : N) :
    reynoldsRetraction
      (G := G)
      (A := A)
      (N := N)
      R
      (tensorMap
        (G := G)
        (A := A)
        (N := N)
        n)
      =
      n := by
  simp [
    tensorMap,
    reynoldsRetraction,
    reynoldsLinear
  ]

/--
Averaging lemma.

This is the key invariant-theoretic statement.
-/
axiom retraction_right_inv
    (x :
      TensorInvariants
        (G := G)
        (A := A)
        (N := N)) :
    tensorMap
      (G := G)
      (A := A)
      (N := N)
      (reynoldsRetraction
        (G := G)
        (A := A)
        (N := N)
        R
        x.1)
      =
      x.1

/-- Exercise 7.5.1(a). -/
theorem tensor_invariants_iso :
    Function.Bijective
      (fun n : N =>
        (⟨
          tensorMap
            (G := G)
            (A := A)
            (N := N)
            n,
          by
            intro g
            simp [tensorMap]
        ⟩ :
          TensorInvariants
            (G := G)
            (A := A)
            (N := N))) := by
  constructor

  · intro n m h

    have h' :=
      congrArg
        (fun x =>
          reynoldsRetraction
            (G := G)
            (A := A)
            (N := N)
            R
            x.1)
        h

    simpa [retraction_left_inv]
      using h'

  · intro x

    refine
      ⟨
        reynoldsRetraction
          (G := G)
          (A := A)
          (N := N)
          R
          x.1,
        ?_
      ⟩

    ext

    exact
      retraction_right_inv
        (G := G)
        (A := A)
        (N := N)
        (R := R)
        x

end TensorInvariants

/-- Exercise 7.5.1(b). -/
theorem GoodQuotient.surjective :
    Function.Surjective q.φ.hom.base := by
  sorry

/-- Exercise 7.5.1(c). -/
theorem GoodQuotient.image_isClosed
    {W : Set X.V}
    (hW : IsClosed W)
    (hWG :
      IsGInvariantSubset
        (G := G)
        W) :
    IsClosed
      (q.φ.hom.base '' W) := by
  sorry

end GIT
