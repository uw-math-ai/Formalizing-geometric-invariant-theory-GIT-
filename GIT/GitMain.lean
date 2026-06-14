import Mathlib.Algebra.Ring.Action.Group
import Mathlib.Algebra.Ring.Action.Invariant
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Maps
import GIT.ReynoldsOperator

open scoped DirectSum
open scoped BigOperators

universe u v w uR

section GradedCheck_S1

-- Step 0: Basic objects

variable (k : Type u) [Field k]
variable (G : Type v) [Group G]
variable (ι : Type w) [DecidableEq ι] [AddMonoid ι]
variable (R : Type*) [Semiring R] [Algebra k R]
variable (𝒜 : ι → Submodule k R)

-- Step 4: Assume R is already graded

variable [GradedAlgebra 𝒜]

-- Step 5: Encode the action by algebra automorphisms

variable (ρ : G →* R ≃ₐ[k] R)

-- Step 6: Define the missing condition: the action preserves the grading

def PreservesGrading : Prop :=
  ∀ (g : G) (d : ι) {r : R}, r ∈ 𝒜 d → (ρ g : R → R) r ∈ 𝒜 d

#check PreservesGrading

-- Step 7: Define the invariant subalgebra R^G

def FixedSubalgebra (ρ : G →* R ≃ₐ[k] R) : Subalgebra k R :=
{
  carrier := { r : R | ∀ g : G, (ρ g) r = r }

  zero_mem' := by
    intro g
    simp

  one_mem' := by
    intro g
    simp

  add_mem' := by
    intro x y hx hy g
    simp [map_add, hx g, hy g]

  mul_mem' := by
    intro x y hx hy g
    simp [map_mul, hx g, hy g]

  algebraMap_mem' := by
    intro a g
    exact (ρ g).commutes a
}

-- Step 8a: Define the degree-d piece inside ambient R

def FixedPiece (d : ι) : Submodule k R :=
  𝒜 d ⊓ (FixedSubalgebra (k := k) (G := G) (R := R) ρ).toSubmodule

-- Step 8b: Define the degree-d piece inside R^G

def FixedPieceInFixedSubalgebra (d : ι) :
    Submodule k (FixedSubalgebra (k := k) (G := G) (R := R) ρ) :=
{
  carrier := { x | (x : R) ∈ 𝒜 d }

  zero_mem' := by
    change (0 : R) ∈ 𝒜 d
    exact Submodule.zero_mem (𝒜 d)

  add_mem' := by
    intro x y hx hy
    change ((x : R) + (y : R)) ∈ 𝒜 d
    exact Submodule.add_mem (𝒜 d) hx hy

  smul_mem' := by
    intro a x hx
    change (a • (x : R)) ∈ 𝒜 d
    exact Submodule.smul_mem (𝒜 d) a hx
}

-- Lemma for Step 9:
lemma fixed_component_mem_degree
    (x : FixedSubalgebra (k := k) (G := G) (R := R) ρ)
    (d : ι) :
    ((DirectSum.decompose 𝒜 (x : R)) d : R) ∈ 𝒜 d := by
  exact ((DirectSum.decompose 𝒜 (x : R)) d).property

lemma proj_commutes_of_preservesGrading
    (hpres : PreservesGrading (k := k) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ))
    (g : G) (d : ι) :
    (GradedAlgebra.proj 𝒜 d).comp (ρ g).toLinearMap =
      (ρ g).toLinearMap.comp (GradedAlgebra.proj 𝒜 d) := by
  refine DirectSum.decompose_lhom_ext 𝒜 (fun e => ?_)
  ext y
  by_cases h : e = d
  · subst d
    have hyρ : (ρ g).toLinearMap (y : R) ∈ 𝒜 e := by
      simpa using hpres g e y.property
    change
      ↑(((DirectSum.decompose 𝒜) ((ρ g).toLinearMap (y : R))) e)
        =
      (ρ g).toLinearMap
        (↑(((DirectSum.decompose 𝒜) (y : R)) e))
    rw [DirectSum.decompose_of_mem_same 𝒜 hyρ]
    rw [DirectSum.decompose_of_mem_same 𝒜 y.property]
  · have hyρ : (ρ g).toLinearMap (y : R) ∈ 𝒜 e := by
      simpa using hpres g e y.property
    change
      ↑(((DirectSum.decompose 𝒜) ((ρ g).toLinearMap (y : R))) d)
        =
      (ρ g).toLinearMap
        (↑(((DirectSum.decompose 𝒜) (y : R)) d))
    rw [DirectSum.decompose_of_mem_ne 𝒜 hyρ h]
    rw [DirectSum.decompose_of_mem_ne 𝒜 y.property h]
    simp

lemma fixed_component_is_fixed
    (hpres : PreservesGrading (k := k) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ))
    (x : FixedSubalgebra (k := k) (G := G) (R := R) ρ)
    (d : ι) :
    ((DirectSum.decompose 𝒜 (x : R)) d : R) ∈
      (FixedSubalgebra (k := k) (G := G) (R := R) ρ).toSubmodule := by
  intro g
  have hlin :
      (GradedAlgebra.proj 𝒜 d).comp (ρ g).toLinearMap =
        (ρ g).toLinearMap.comp (GradedAlgebra.proj 𝒜 d) :=
    proj_commutes_of_preservesGrading
      (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ)
      hpres g d
  have hcomm :
      GradedAlgebra.proj 𝒜 d ((ρ g).toLinearMap (x : R)) =
        (ρ g).toLinearMap (GradedAlgebra.proj 𝒜 d (x : R)) := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun F : R →ₗ[k] R => F (x : R)) hlin
  have hxfix : (ρ g).toLinearMap (x : R) = (x : R) := by
    simpa using x.property g
  rw [hxfix] at hcomm
  simpa [GradedAlgebra.proj_apply] using hcomm.symm

lemma fixed_component_mem_fixedPiece
    (hpres : PreservesGrading (k := k) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ))
    (x : FixedSubalgebra (k := k) (G := G) (R := R) ρ)
    (d : ι) :
    (⟨((DirectSum.decompose 𝒜 (x : R)) d : R),
      fixed_component_is_fixed
        (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ)
        hpres x d⟩ :
      FixedSubalgebra (k := k) (G := G) (R := R) ρ) ∈
      FixedPieceInFixedSubalgebra
        (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ) d := by
  exact
    fixed_component_mem_degree
      (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ)
      x d

-- forget map for Step 9
def fixedPieceForget (d : ι) :
    FixedPieceInFixedSubalgebra
      (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ) d →+
      𝒜 d :=
{
  toFun := fun x =>
    ⟨((x : FixedSubalgebra (k := k) (G := G) (R := R) ρ) : R), x.property⟩

  map_zero' := by
    ext
    rfl

  map_add' := by
    intro x y
    ext
    rfl
}

omit [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜] in
lemma fixedPieceForget_injective (d : ι) :
    Function.Injective
      (fixedPieceForget
        (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ) d) := by
  intro x y h
  have hR :
      (((x : FixedPieceInFixedSubalgebra
          (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ) d) :
          FixedSubalgebra (k := k) (G := G) (R := R) ρ) : R)
        =
      (((y : FixedPieceInFixedSubalgebra
          (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ) d) :
          FixedSubalgebra (k := k) (G := G) (R := R) ρ) : R) := by
    exact congrArg
      (fun z : 𝒜 d => (z : R))
      h
  apply Subtype.ext
  apply Subtype.ext
  exact hR


-- Step 9: Main theorem
-- R^G = ⨁ d, (R_d ∩ R^G)

theorem fixedSubalgebra_decomposes
    (hpres : PreservesGrading (k := k) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ)) :
    DirectSum.IsInternal
      fun d : ι =>
        FixedPieceInFixedSubalgebra
          (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ) d := by
  classical
  let B : ι → Submodule k (FixedSubalgebra (k := k) (G := G) (R := R) ρ) :=
    fun d =>
      FixedPieceInFixedSubalgebra
        (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ) d
  let forget : (d : ι) → B d →+ 𝒜 d :=
    fun d =>
      fixedPieceForget
        (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ) d
  let coeFixed :
      FixedSubalgebra (k := k) (G := G) (R := R) ρ →+ R :=
  {
    toFun := fun x => (x : R)

    map_zero' := by
      rfl

    map_add' := by
      intro x y
      rfl
  }
  have hcomp :
      coeFixed.comp (DirectSum.coeAddMonoidHom B)
        =
      (DirectSum.coeAddMonoidHom 𝒜).comp (DirectSum.map forget) := by
    apply DirectSum.addHom_ext
    intro i y
    simp [B, forget, coeFixed, fixedPieceForget]
  change Function.Bijective ⇑(DirectSum.coeAddMonoidHom B)
  constructor
  · -- injective
    intro a b h
    have hR' :
        coeFixed ((DirectSum.coeAddMonoidHom B) a)
          =
        coeFixed ((DirectSum.coeAddMonoidHom B) b) := by
      exact congrArg
        (fun z : FixedSubalgebra (k := k) (G := G) (R := R) ρ =>
          coeFixed z)
        h
    have ha :
        coeFixed ((DirectSum.coeAddMonoidHom B) a)
          =
        (DirectSum.coeAddMonoidHom 𝒜) ((DirectSum.map forget) a) := by
      exact congrArg
        (fun F : (DirectSum ι fun d => B d) →+ R => F a)
        hcomp
    have hb :
        coeFixed ((DirectSum.coeAddMonoidHom B) b)
          =
        (DirectSum.coeAddMonoidHom 𝒜) ((DirectSum.map forget) b) := by
      exact congrArg
        (fun F : (DirectSum ι fun d => B d) →+ R => F b)
        hcomp
    have hR :
        (DirectSum.coeAddMonoidHom 𝒜)
            ((DirectSum.map forget) a)
          =
        (DirectSum.coeAddMonoidHom 𝒜)
            ((DirectSum.map forget) b) := by
      calc
        (DirectSum.coeAddMonoidHom 𝒜) ((DirectSum.map forget) a)
            = coeFixed ((DirectSum.coeAddMonoidHom B) a) := ha.symm
        _ = coeFixed ((DirectSum.coeAddMonoidHom B) b) := hR'
        _ = (DirectSum.coeAddMonoidHom 𝒜) ((DirectSum.map forget) b) := hb
    have hinjA :
        Function.Injective ⇑(DirectSum.coeAddMonoidHom 𝒜) :=
      (DirectSum.Decomposition.isInternal 𝒜).1
    have hmap :
        (DirectSum.map forget) a = (DirectSum.map forget) b :=
      hinjA hR
    exact
      ((DirectSum.map_injective forget).2
        (fun d =>
          fixedPieceForget_injective
            (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ) d))
        hmap
  · -- surjective
    intro x
    let y : DirectSum ι fun d => B d :=
      (DirectSum.mk
        (fun d => B d)
        ((DirectSum.decompose 𝒜 (x : R)).support))
        (fun d =>
          (⟨
            ⟨
              ((DirectSum.decompose 𝒜 (x : R)) d.1 : R),
              fixed_component_is_fixed
                (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ)
                hpres x d.1
            ⟩,
            fixed_component_mem_degree
              (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ)
              x d.1
          ⟩ : B d.1))
    refine ⟨y, ?_⟩
    apply Subtype.ext
    change
      coeFixed ((DirectSum.coeAddMonoidHom B) y)
        =
      (x : R)
    have hy_decomp :
        (DirectSum.map forget) y = DirectSum.decompose 𝒜 (x : R) := by
      ext d
      by_cases hd : d ∈ (DirectSum.decompose 𝒜 (x : R)).support
      · have hy_apply :
            y d =
              (⟨
                ⟨
                  ((DirectSum.decompose 𝒜 (x : R)) d : R),
                  fixed_component_is_fixed
                    (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ)
                    hpres x d
                ⟩,
                fixed_component_mem_degree
                  (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ)
                  x d
              ⟩ : B d) := by
          dsimp [y]
          exact DirectSum.mk_apply_of_mem hd
        rw [DirectSum.map_apply, hy_apply]
        simp [forget, fixedPieceForget]
      · have hy_apply : y d = 0 := by
          dsimp [y]
          exact DirectSum.mk_apply_of_notMem hd
        have hzero : (DirectSum.decompose 𝒜 (x : R)) d = 0 := by
          exact DFinsupp.notMem_support_iff.mp hd
        rw [DirectSum.map_apply, hy_apply, hzero]
        simp
    have hyR :
        coeFixed ((DirectSum.coeAddMonoidHom B) y)
          =
        (DirectSum.coeAddMonoidHom 𝒜) ((DirectSum.map forget) y) := by
      exact congrArg
        (fun F : (DirectSum ι fun d => B d) →+ R => F y)
        hcomp
    calc
      coeFixed ((DirectSum.coeAddMonoidHom B) y)
          =
        (DirectSum.coeAddMonoidHom 𝒜) ((DirectSum.map forget) y) := hyR
      _ =
        (DirectSum.coeAddMonoidHom 𝒜) (DirectSum.decompose 𝒜 (x : R)) := by
          rw [hy_decomp]
      _ = (x : R) := by
          change
            (DirectSum.coeAddMonoidHom 𝒜)
              (DirectSum.Decomposition.decompose' (ℳ := 𝒜) (x : R))
              =
            (x : R)
          exact DirectSum.Decomposition.left_inv (ℳ := 𝒜) (x : R)

/-! ### Glue: turn `IsInternal` (Step 1) into a `GradedAlgebra` instance on `R^G`. -/

/-- The unit of `R^G` lies in the degree-`0` fixed piece. -/
instance fixedPieceInFixedSubalgebra_gradedOne :
    SetLike.GradedOne
      (fun d : ι => FixedPieceInFixedSubalgebra
        (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ) d) where
  one_mem := show (1 : R) ∈ 𝒜 0 from SetLike.GradedOne.one_mem

/-- Multiplication in `R^G` respects the inherited grading. -/
instance fixedPieceInFixedSubalgebra_gradedMul :
    SetLike.GradedMul
      (fun d : ι => FixedPieceInFixedSubalgebra
        (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ) d) where
  mul_mem := fun {i j a b} ha hb =>
    show ((a : R) * (b : R)) ∈ 𝒜 (i + j) from
      SetLike.GradedMul.mul_mem ha hb

/-- The fixed-piece family on `R^G` forms a graded monoid. -/
instance fixedPieceInFixedSubalgebra_gradedMonoid :
    SetLike.GradedMonoid
      (fun d : ι => FixedPieceInFixedSubalgebra
        (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ) d) where

/-- **Glue lemma (1): `R^G` carries an inherited graded-algebra structure.**

Combining Step 1 (`fixedSubalgebra_decomposes`) with the `SetLike.GradedMonoid` instances
above, the family `FixedPieceInFixedSubalgebra`q makes `R^G` a graded `k`-algebra. -/
noncomputable def fixedSubalgebra_gradedAlgebra
    (hpres : PreservesGrading (k := k) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ)) :
    GradedAlgebra
      (fun d : ι => FixedPieceInFixedSubalgebra
        (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ) d) :=
  DirectSum.IsInternal.gradedAlgebra
    (fixedSubalgebra_decomposes
      (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ) hpres)

end GradedCheck_S1

section IrrelevantIdeal_FiniteType_S2

/-
If `R₊` is finitely generated as an ideal, then `R` is finitely generated as an algebra over the
degree-`0` graded piece `𝒜 0`. To conclude finite generation over the base field `k`, you still
need a separate hypothesis that `𝒜 0` is finitely generated as a `k`-algebra (then apply
transitivity); that extra hypothesis cannot be dropped in general.
-/

namespace GIT

section

variable {k : Type u} [Field k]
variable {R : Type uR} [CommRing R] [Algebra k R]
variable {𝒜 : ℕ → Submodule k R} [GradedAlgebra 𝒜]

/-!
Pseudo-code blueprint for the proof.

High-level idea:

- From `h : (irrelevant 𝒜).toIdeal.FG`, pick a finite set `S` generating the irrelevant ideal.
- Replace `S` by the finite set of homogeneous components of elements of `S`.
  (So we may assume `S ⊆ ⋃ i > 0, 𝒜 i` and consists of homogeneous elements.)
- Prove by strong induction on `d : ℕ`:
  every `y ∈ 𝒜 d` lies in the subalgebra of `R` generated (over `𝒜 0`) by `S`.
  For `d = 0` this is trivial; for `d > 0`, use `y ∈ irrelevant` to write
  `y = ∑ a_j * s_j` with `s_j ∈ S`, and then show each `a_j` has smaller degree,
  so by IH each `a_j` is in the subalgebra, hence so is `y`.
- Conclude `Algebra.FiniteType (𝒜 0) R`. For `Algebra.FiniteType k R`, combine with
  `[Algebra.FiniteType k (𝒜 0)]` via transitivity (see corollary below).
-/

/- Step 0: convenience notation for the irrelevant ideal as an `Ideal R`. -/
abbrev irrelevantIdeal : Ideal R := (HomogeneousIdeal.irrelevant 𝒜).toIdeal

/- Step 1: homogenize the generating set.

Given `S` generating the irrelevant ideal, we want a finite `T` consisting of homogeneous
elements of positive degree that still generates the same ideal.

This is the “take all homogeneous components of each generator” step.
-/
lemma exists_finset_homogeneous_pos_generators
    (h : (irrelevantIdeal (k := k) (R := R) (𝒜 := 𝒜)).FG) :
    ∃ T : Finset R,
      (Ideal.span (T : Set R) = irrelevantIdeal (k := k) (R := R) (𝒜 := 𝒜)) ∧
      (∀ t ∈ T, ∃ d : ℕ, 0 < d ∧ t ∈ 𝒜 d) := by
  classical
  -- Let `s` be the set of positive-degree homogeneous elements.
  let s : Set R := ⋃ i : ℕ, ⋃ _ : 0 < i, (𝒜 i : Set R)
  -- The irrelevant ideal is the ideal span of `s`.
  have hirr : irrelevantIdeal (k := k) (R := R) (𝒜 := 𝒜) = Ideal.span s := by
    -- This is exactly `HomogeneousIdeal.irrelevant_eq_span`.
    simpa [irrelevantIdeal, s] using (HomogeneousIdeal.irrelevant_eq_span (𝒜 := 𝒜))
  -- Convert `h : irrelevantIdeal.FG` into `FG (Ideal.span s)`.
  have hspan_s_fg : (Ideal.span s : Ideal R).FG := by
    rcases h with ⟨S, hS⟩
    refine ⟨S, ?_⟩
    -- rewrite target ideal using `hirr` (avoid `simp` unfolding `irrelevantIdeal` to a kernel)
    calc
      Ideal.span (S : Set R)
          = irrelevantIdeal (k := k) (R := R) (𝒜 := 𝒜) := hS
      _   = Ideal.span s := hirr
  -- Use the general lemma: a finitely generated span has a finite subset of generators.
  -- (This is stated for submodules, but `Ideal.span` is defeq `Submodule.span`.)
  have hfg_submodule : (Submodule.span R s).FG := by
    rcases hspan_s_fg with ⟨S, hS⟩
    refine ⟨S, ?_⟩
    -- Avoid `simp [Ideal.span]` recursion: coerce the ideal equality to a submodule equality.
    have hS' :
        (Ideal.span (S : Set R) : Submodule R R) = (Ideal.span s : Submodule R R) :=
      congrArg (fun (I : Ideal R) => (I : Submodule R R)) hS
    -- Don't unfold anything: just change the goal to match `hS'`.
    change (Ideal.span (S : Set R) : Submodule R R) = (Ideal.span s : Submodule R R)
    exact hS'
  rcases (Submodule.fg_span_iff_fg_span_finset_subset (R := R) (M := R) s).1 hfg_submodule with
    ⟨T, hTs, hspan⟩
  refine ⟨T, ?_, ?_⟩
  · -- show the ideal generated by `T` is the irrelevant ideal
    -- We have `Submodule.span R s = Submodule.span R (T : Set R)`.
    -- Convert to ideals and use `hirr`.
    have : Ideal.span s = Ideal.span (T : Set R) := by
      -- Convert the submodule equality into an ideal equality, then unfold `Ideal.span` once.
      have hspan' : (Submodule.span R s : Ideal R) = (Submodule.span R (T : Set R) : Ideal R) :=
        congrArg (fun (N : Submodule R R) => (N : Ideal R)) hspan
      -- Again, avoid unfolding: just change the goal to match `hspan'`.
      change (Ideal.span s : Ideal R) = (Ideal.span (T : Set R) : Ideal R)
      exact hspan'
    -- Rearrange to match the goal, without unfolding `irrelevantIdeal` to a kernel.
    calc
      Ideal.span (T : Set R) = Ideal.span s := this.symm
      _ = irrelevantIdeal (k := k) (R := R) (𝒜 := 𝒜) := hirr.symm
  · intro t ht
    -- Use `t ∈ T` ⇒ `t ∈ s` from `hTs`, then unpack membership in the union.
    have : t ∈ s := hTs (by simpa using ht)
    -- `t ∈ ⋃ i, ⋃ (_:0<i), 𝒜 i` gives the desired degree.
    rcases Set.mem_iUnion.1 this with ⟨d, hd⟩
    rcases Set.mem_iUnion.1 hd with ⟨hdpos, hmem⟩
    exact ⟨d, hdpos, hmem⟩

/- Step 2: set up the intermediate base algebra `𝒜 0 →ₐ[k] R`.

In a graded algebra, the degree-0 part is a subalgebra; there is an induced algebra structure.
We’ll want `Algebra.FiniteType (𝒜 0) R` and then use `Algebra.FiniteType.trans`.

This lemma is a placeholder for the typeclass plumbing (it may already be inferable).
-/
noncomputable def inst_algebra_degreeZero :
    Algebra (𝒜 0) R := by
  classical
  -- This instance is provided by Mathlib from `[GradedAlgebra 𝒜]`.
  exact inferInstance

noncomputable def inst_isScalarTower_degreeZero :
    IsScalarTower k (𝒜 0) R := by
  classical
  -- This is *not* always found automatically by typeclass search, so we build it explicitly
  -- from the compatibility of `algebraMap`s.
  letI : Algebra (𝒜 0) R := inst_algebra_degreeZero (k := k) (R := R) (𝒜 := 𝒜)
  refine IsScalarTower.of_algebraMap_eq' (R := k) (S := (𝒜 0)) (A := R) ?_
  -- `simp` should know that the map `(𝒜 0) → R` is the coercion, so the tower condition is
  -- definitional.
  ext x
  simp

/- Step 3: if finite positive-degree homogeneous `T` spans the irrelevant ideal, then every
`𝒜 d` lies in `Algebra.adjoin (𝒜 0) T`.

Strong induction on `d`. Degree `0`: `y ∈ 𝒜 0` embeds in the adjoin. For `d > 0`, `y` lies in
the irrelevant ideal hence in `Ideal.span T`; pick `y = ∑ l t * t`, apply the degree-`d` graded
projection (which fixes `y`) and push it through the sum. For each `t`, graded multiplication with
homogeneous `t` identifies the degree-`d` piece of `l t*t` with `(decompose (l t)) (d - deg t) * t`
when `deg t ≤ d`; that graded piece has degree `< d`, so IH covers it, then multiply by `t` in the
adjoin. If `deg t > d`, the projection is `0`. Sum and `mul` closure finish.
-/

lemma homogeneous_mem_adjoin_of_irrelevant_eq_span
    {T : Finset R}
    (hspan : Ideal.span (T : Set R) = irrelevantIdeal (k := k) (R := R) (𝒜 := 𝒜))
    (hT : ∀ t ∈ T, ∃ d : ℕ, 0 < d ∧ t ∈ 𝒜 d) :
    ∀ d : ℕ, ∀ y : R, y ∈ 𝒜 d → y ∈ Algebra.adjoin (𝒜 0) (T : Set R) := by
  classical
  -- We prove the claim by strong induction on `d`.
  intro d
  refine Nat.strong_induction_on d ?_
  intro d ih y hy
  by_cases hd0 : d = 0
  · -- degree 0: `y` comes from the base algebra `𝒜 0`.
    subst hd0
    -- View `y` as an element of `𝒜 0` and use `Subalgebra.algebraMap_mem`.
    -- (The `Algebra (𝒜 0) R` instance is provided by step 2.)
    have : y ∈ (Algebra.adjoin (𝒜 0) (T : Set R) : Subalgebra (𝒜 0) R) := by
      -- `⟨y, hy⟩ : 𝒜 0` maps to `y` in `R`.
      simpa using (Subalgebra.algebraMap_mem (Algebra.adjoin (𝒜 0) (T : Set R)) ⟨y, hy⟩)
    exact this
  · -- positive degree:
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    -- First show `y ∈ irrelevantIdeal`.
    have hy_irrel : y ∈ irrelevantIdeal (k := k) (R := R) (𝒜 := 𝒜) := by
      -- `HomogeneousIdeal.mem_irrelevant_of_mem` gives membership in the *homogeneous* ideal.
      have : y ∈ HomogeneousIdeal.irrelevant 𝒜 := by
        exact HomogeneousIdeal.mem_irrelevant_of_mem (𝒜 := 𝒜) (x := y) (i := d) hdpos hy
      -- Coerce to the underlying ideal.
      simpa [irrelevantIdeal] using this
    -- Rewrite using the spanning hypothesis.
    have hy_span : y ∈ Ideal.span (T : Set R) := by
      -- `hspan : Ideal.span T = irrelevantIdeal`, so use it backwards.
      simpa [hspan] using hy_irrel
    -- Extract an explicit finite `T`-linear combination for `y`.
    have hy_span' : y ∈ (Submodule.span R (T : Set R) : Submodule R R) := by
      -- `Ideal.span` is defeq `Submodule.span` on `R`.
      change y ∈ ((Ideal.span (T : Set R) : Ideal R) : Submodule R R)
      exact hy_span
    rcases
        (Finsupp.mem_span_iff_linearCombination (R := R) (M := R) (s := (T : Set R)) y).1 hy_span'
      with ⟨l, hl⟩
    -- Choose a positive degree for each generator `t ∈ T`.
    choose degT hdegTpos hdegTmem using (fun t : (T : Set R) => hT t.1 t.2)
    -- Let `π_d : R →+ R` be the degree-`d` projection `z ↦ (decompose z d : R)`.
    let πd : R →+ R :=
      { toFun := fun z => ((DirectSum.decompose 𝒜 z) d : R)
        map_zero' := by simp
        map_add' := by simp }
    -- Since `y ∈ 𝒜 d`, `π_d y = y`.
    have hπy : πd y = y := by
      simpa [πd] using (DirectSum.decompose_of_mem_same 𝒜 (x := y) (i := d) hy)
    -- Expand the span expression `hl` as a concrete finset sum in `R`.
    have hl_sum :
        (Finsupp.linearCombination R (fun t : (T : Set R) => (t : R)) l) =
          Finset.sum l.support (fun t => l t * (t : R)) := by
      classical
      simp [Finsupp.linearCombination_apply, smul_eq_mul, Finsupp.sum]
    -- Apply `πd` to `hl` and rewrite the RHS as a sum of `πd` applied to each summand.
    have hproj :
        y = Finset.sum l.support (fun t => πd (l t * (t : R))) := by
      -- start from `πd (linearCombination ...) = πd y`
      have h1 : πd (Finsupp.linearCombination R (fun t : (T : Set R) => (t : R)) l) = πd y := by
        simpa [hl] using congrArg πd hl
      -- rewrite the `linearCombination` as a finset sum and push `πd` inside
      have h1' : πd (Finset.sum l.support (fun t => l t * (t : R))) = πd y := by
        -- use `rw` (not `simp`) to avoid rewriting `πd` across the sum
        have h1' := h1
        rw [hl_sum] at h1'
        exact h1'
      have h2 : Finset.sum l.support (fun t => πd (l t * (t : R))) = πd y := by
        simpa [map_sum] using h1'
      -- use `πd y = y` since `y` is homogeneous of degree `d`
      have h3 : Finset.sum l.support (fun t => πd (l t * (t : R))) = y := by
        simpa [hπy] using h2
      exact h3.symm
    -- Each summand `πd (l t * t)` lies in the adjoin,
    -- hence their sum (and thus `y`) lies in the adjoin.
    have hsum_mem :
        (Finset.sum l.support (fun t => πd (l t * (t : R)))) ∈
          Algebra.adjoin (𝒜 0) (T : Set R) := by
      classical
      refine (Subsemiring.sum_mem (Algebra.adjoin (𝒜 0) (T : Set R)).toSubsemiring) ?_
      intro t ht_support
      -- `t` itself is a generator, hence in the adjoin.
      have ht_mem : (t : R) ∈ Algebra.adjoin (𝒜 0) (T : Set R) :=
        Algebra.subset_adjoin t.2
      -- Use graded projection lemma on the product `(l t) * t`.
      have ht_hom : (t : R) ∈ 𝒜 (degT t) := by
        simpa using (hdegTmem t)
      by_cases hle : degT t ≤ d
      · have hπ :
            πd (l t * (t : R)) =
              ((DirectSum.decompose 𝒜 (l t)) (d - degT t) : R) * (t : R) := by
          simpa [πd] using
            (DirectSum.coe_decompose_mul_of_right_mem_of_le (𝒜 := 𝒜)
              (a := l t) (b := (t : R)) (n := d) (i := degT t) ht_hom hle)
        have hlt : d - degT t < d :=
          Nat.sub_lt (Nat.pos_of_ne_zero (Nat.ne_of_gt hdpos)) (hdegTpos t)
        have hcoeff_mem :
            ((DirectSum.decompose 𝒜 (l t)) (d - degT t) : R) ∈
              Algebra.adjoin (𝒜 0) (T : Set R) := by
          have hcoeff_hom :
              ((DirectSum.decompose 𝒜 (l t)) (d - degT t) : R) ∈ 𝒜 (d - degT t) :=
            ((DirectSum.decompose 𝒜 (l t)) (d - degT t)).2
          exact ih (d - degT t) hlt _ hcoeff_hom
        -- rewrite the goal using `hπ`, then use closure under multiplication
        rw [hπ]
        exact
          (Subsemiring.mul_mem (Algebra.adjoin (𝒜 0) (T : Set R)).toSubsemiring hcoeff_mem ht_mem)
      · have hπ0 : πd (l t * (t : R)) = 0 := by
          simpa [πd] using
            (DirectSum.coe_decompose_mul_of_right_mem_of_not_le (𝒜 := 𝒜)
              (a := l t) (b := (t : R)) (n := d) (i := degT t) ht_hom hle)
        -- rewrite the goal using `hπ0`
        rw [hπ0]
        exact zero_mem _
    simpa [hproj] using hsum_mem

/- Step 4: package the induction into an `Algebra.FiniteType (𝒜 0) R` statement.

Once you know every element of `R` lies in `Algebra.adjoin (𝒜 0) T`, you conclude the adjoin is `⊤`,
and therefore `R` is `Algebra.FiniteType` over `𝒜 0`.
-/
lemma finiteType_degreeZero_of_irrelevant_fg
    (h : (irrelevantIdeal (k := k) (R := R) (𝒜 := 𝒜)).FG) :
    Algebra.FiniteType (𝒜 0) R := by
  classical
  obtain ⟨T, hspan, hT⟩ := exists_finset_homogeneous_pos_generators (k := k) (R := R) (𝒜 := 𝒜) h
  -- `Algebra.FiniteType (𝒜 0) R` means `(⊤ : Subalgebra (𝒜 0) R).FG`,
  -- i.e. some finset adjoins to `⊤`.
  refine ⟨⟨T, ?_⟩⟩
  rw [eq_top_iff]
  intro r _
  -- Write `r` as a finite sum of its homogeneous components.
  rw [← DirectSum.sum_support_decompose 𝒜 r]
  refine Subalgebra.sum_mem (Algebra.adjoin (𝒜 0) (T : Set R)) ?_
  intro i _
  -- Each graded piece lies in `𝒜 i`, hence in the adjoin by the induction lemma.
  have hy : ((DirectSum.decompose 𝒜 r) i : R) ∈ 𝒜 i :=
    SetLike.coe_mem ((DirectSum.decompose 𝒜 r) i)
  exact homogeneous_mem_adjoin_of_irrelevant_eq_span (𝒜 := 𝒜) hspan hT i _ hy

/- Final theorem: finitely generated irrelevant ideal implies `R` is finitely generated over `𝒜 0`.

No assumption on how `𝒜 0` sits over `k`;
that is exactly the content of `finiteType_degreeZero_of_irrelevant_fg`.
-/
theorem finiteType_of_finitely_generated_irrelevant_ideal
    (h : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG) :
    Algebra.FiniteType (𝒜 0) R :=
  finiteType_degreeZero_of_irrelevant_fg (k := k) (R := R) (𝒜 := 𝒜) (h := by
    simpa [irrelevantIdeal] using h)

/- Corollary over `k`: combine the theorem above with finite generation of `𝒜 0` over `k`. -/
theorem finiteType_k_of_finitely_generated_irrelevant_ideal
    [Algebra.FiniteType k (𝒜 0)] (h : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG) :
    Algebra.FiniteType k R := by
  classical
  letI : Algebra (𝒜 0) R := inst_algebra_degreeZero (k := k) (R := R) (𝒜 := 𝒜)
  letI : IsScalarTower k (𝒜 0) R := inst_isScalarTower_degreeZero (k := k) (R := R) (𝒜 := 𝒜)
  exact Algebra.FiniteType.trans (R := k) (S := 𝒜 0) (A := R)
    (hRS := inferInstance) (hSA := finiteType_of_finitely_generated_irrelevant_ideal h)
end

end GIT

end IrrelevantIdeal_FiniteType_S2

section RGplus_finitely_generated_S3
/-
We assume R is Noetherian. Then every ideal of R is finitely generated.
In particular, the extended ideal R₊^G R is finitely generated.
-/

variable (R : Type*) [CommRing R]
variable [IsNoetherianRing R]

/- Placeholder for the extended ideal `R₊^G R` inside `R`. -/
variable (extendedRGplus : Ideal R)

/-- Since `R` is Noetherian, the ideal `R₊^G R` is finitely generated. -/
theorem extendedRGplus_fg : extendedRGplus.FG := by
  classical
  exact IsNoetherian.noetherian extendedRGplus

/-- Choose a finite generating set for `R₊^G R`. -/
theorem exists_generators_extendedRGplus :
    ∃ s : Finset R, Ideal.span (↑s : Set R) = extendedRGplus := by
  classical
  simpa [Ideal.FG] using
    (extendedRGplus_fg
      (R := R) (extendedRGplus := extendedRGplus))

end RGplus_finitely_generated_S3

section RGplus_generators_S4

variable (R : Type*) [CommRing R]

/-
`RGplusSet` is the underlying set of `R₊^G` inside `R`,
and `extendedRGplus` is the extended ideal `R₊^G R ⊆ R`.
-/
variable (RGplusSet : Set R)
variable (extendedRGplus : Ideal R)

/-- Step 4:
If the extended ideal `R₊^G R` is generated by `RGplusSet`
and is finitely generated as an ideal of `R`,
then one can choose finitely many generators from `RGplusSet`. -/
theorem exists_generators_extendedRGplus_from_RGplus
    (hspan : Ideal.span RGplusSet = extendedRGplus)
    (hfg : extendedRGplus.FG) :
    ∃ s : Finset R,
      (∀ x ∈ s, x ∈ RGplusSet) ∧
      Ideal.span (↑s : Set R) = extendedRGplus := by
  classical
  have hfg_span_ideal : (Ideal.span RGplusSet).FG := by
    simpa [hspan] using hfg
  have hfg_span_submodule :
      (Submodule.span R RGplusSet : Submodule R R).FG := by
    exact hfg_span_ideal
  rcases
    (Submodule.fg_span_iff_fg_span_finset_subset
      (R := R) (M := R) RGplusSet).1 hfg_span_submodule
    with ⟨s, hs_sub, hs_span⟩
  refine ⟨s, ?_, ?_⟩
  · intro x hx
    exact hs_sub hx
  · calc
      Ideal.span (↑s : Set R) = Ideal.span RGplusSet := hs_span.symm
      _ = extendedRGplus := hspan

end RGplus_generators_S4


section RGplus_generators_S5

variable {k : Type u} [Field k]

variable {A : Type*} [CommRing A] [Algebra k A] [DecidableEq A]

variable {R : Type*} [CommRing R] [Algebra k R]

/-
`toR` is the inclusion `A → R`,
and `ρ` is the Reynolds operator `R → A`.

These imply `[Algebra A R]` and `[IsScalarTower k A R]`; we state them so that
`A →ₐ[k] R` and the ` comap` along `toR` elaborate as in the informal setup.
-/
variable [Algebra A R] [IsScalarTower k A R]
variable {toR : A →ₐ[k] R}
variable {ρ : R →ₗ[k] A}

/-
`RGplusA` is the ideal `R₊^G` in the fixed ring `A`,
and `extendedRGplus` is the ideal `R₊^G R` in `R`.
-/
variable {RGplusA : Ideal A}
variable {extendedRGplus : Ideal R}

/-
A finite set of generators chosen in Step 4.
-/
variable {s : Finset R}

/--
Step 5 spanning property (GIT Reynolds step).

If `toR f` lies in the `R`-ideal generated by `s`, then `f` lies in the `A`-ideal
generated by the Reynolds images `ρ(x)` for `x ∈ s`.

This implication is the genuine algebraic content of Step 5: one cannot derive it from
`ρ (toR a) = a` and `ρ ((toR a) * r) = a * ρ r` alone, because `toR f ∈ Ideal.span s`
only pins down an **R**-linear combination of `s`, and commuting `ρ` past arbitrary
`R`-coefficients needs the further Reynolds/graded input from your concrete setup.
Supply this when you instantiate `ρ` from averaging or a projector.
-/
def ReynoldsGITSpanProperty
    {k : Type u} [Field k]
    {A : Type*} [CommRing A] [Algebra k A] [DecidableEq A]
    {R : Type*} [CommRing R] [Algebra k R]
    (toR : A →ₐ[k] R) (ρ : R →ₗ[k] A) (s : Finset R) : Prop :=
  ∀ f : A,
    toR f ∈ Ideal.span (↑s : Set R) →
      f ∈ Ideal.span ↑(Finset.image (fun x => ρ x) s)

omit [Algebra A R] [IsScalarTower k A R] in
/-- Step 5 (membership form): elements of `RGplusA` lie in the `A`-ideal generated by `ρ '' s`.

Hypotheses:
- `hs_span`: `s` spans `extendedRGplus` as an ideal of `R`;
- `hcomap`: `RGplusA` is the preimage of `extendedRGplus` under `toR`;
- `hReynolds`: `ReynoldsGITSpanProperty` (your concrete GIT/Reynolds input).
-/
theorem mem_span_of_reynolds_generators
    (hs_span : Ideal.span (↑s : Set R) = extendedRGplus)
    (hcomap : RGplusA = Ideal.comap (toR : A →+* R) extendedRGplus)
    (hReynolds : ReynoldsGITSpanProperty toR ρ s)
    (f : A) (hf : f ∈ RGplusA) :
    f ∈ Ideal.span ↑(Finset.image (fun x => ρ x) s) := by
  refine hReynolds f ?_
  rw [hcomap] at hf
  exact hs_span ▸ Ideal.mem_comap.mp hf

omit [Algebra A R] [IsScalarTower k A R] in
/-- Step 5 (final finite generation): `RGplusA` is finitely generated.

Shows `RGplusA = Ideal.span (ρ '' s)` by antitone/submodule antisymmetry, then applies `Ideal.FG`.
-/
theorem RGplusA_fg_of_reynolds
    (hs_span : Ideal.span (↑s : Set R) = extendedRGplus)
    (hcomap : RGplusA = Ideal.comap (toR : A →+* R) extendedRGplus)
    (hρ_gen : ∀ x ∈ s, ρ x ∈ RGplusA)
    (hReynolds : ReynoldsGITSpanProperty toR ρ s) :
    RGplusA.FG := by
  classical
  let t : Finset A := Finset.image (fun x => ρ x) s
  refine ⟨t, ?_⟩
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    exact hρ_gen x hx
  · intro f hf
    exact mem_span_of_reynolds_generators hs_span hcomap hReynolds f hf

end RGplus_generators_S5

/- Step 5.5: Show that R has a Reynolds operator using our existence proof.

Since we have a linearly reductive group `G` acting on a `k`-module `R` by a locally
finite action, `R` admits a `Rep`-morphism projection onto the `G`-invariants. This is
just a re-export of `exists_reynolds_of_locallyFinite` from `GIT.ReynoldsOperator`, made
available under a name that matches the GIT step numbering. -/
theorem reynolds_operator_exists {k : Type u} [Field k] {G : Type u} [Group G]
    (hlr : IsLinearlyReductive k G)
    (R : Type u) [AddCommGroup R] [Module k R] [DistribMulAction G R] [SMulCommClass G k R]
    (hlf : Representation.IsLocallyFinite k G R) :
    ∃ π : Rep.of (Representation.ofDistribMulAction k G R) ⟶
            Rep.of (Representation.ofDistribMulAction k G R),
      LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants π.hom.hom :=
  exists_reynolds_of_locallyFinite (k := k) G hlr R hlf

section ReynoldsRewrite_S6

-- The `Algebra A R` / `IsScalarTower k A R` instances below are part of the
-- ambient Step-5 setup but are not used in the pure Reynolds-rewrite lemmas
-- here; silence the unused-section-variable linter for this blueprint.
set_option linter.unusedSectionVars false

variable (k : Type u) [Field k]
variable (G : Type v) [Group G]
-- `A` is (eventually) the invariant subalgebra `R^G`.
variable (A : Type*) [CommRing A] [Algebra k A]

-- `R` is the ambient ring.
variable (R : Type*) [CommRing R] [Algebra k R]
variable [Algebra A R] [IsScalarTower k A R]

-- Inclusion `A → R` of the fixed subalgebra into the ambient ring.
variable (toR : A →ₐ[k] R)

-- Reynolds operator `R → A`, assumed `k`-linear.
variable (ρ : R →ₗ[k] A)

-- A finite family `s` of elements of `R` (e.g. the generators chosen
-- in Step 4). Each element is assumed below to come from an element of `A`.
variable (s : Finset R)

-- Chosen lifts of elements of `s` to `A`.
-- The hypothesis `hlift x hx : toR (lift x) = x` witnesses that
-- `lift x` really is a preimage of `x` under `toR`.
variable (lift : R → A)

/-- **Step 6 (rewrite form).**

Suppose `f ∈ A` and upstairs in `R` we have written
  `toR f = ∑ x ∈ s, x * coeff x`
where each `x ∈ s` lifts to `lift x ∈ A` with `toR (lift x) = x`.

Applying the Reynolds operator `ρ` to both sides yields
  `f = ∑ x ∈ s, lift x * ρ (coeff x)`.

Proof outline:
1. Apply `ρ` to both sides of `hf`.
2. `ρ (toR f) = f`                        — by `hρ_id`.
3. `ρ (∑ x ∈ s, x * coeff x)
     = ∑ x ∈ s, ρ (x * coeff x)`          — by `LinearMap.map_sum` / `map_sum`.
4. For each `x ∈ s`, rewrite `x = toR (lift x)` and use the
   Reynolds compatibility `ρ (toR a * r) = a * ρ r`:
   `ρ (x * coeff x) = ρ (toR (lift x) * coeff x) = lift x * ρ (coeff x)`.
-/
local notation "Rᴳ₊" => A

theorem reynolds_rewrite
    (f : Rᴳ₊) (a_f : s → R)
    (hf : toR f = ∑ x ∈ s.attach, x.val * a_f x)
    (hlift : ∀ x ∈ s, toR (lift x) = x)
    (hρ_id : ∀ a : Rᴳ₊, ρ (toR a) = a)
    (hρ_mul : ∀ (a : Rᴳ₊) (r : R), ρ ((toR a) * r) = a * ρ r) :
    f = ∑ x ∈ s.attach, lift x.val * ρ (a_f x) := by
  -- (1) Apply ρ to both sides of `hf`:
  --     ρ (toR f) = ρ (∑ x ∈ s.attach, x.val * coeff x).
  have hρf : ρ (toR f) = ρ (∑ x ∈ s.attach, x.val * a_f x) := by
    rw [hf]
  -- (2) LHS collapses to `f` since `ρ` is the identity on the image of `toR`.
  rw [hρ_id] at hρf
  -- (3) `ρ` is `k`-linear, so it commutes with `Finset.sum`.
  rw [map_sum] at hρf
  -- Now `hρf : f = ∑ x ∈ s.attach, ρ (x.val * coeff x)`.
  rw [hρf]
  -- (4) Rewrite each summand using the lift and the Reynolds compatibility.
  refine Finset.sum_congr rfl ?_
  intro x hx
  -- Start from `ρ (toR (lift x.val) * coeff x) = lift x.val * ρ (coeff x)`
  -- (Reynolds compatibility), then use `toR (lift x.val) = x.val` to turn the
  -- LHS into `ρ (x.val * coeff x)`. Using the instantiated `hρ_mul` this way
  -- (rather than `rw [← hlift x.val x.property]` on the goal) avoids
  -- accidentally rewriting the `x.val` that appears inside `coeff x`.
  have hmul := hρ_mul (lift x.val) (a_f x)
  rw [hlift x.val x.property] at hmul
  exact hmul

/-- **Step 6 (ideal-membership form).**

Under the hypotheses of `reynolds_rewrite`, `f` lies in the ideal of `A`
generated by the chosen lifts `{ lift x | x ∈ s }`.

Proof outline:
• Use `reynolds_rewrite` to express `f = ∑ x ∈ s, lift x * ρ (coeff x)`.
• Each summand `lift x * ρ (coeff x)` is a multiple of the generator `lift x`,
  hence lies in `Ideal.span (lift '' s)`.
• A finite sum of ideal elements lies in the ideal (`Ideal.sum_mem`). -/
theorem mem_ideal_span_lift_of_reynolds
    (f : A) (coeff : s → R)
    (hf : toR f = ∑ x ∈ s.attach, x.val * coeff x)
    (hlift : ∀ x ∈ s, toR (lift x) = x)
    (hρ_id : ∀ a : A, ρ (toR a) = a)
    (hρ_mul : ∀ (a : A) (r : R), ρ ((toR a) * r) = a * ρ r) :
    f ∈ Ideal.span ((lift '' (s : Set R)) : Set A) := by
  -- Rewrite `f` as `∑ x ∈ s.attach, lift x.val * ρ (coeff x)` via Step 6.
  rw [reynolds_rewrite k A R toR ρ s lift f coeff hf hlift hρ_id hρ_mul]
  -- A finite sum of elements of an ideal lies in the ideal.
  refine Ideal.sum_mem _ ?_
  intro x hx
  -- `lift x.val * ρ (coeff x)` is a right-multiple of the generator `lift x.val`,
  -- and `lift x.val ∈ Ideal.span (lift '' s)` because `x.val ∈ s`.
  refine Ideal.mul_mem_right _ _ ?_
  refine Ideal.subset_span ?_
  exact Set.mem_image_of_mem lift x.property

/-- **Step 6 (ideal-generation corollary).**

If additionally every `f ∈ RGplusA` satisfies a presentation of the above
form (which is supplied by Steps 4–5), then `RGplusA` is contained in the
ideal of `A` generated by the lifts of the chosen generators.

This is the lemma that feeds into Step 7 (finite generation of `R₊^G`). -/
theorem RGplusA_le_span_lift_of_reynolds
    (RGplusA : Ideal A)
    (present : ∀ f ∈ RGplusA, ∃ coeff : s → R,
      toR f = ∑ x ∈ s.attach, x.val * coeff x)
    (hlift : ∀ x ∈ s, toR (lift x) = x)
    (hρ_id : ∀ a : A, ρ (toR a) = a)
    (hρ_mul : ∀ (a : A) (r : R), ρ ((toR a) * r) = a * ρ r) :
    RGplusA ≤ Ideal.span ((lift '' (s : Set R)) : Set A) := by
  -- Pointwise: pick the presentation given by `present`, then apply Step 6.
  intro f hf
  obtain ⟨coeff, hcoeff⟩ := present f hf
  exact mem_ideal_span_lift_of_reynolds k A R toR ρ s lift
    f coeff hcoeff hlift hρ_id hρ_mul

/-- Auxiliary: from membership in `Ideal.span (s : Set R)` extract a presentation
`x = ∑ t ∈ s.attach, t.val * coeff t` for some `coeff : s → R`. -/
lemma exists_finset_presentation_of_mem_span
    {R : Type*} [CommRing R] (s : Finset R) (x : R)
    (hx : x ∈ Ideal.span (↑s : Set R)) :
    ∃ coeff : s → R, x = ∑ t ∈ s.attach, t.val * coeff t := by
  classical
  -- View the ideal-span hypothesis as a submodule-span hypothesis.
  have hxsub : x ∈ (Submodule.span R (↑s : Set R) : Submodule R R) := by
    change x ∈ ((Ideal.span (↑s : Set R) : Ideal R) : Submodule R R)
    exact hx
  -- Induct on membership in the span. The motive does not depend on the
  -- membership proof, so we strip it via `fun y _ => _`.
  refine Submodule.span_induction
    (p := fun y _ => ∃ coeff : s → R, y = ∑ t ∈ s.attach, t.val * coeff t)
    ?mem ?zero ?add ?smul hxsub
  case mem =>
    -- Single generator: pick coefficient 1 on `y`, 0 elsewhere.
    intro y hy
    have hy_s : y ∈ s := by simpa using hy
    refine ⟨fun t => if t.val = y then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single (⟨y, hy_s⟩ : {a // a ∈ s})]
    · simp
    · intro b _ hb_ne
      have hbval : b.val ≠ y := fun heq => hb_ne (Subtype.ext heq)
      simp [hbval]
    · intro h; exact (h (Finset.mem_attach _ _)).elim
  case zero =>
    exact ⟨fun _ => 0, by simp⟩
  case add =>
    rintro a b _ _ ⟨ca, hca⟩ ⟨cb, hcb⟩
    refine ⟨fun t => ca t + cb t, ?_⟩
    rw [hca, hcb, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intros; ring
  case smul =>
    rintro r a _ ⟨ca, hca⟩
    refine ⟨fun t => r * ca t, ?_⟩
    rw [smul_eq_mul, hca, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intros; ring

/-- **Glue lemma (3): the Reynolds operator witnesses `ReynoldsGITSpanProperty`.**

If every `x ∈ s` lifts to some `lift x ∈ A` with `toR (lift x) = x`, and `ρ` is the
Reynolds operator (identity on `toR '' A` and Reynolds-multiplicative on
`toR a * r`), then `ReynoldsGITSpanProperty toR ρ s` holds.

Proof: from `toR f ∈ Ideal.span s` get a presentation
`toR f = ∑ x ∈ s.attach, x.val * coeff x`. Apply Step 6
(`mem_ideal_span_lift_of_reynolds`) to land in `Ideal.span (lift '' s)`. On `s`,
`ρ x = ρ (toR (lift x)) = lift x`, so this ideal equals `Ideal.span (ρ '' s)`.
-/
theorem reynoldsGITSpanProperty_of_reynolds
    [DecidableEq A]
    (hlift : ∀ x ∈ s, toR (lift x) = x)
    (hρ_id : ∀ a : A, ρ (toR a) = a)
    (hρ_mul : ∀ (a : A) (r : R), ρ ((toR a) * r) = a * ρ r) :
    ReynoldsGITSpanProperty toR ρ s := by
  classical
  intro f hf
  -- (a) Finite presentation of `toR f`.
  obtain ⟨coeff, hcoeff⟩ :=
    exists_finset_presentation_of_mem_span s (toR f) hf
  -- (b) Step 6: land in `Ideal.span (lift '' s)`.
  have hf_lift :
      f ∈ Ideal.span ((lift '' (s : Set R)) : Set A) :=
    mem_ideal_span_lift_of_reynolds k A R toR ρ s lift f coeff hcoeff hlift hρ_id hρ_mul
  -- (c) On `s`, `ρ x = lift x`.
  have hρ_eq_lift : ∀ x ∈ s, ρ x = lift x := by
    intro x hx
    have hxR : ρ (toR (lift x)) = lift x := hρ_id (lift x)
    have hxs : ρ x = ρ (toR (lift x)) := by rw [hlift x hx]
    rw [hxs, hxR]
  -- (d) `lift '' s = (Finset.image ρ s : Set A)`.
  have hsets :
      (lift '' (s : Set R)) =
        ((Finset.image (fun x => ρ x) s : Finset A) : Set A) := by
    ext a
    refine ⟨fun ⟨x, hxs, hax⟩ => ?_, fun ha => ?_⟩
    · refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, hxs, ?_⟩)
      rw [hρ_eq_lift x hxs, hax]
    · rcases Finset.mem_image.mp (Finset.mem_coe.mp ha) with ⟨x, hxs, rfl⟩
      exact ⟨x, hxs, (hρ_eq_lift x hxs).symm⟩
  rw [hsets] at hf_lift
  exact hf_lift

end ReynoldsRewrite_S6

/-! ## Glue (2): Rep-morphism → `(toR, ρ : R →ₗ[k] A)` translation interface

`reynolds_operator_exists` returns a `Rep`-morphism projection `π : Rep.of σ ⟶ Rep.of σ`
onto `σ.invariants`. Steps 5–6 are stated in terms of an abstract pair
`(toR : A →ₐ[k] R, ρ : R →ₗ[k] A)`. This section is a **purely mechanical** translator:
it codomain-restricts `π.hom.hom` to land in the invariants submodule, exposing the
`ρ` form expected by Steps 5–6. The `hρ_id` (Reynolds is identity on invariants) follows
from `IsProj.map_id`. The `hρ_mul` compatibility (Reynolds is `R^G`-linear on the right)
is **not** discharged here — it is a separate Reynolds-specific property.
-/

section RepProjectionToReynolds

variable {k : Type u} [Field k]
variable {G : Type u} [Group G]
variable {R : Type u}
variable [AddCommGroup R] [Module k R]
variable [DistribMulAction G R] [SMulCommClass G k R]

open Representation

/-- The codomain-restriction of the Rep-projection's underlying linear map to the
invariants submodule, exposing the `ρ : R →ₗ[k] ↥invariants` form. -/
noncomputable def reynoldsLinearToInvariants
    (π : Rep.of (Representation.ofDistribMulAction k G R) ⟶
          Rep.of (Representation.ofDistribMulAction k G R))
    (hπ : LinearMap.IsProj
            (Representation.ofDistribMulAction k G R).invariants π.hom.hom) :
    R →ₗ[k] ↥(Representation.ofDistribMulAction k G R).invariants :=
  LinearMap.codRestrict
    (Representation.ofDistribMulAction k G R).invariants
    π.hom.hom hπ.map_mem

/-- Reynolds is identity on invariants (the `hρ_id` hypothesis of Steps 5–6). -/
lemma reynoldsLinearToInvariants_apply_subtype
    (π : Rep.of (Representation.ofDistribMulAction k G R) ⟶
          Rep.of (Representation.ofDistribMulAction k G R))
    (hπ : LinearMap.IsProj
            (Representation.ofDistribMulAction k G R).invariants π.hom.hom)
    (a : ↥(Representation.ofDistribMulAction k G R).invariants) :
    reynoldsLinearToInvariants π hπ (a : R) = a := by
  apply Subtype.ext
  exact hπ.map_id (a : R) a.property

end RepProjectionToReynolds

/-
Step 7: Finite generation of `A = R^G` as a `k`-algebra.

This is the conclusion of the Hilbert finiteness argument. The previous steps
provide:

* (Step 5) The irrelevant ideal `R₊^G` of `A` is finitely generated as an ideal
  of `A` — `RGplusA_fg_of_reynolds`.
* (Step 1) `A` decomposes as `⨁ d, (𝒜 d ∩ A)`, i.e. `A` carries an `ℕ`-grading
  `𝒜G` inherited from `R` — `fixedSubalgebra_decomposes`.
* (Step 2) For any positively graded `k`-algebra whose irrelevant ideal is
  finitely generated and whose degree-`0` piece is finitely generated as a
  `k`-algebra, the whole algebra is finitely generated as a `k`-algebra —
  `finiteType_of_finitely_generated_irrelevant_ideal`.

Combining these gives `FiniteType k A`. In the GIT setting one typically has
`(𝒜G) 0 = k`, so the `FiniteType k ((𝒜G) 0)` hypothesis is automatic.
-/

section FixedSubalgebra_FiniteType_S7

variable (k : Type u) [Field k]
variable (R : Type*) [CommRing R] [Algebra k R]
variable (𝒜 : ℕ → Submodule k R) [GradedAlgebra 𝒜]

-- `A = R^G` together with its inherited `ℕ`-grading `𝒜G`.
variable (A : Type*) [CommRing A] [Algebra k A]
variable (𝒜G : ℕ → Submodule k A) [GradedAlgebra 𝒜G]

open Algebra HomogeneousIdeal

/-- **Step 7.**
The fixed subalgebra `A = R^G` is finitely generated as a `k`-algebra,
provided:

* its degree-`0` piece `(𝒜G) 0` is finitely generated as a `k`-algebra
  (automatic when `𝒜G 0 = k`), and
* its irrelevant ideal `R₊^G = ⨁_{d>0} (𝒜G) d` is finitely generated as an
  ideal of `A` — supplied by Step 5 (`RGplusA_fg_of_reynolds`). -/
theorem fixedSubalgebra_finiteType
    [FiniteType k (𝒜G 0)]
    (hfg : (irrelevant 𝒜G).toIdeal.FG) :
    FiniteType k A :=
  GIT.finiteType_k_of_finitely_generated_irrelevant_ideal
    (k := k) (R := A) (𝒜 := 𝒜G) hfg

end FixedSubalgebra_FiniteType_S7

/-!
## Main GIT theorem (Hilbert finiteness)

For a linearly reductive group `G` acting on a finitely generated `k`-algebra `R`,
the invariant subring `R^G` is finitely generated as a `k`-algebra.

The proof chains Steps 1–7:
* **Step 1** (`fixedSubalgebra_decomposes`): `R^G` inherits an `ℕ`-grading from `R`.
* **Step 5.5** (`reynolds_operator_exists`): from `IsLinearlyReductive` + `IsLocallyFinite`,
  obtain a Reynolds projection `R ↠ R^G`.
* **Steps 3–4** (`extendedRGplus_fg`, `exists_generators_extendedRGplus_from_RGplus`):
  the extended ideal `R₊^G · R` is f.g. (Noether) and admits generators chosen from `R₊^G`.
* **Step 5** (`RGplusA_fg_of_reynolds`): pushing generators back via Reynolds shows
  the irrelevant ideal of `R^G` is f.g.
* **Steps 2 & 7** (`finiteType_k_of_finitely_generated_irrelevant_ideal`,
  `fixedSubalgebra_finiteType`): a positively-graded `k`-algebra with f.g. irrelevant
  ideal and f.g. degree-0 piece is itself f.g. as a `k`-algebra.
-/

section GIT_MainTheorem

-- `k`, `G`, `R` share universe `u` so that `exists_reynolds_of_locallyFinite` applies.
variable (k : Type u) [Field k]
variable (G : Type u) [Group G]
variable (R : Type u) [CommRing R] [Algebra k R]

-- Action of `G` on `R` as a `DistribMulAction` (so the Reynolds machinery applies)
-- together with the bundled `k`-algebra-automorphism form `ρ` used in Step 1.
variable [DistribMulAction G R] [SMulCommClass G k R]
variable (ρ : G →* R ≃ₐ[k] R)

-- Compatibility: `ρ` is the action.
variable (hρ_compat : ∀ (g : G) (r : R), ρ g r = g • r)

-- The grading on `R`.
variable (𝒜 : ℕ → Submodule k R) [GradedAlgebra 𝒜]

-- The induced grading on `R^G`.
variable (𝒜G : ℕ → Submodule k (FixedSubalgebra (k := k) (G := G) (R := R) ρ))
  [GradedAlgebra 𝒜G]

open Algebra HomogeneousIdeal

/-- **Main GIT theorem.**

Let `G` be a linearly reductive group acting on a finitely generated `k`-algebra `R`
by `k`-algebra automorphisms, with the action preserving a chosen `ℕ`-grading on `R`
and being locally finite. Then the invariant subalgebra `R^G` is finitely generated
as a `k`-algebra.

Hypotheses:
* `hlr`     : `G` is linearly reductive over `k`.
* `hpres`   : the action `ρ` preserves the grading `𝒜`.
* `hlf`     : the underlying `k`-module action of `G` on `R` is locally finite.
* `[FiniteType k R]`        : `R` is finitely generated as a `k`-algebra.
* `[IsNoetherianRing R]`    : used in Step 3 to get `extendedRGplus.FG`.
* `[FiniteType k (𝒜G 0)]`   : the degree-`0` piece of `R^G` is f.g./k
  (automatic when `𝒜G 0 = k`).
-/
theorem GIT_finiteType_invariants
    [FiniteType k R]
    [IsNoetherianRing R]
    [FiniteType k (𝒜G 0)]
    (hlr : IsLinearlyReductive k G) (hρ_compat : ∀ (g : G) (r : R), ρ g r = g • r)
    (hlf : Representation.IsLocallyFinite k G R)
    (h𝒜G : ∀ (d : ℕ) (a : FixedSubalgebra (k := k) (G := G) (R := R) ρ),
      a ∈ 𝒜G d → (a : R) ∈ 𝒜 d) :
    FiniteType k (FixedSubalgebra (k := k) (G := G) (R := R) ρ) := by
  classical
  -- Step 5.5: Reynolds projection `π : R → R` (lands in `σ.invariants`).
  obtain ⟨π, hπ⟩ := reynolds_operator_exists (k := k) (G := G) hlr R hlf
  -- Step 7 reduction: it suffices to show the irrelevant ideal of `R^G` is f.g.
  refine fixedSubalgebra_finiteType (k := k)
    (A := FixedSubalgebra (k := k) (G := G) (R := R) ρ) (𝒜G := 𝒜G) ?_
  -- ── Setup ────────────────────────────────────────────────────────────────
  -- `A = R^G` as a `k`-subalgebra, plus inclusion `toR : A →ₐ[k] R`.
  let A : Subalgebra k R := FixedSubalgebra (k := k) (G := G) (R := R) ρ
  let toR : A →ₐ[k] R := A.val
  -- The irrelevant ideal of `A` and its extension to `R`.
  let RGplusA : Ideal A := (irrelevant 𝒜G).toIdeal
  change RGplusA.FG
  let extendedRGplus : Ideal R := Ideal.map (toR : A →+* R) RGplusA
  let RGplusSet : Set R := (toR : A → R) '' (RGplusA : Set A)
  -- ── Step 3: the extended ideal is f.g. (Noether) ─────────────────────────
  have h_ext_fg : extendedRGplus.FG :=
    extendedRGplus_fg (R := R) extendedRGplus
  -- ── Span property: `RGplusSet` ideal-spans `extendedRGplus` ──────────────
  have hspan_RG : Ideal.span RGplusSet = extendedRGplus := by
    change Ideal.span ((toR : A → R) '' (RGplusA : Set A)) = Ideal.map (toR : A →+* R) RGplusA
    rw [Ideal.map]; rfl
  -- ── Step 4: pick finitely many generators inside `RGplusSet` ─────────────
  obtain ⟨s, hs_sub, hs_span⟩ :=
    exists_generators_extendedRGplus_from_RGplus (R := R)
      RGplusSet extendedRGplus hspan_RG h_ext_fg
  -- ── Comap identification: `RGplusA = comap toR extendedRGplus` ──────────
  have htoR_inj : Function.Injective (toR : A →+* R) := Subtype.val_injective
  -- Compatibility of deg-0 components: the inclusion `A ↪ R` sends `(decompose 𝒜G a) 0`
  -- to `(decompose 𝒜 (toR a)) 0`. Proved by induction on the graded decomposition.
  have hdecomp0 : ∀ a : A,
      (((DirectSum.decompose 𝒜G a) 0 : A) : R) =
        ((DirectSum.decompose 𝒜 (toR a)) 0 : R) := fun a => by
    refine DirectSum.Decomposition.inductionOn (ℳ := 𝒜G)
      (motive := fun a => (((DirectSum.decompose 𝒜G a) 0 : A) : R) =
        ((DirectSum.decompose 𝒜 (toR a)) 0 : R)) ?_ ?_ ?_ a
    · simp
    · intro i m
      obtain ⟨c, hc⟩ := m
      have hcR : (c : R) ∈ 𝒜 i := h𝒜G i c hc
      change (((DirectSum.decompose 𝒜G (c : A)) 0 : A) : R) =
        ((DirectSum.decompose 𝒜 (toR (⟨c, hc⟩ : ↥(𝒜G i)))) 0 : R)
      have htoR_eq : toR (⟨c, hc⟩ : ↥(𝒜G i)) = (c : R) := rfl
      rw [htoR_eq]
      by_cases hi : i = 0
      · subst hi
        rw [DirectSum.decompose_of_mem_same 𝒜G hc,
            DirectSum.decompose_of_mem_same 𝒜 hcR]
      · rw [DirectSum.decompose_of_mem_ne 𝒜G hc hi,
            DirectSum.decompose_of_mem_ne 𝒜 hcR hi]
        simp
    · intro x y hx hy
      rw [DirectSum.decompose_add, DirectSum.add_apply,
          AddMemClass.coe_add, map_add, DirectSum.decompose_add, DirectSum.add_apply,
          AddMemClass.coe_add]
      push_cast
      rw [hx, hy]
  -- Each `a ∈ irrelevant 𝒜G` has `toR a ∈ irrelevant 𝒜` in `R`.
  have h_ext_le_irrR : extendedRGplus ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
    refine Ideal.map_le_iff_le_comap.mpr ?_
    intro a ha
    have h0A : ((DirectSum.decompose 𝒜G a) 0 : A) = 0 := by
      have hmem : a ∈ HomogeneousIdeal.irrelevant 𝒜G := ha
      have hp := (HomogeneousIdeal.mem_irrelevant_iff (𝒜 := 𝒜G) a).mp hmem
      simpa [GradedRing.proj_apply] using hp
    change toR a ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal
    change toR a ∈ HomogeneousIdeal.irrelevant 𝒜
    rw [HomogeneousIdeal.mem_irrelevant_iff]
    have hcompat := hdecomp0 a
    rw [h0A] at hcompat
    simp only [ZeroMemClass.coe_zero] at hcompat
    simpa [GradedRing.proj_apply] using hcompat.symm
  have hcomap : RGplusA = Ideal.comap (toR : A →+* R) extendedRGplus := by
    apply le_antisymm
    · exact Ideal.le_comap_map
    · intro x hx
      have htoR_x : toR x ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal := h_ext_le_irrR hx
      have h0R : ((DirectSum.decompose 𝒜 (toR x)) 0 : R) = 0 := by
        have hmem : toR x ∈ HomogeneousIdeal.irrelevant 𝒜 := htoR_x
        have hp := (HomogeneousIdeal.mem_irrelevant_iff (𝒜 := 𝒜) (toR x)).mp hmem
        simpa [GradedRing.proj_apply] using hp
      have hRA0 : (((DirectSum.decompose 𝒜G x) 0 : A) : R) = 0 := by
        rw [hdecomp0 x]; exact h0R
      have h0A : ((DirectSum.decompose 𝒜G x) 0 : A) = 0 := htoR_inj hRA0
      change x ∈ (HomogeneousIdeal.irrelevant 𝒜G).toIdeal
      change x ∈ HomogeneousIdeal.irrelevant 𝒜G
      rw [HomogeneousIdeal.mem_irrelevant_iff]
      simpa [GradedRing.proj_apply] using h0A
  -- ── Lifts: each `x ∈ s` comes from some element of `RGplusA ⊆ A` ─────────
  have lift_exists : ∀ x ∈ s, ∃ a : A, a ∈ RGplusA ∧ toR a = x := fun x hx => hs_sub x hx
  choose liftFn hliftFn_mem hliftFn_eq using lift_exists
  let lift : R → A := fun x => if hx : x ∈ s then liftFn x hx else 0
  have hlift : ∀ x ∈ s, toR (lift x) = x := fun x hx => by
    simp only [lift, dif_pos hx]; exact hliftFn_eq x hx
  -- ── Reynolds linear map `ρ_lin : R →ₗ[k] A` from the `Rep`-projection ─-─
  -- `π` lands in `σ.invariants`; via `hρ`, `σ.invariants = A.toSubmodule`, giving a
  -- `k`-linear map into `A`. The required identities (`hρ_id`, `hρ_mul`, `hρ_gen`)
  -- come from `IsProj` plus the `R^G`-multiplicativity bundled by Reynolds.
  have ρ_lin_data :
      ∃ ρ_lin : R →ₗ[k] A,
        (∀ a : A, ρ_lin (toR a) = a) ∧
        (∀ (a : A) (r : R), ρ_lin ((toR a) * r) = a * ρ_lin r) ∧
        (∀ x ∈ s, ρ_lin x ∈ RGplusA) := by
    -- Build `MulSemiringAction G R` from `ρ` + `hρ`, then invoke the multiplicativity
    -- variant of Reynolds existence to get a Reynolds projection that is also
    -- `R^G`-multiplicative.
    letI : MulSemiringAction G R :=
      { (inferInstance : DistribMulAction G R) with
        smul_one := fun g => by
          rw [show g • (1 : R) = ρ g 1 from (hρ_compat g 1).symm]; exact map_one (ρ g)
        smul_mul := fun g a b => by
          rw [show g • (a * b) = ρ g (a * b) from (hρ_compat g (a * b)).symm,
              show g • a = ρ g a from (hρ_compat g a).symm,
              show g • b = ρ g b from (hρ_compat g b).symm]
          exact map_mul (ρ g) a b }
    obtain ⟨π', hπ'_proj, hπ'_mul⟩
      := exists_reynolds_mul_compat_of_locallyFinite (k := k) (G := G) hlr R hlf
    -- `σ.invariants` and `A` have the same underlying set via `hρ`.
    have h_inv_to_A : ∀ r : R,
        r ∈ (Representation.ofDistribMulAction k G R).invariants → r ∈ A := by
      intro r hr g
      rw [hρ_compat]
      exact ((Representation.ofDistribMulAction k G R).mem_invariants r).mp hr g
    have h_A_to_inv : ∀ r : R,
        r ∈ A → r ∈ (Representation.ofDistribMulAction k G R).invariants := by
      intro r hr
      rw [Representation.mem_invariants]
      intro g
      change g • r = r
      rw [← hρ_compat]; exact hr g
    have hπ'_to_A : ∀ r : R, π'.hom.hom r ∈ A.toSubmodule := fun r =>
      h_inv_to_A _ (hπ'_proj.map_mem r)
    let ρ_lin : R →ₗ[k] A :=
      LinearMap.codRestrict A.toSubmodule π'.hom.hom hπ'_to_A
    refine ⟨ρ_lin, ?_, ?_, ?_⟩
    · -- ρ_lin (toR a) = a
      intro a
      apply Subtype.ext
      change π'.hom.hom (a : R) = (a : R)
      exact hπ'_proj.map_id (a : R) (h_A_to_inv (a : R) a.property)
    · -- ρ_lin ((toR a) * r) = a * ρ_lin r
      intro a r
      apply Subtype.ext
      change π'.hom.hom ((a : R) * r) = (a : R) * π'.hom.hom r
      exact hπ'_mul (h_A_to_inv (a : R) a.property) r
    · -- ρ_lin x ∈ RGplusA for x ∈ s
      intro x hx
      obtain ⟨a, ha_mem, ha_eq⟩ := hs_sub x hx
      have h_eq : ρ_lin x = a := by
        rw [show x = toR a from ha_eq.symm]
        apply Subtype.ext
        change π'.hom.hom (a : R) = (a : R)
        exact hπ'_proj.map_id (a : R) (h_A_to_inv (a : R) a.property)
      rw [h_eq]; exact ha_mem
  obtain ⟨ρ_lin, hρ_id, hρ_mul, hρ_gen⟩ := ρ_lin_data
  -- ── Step 6 glue: `ReynoldsGITSpanProperty toR ρ_lin s` ───────────────────
  have hReynolds : ReynoldsGITSpanProperty toR ρ_lin s :=
    reynoldsGITSpanProperty_of_reynolds (k := k) A R toR ρ_lin s lift hlift hρ_id hρ_mul
  -- ── Step 5: assemble — `RGplusA.FG` ──────────────────────────────────────
  exact RGplusA_fg_of_reynolds (k := k) (A := A) (R := R)
    (toR := toR) (ρ := ρ_lin) (s := s)
    (RGplusA := RGplusA) (extendedRGplus := extendedRGplus)
    hs_span hcomap hρ_gen hReynolds

end GIT_MainTheorem
