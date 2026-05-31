import Mathlib.Algebra.Ring.Action.Group
import Mathlib.Algebra.Ring.Action.Invariant
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-!
# Inherited grading on the invariant subalgebra

When `G` acts on a graded `k`-algebra `R` by *grading-preserving* `k`-algebra automorphisms,
the invariant subalgebra `R^G` inherits the grading: `R^G = ⨁_d (𝒜 d ∩ R^G)`.

## Main definitions

* `GIT.PreservesGrading G 𝒜` — every `g : G` preserves each homogeneous piece `𝒜 d`.
* `GIT.FixedSubalgebra k G R` — the invariant subalgebra `R^G`.
* `GIT.FixedPieceInFixedSubalgebra G 𝒜 d` — the degree-`d` piece in `R^G`.

## Main result

* `GIT.fixedSubalgebra_decomposes` — the internal direct-sum decomposition
  `R^G = ⨁_d (FixedPieceInFixedSubalgebra G 𝒜 d)`.
-/

open scoped DirectSum

universe u v w

namespace GIT

variable {k : Type u} [Field k]
variable (G : Type v) [Group G]
variable {ι : Type w} [DecidableEq ι] [AddMonoid ι]
variable {R : Type*} [Semiring R] [Algebra k R]
variable (𝒜 : ι → Submodule k R) [GradedAlgebra 𝒜]
variable [MulSemiringAction G R] [SMulCommClass G k R]

/-- **Grading-preservation hypothesis.** Every group element maps each homogeneous piece into
itself: `∀ g d r, r ∈ 𝒜 d → g • r ∈ 𝒜 d`. -/
def PreservesGrading : Prop :=
  ∀ (g : G) (d : ι) {r : R}, r ∈ 𝒜 d → g • r ∈ 𝒜 d

/-- **The invariant subalgebra `R^G`.** Carrier `{r | ∀ g, g • r = r}`, closed under the
algebra operations because `g` acts as a ring/algebra homomorphism. -/
def FixedSubalgebra (k : Type u) [Field k] (G : Type v) [Group G]
    (R : Type*) [Semiring R] [Algebra k R] [MulSemiringAction G R]
    [SMulCommClass G k R] : Subalgebra k R where
  carrier := { r : R | ∀ g : G, g • r = r }
  zero_mem' g := smul_zero g
  one_mem' g := smul_one g
  add_mem' hx hy g := by simp [smul_add, hx g, hy g]
  mul_mem' hx hy g := by simp [smul_mul', hx g, hy g]
  algebraMap_mem' a g := smul_algebraMap g a

/-- **The degree-`d` piece in `R^G`.** Carrier `{x : R^G | (x : R) ∈ 𝒜 d}`, with the obvious
`k`-submodule structure inherited from `𝒜 d`. -/
def FixedPieceInFixedSubalgebra (d : ι) :
    Submodule k (FixedSubalgebra k G R) where
  carrier := { x | (x : R) ∈ 𝒜 d }
  zero_mem' := Submodule.zero_mem (𝒜 d)
  add_mem' hx hy := Submodule.add_mem (𝒜 d) hx hy
  smul_mem' a _ hx := Submodule.smul_mem (𝒜 d) a hx

/-- The `d`-component of `(x : R)` (for `x ∈ R^G`) lies in `𝒜 d`. -/
lemma fixed_component_mem_degree
    (x : FixedSubalgebra k G R) (d : ι) :
    ((DirectSum.decompose 𝒜 (x : R)) d : R) ∈ 𝒜 d :=
  ((DirectSum.decompose 𝒜 (x : R)) d).property

/-- **Same-degree case of `proj_commutes_of_preservesGrading`.** If `y ∈ 𝒜 d` and `g • y ∈ 𝒜 d`,
projecting and applying `g` commute on `y`. -/
private lemma proj_commutes_same
    (hpres : PreservesGrading G 𝒜) (g : G) (d : ι) (y : 𝒜 d) :
    ↑(((DirectSum.decompose 𝒜) ((DistribSMul.toLinearMap k R g) (y : R))) d) =
      (DistribSMul.toLinearMap k R g) (↑(((DirectSum.decompose 𝒜) (y : R)) d)) := by
  have hyρ : (DistribSMul.toLinearMap k R g) (y : R) ∈ 𝒜 d := by
    simpa using hpres g d y.property
  rw [DirectSum.decompose_of_mem_same 𝒜 hyρ,
      DirectSum.decompose_of_mem_same 𝒜 y.property]

/-- **Different-degree case of `proj_commutes_of_preservesGrading`.** -/
private lemma proj_commutes_ne
    (hpres : PreservesGrading G 𝒜) (g : G) (d e : ι) (y : 𝒜 e) (h : e ≠ d) :
    ↑(((DirectSum.decompose 𝒜) ((DistribSMul.toLinearMap k R g) (y : R))) d) =
      (DistribSMul.toLinearMap k R g) (↑(((DirectSum.decompose 𝒜) (y : R)) d)) := by
  have hyρ : (DistribSMul.toLinearMap k R g) (y : R) ∈ 𝒜 e := by
    simpa using hpres g e y.property
  rw [DirectSum.decompose_of_mem_ne 𝒜 hyρ h,
      DirectSum.decompose_of_mem_ne 𝒜 y.property h]
  simp

/-- **`g`-action commutes with the degree-`d` projection** when `g` preserves the grading.

Math statement: `(GradedAlgebra.proj 𝒜 d).comp (g •ₗ ·) = (g •ₗ ·).comp (GradedAlgebra.proj 𝒜 d)`.

Proof idea: by `DirectSum.decompose_lhom_ext`, it suffices to check on each piece `𝒜 e`;
split into `e = d` (same-degree case) and `e ≠ d` (vanishing case). -/
lemma proj_commutes_of_preservesGrading
    (hpres : PreservesGrading G 𝒜)
    (g : G) (d : ι) :
    (GradedAlgebra.proj 𝒜 d).comp (DistribSMul.toLinearMap k R g) =
      (DistribSMul.toLinearMap k R g).comp (GradedAlgebra.proj 𝒜 d) := by
  refine DirectSum.decompose_lhom_ext 𝒜 (fun e => ?_)
  ext y
  by_cases h : e = d
  · subst d; exact proj_commutes_same G 𝒜 hpres g e y
  · exact proj_commutes_ne G 𝒜 hpres g d e y h

/-- **Components of invariants are invariant.** For `x ∈ R^G`, every `(decompose 𝒜 x) d`
lies in `R^G`.

Proof idea: `g • (proj_d x) = proj_d (g • x) = proj_d x` by orbit-preservation of `proj` and
invariance of `x`. -/
lemma fixed_component_is_fixed
    (hpres : PreservesGrading G 𝒜)
    (x : FixedSubalgebra k G R) (d : ι) :
    ((DirectSum.decompose 𝒜 (x : R)) d : R) ∈
      (FixedSubalgebra k G R).toSubmodule := by
  intro g
  have hlin := proj_commutes_of_preservesGrading G 𝒜 hpres g d
  have hcomm : GradedAlgebra.proj 𝒜 d ((DistribSMul.toLinearMap k R g) (x : R)) =
      (DistribSMul.toLinearMap k R g) (GradedAlgebra.proj 𝒜 d (x : R)) := by
    simpa [LinearMap.comp_apply] using congrArg (fun F : R →ₗ[k] R => F (x : R)) hlin
  have hxfix : (DistribSMul.toLinearMap k R g) (x : R) = (x : R) := by simpa using x.property g
  rw [hxfix] at hcomm
  simpa [GradedAlgebra.proj_apply] using hcomm.symm

/-- The "forget" map `FixedPieceInFixedSubalgebra G 𝒜 d → 𝒜 d`. -/
def fixedPieceForget (d : ι) :
    FixedPieceInFixedSubalgebra G 𝒜 d →+ 𝒜 d where
  toFun x := ⟨((x : FixedSubalgebra k G R) : R), x.property⟩
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl

omit [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜] in
/-- `fixedPieceForget` is injective. -/
lemma fixedPieceForget_injective (d : ι) :
    Function.Injective (fixedPieceForget G 𝒜 d) := fun _ _ h =>
  Subtype.ext (Subtype.ext (congrArg (fun z : 𝒜 d => (z : R)) h))

/-- **Injectivity** of `DirectSum.coeAddMonoidHom B` for `B d = FixedPieceInFixedSubalgebra G 𝒜 d`.

Proof idea: the coercion `R^G ↪ R` makes the square `coeFixed ∘ coeAddMonoidHom B =
(coeAddMonoidHom 𝒜) ∘ (map fixedPieceForget)` commute. Chasing this square reduces injectivity
of `coeAddMonoidHom B` to injectivity of `coeAddMonoidHom 𝒜` (from `Decomposition.isInternal 𝒜`)
combined with injectivity of `DirectSum.map fixedPieceForget`. -/
private lemma decomposes_injective
    (a b : DirectSum ι (fun d => FixedPieceInFixedSubalgebra G 𝒜 d))
    (h : DirectSum.coeAddMonoidHom (fun d => FixedPieceInFixedSubalgebra G 𝒜 d) a =
        DirectSum.coeAddMonoidHom (fun d => FixedPieceInFixedSubalgebra G 𝒜 d) b) :
    a = b := by
  let coeFixed : FixedSubalgebra k G R →+ R :=
    { toFun := fun x => (x : R), map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hcomp : coeFixed.comp (DirectSum.coeAddMonoidHom
        (fun d => FixedPieceInFixedSubalgebra G 𝒜 d)) =
      (DirectSum.coeAddMonoidHom 𝒜).comp
        (DirectSum.map (fun d => fixedPieceForget G 𝒜 d)) := by
    apply DirectSum.addHom_ext; intro i y; simp [coeFixed, fixedPieceForget]
  let forget : (d : ι) → FixedPieceInFixedSubalgebra G 𝒜 d →+ 𝒜 d :=
    fun d => fixedPieceForget G 𝒜 d
  have hR : (DirectSum.coeAddMonoidHom 𝒜) (DirectSum.map forget a) =
      (DirectSum.coeAddMonoidHom 𝒜) (DirectSum.map forget b) := by
    have ha := DFunLike.congr_fun hcomp a
    have hb := DFunLike.congr_fun hcomp b
    simp only [AddMonoidHom.coe_comp, Function.comp_apply] at ha hb
    rw [← ha, ← hb]; exact congrArg coeFixed h
  exact ((DirectSum.map_injective _).2 (fun d => fixedPieceForget_injective G 𝒜 d))
    ((DirectSum.Decomposition.isInternal 𝒜).1 hR)

/-- **Surjectivity witness:** for `x ∈ R^G`, the dependent sum whose `d`-component is
`⟨(decompose 𝒜 (x : R)) d, …⟩`, supported on the same finite set. -/
private noncomputable def decomposesWitness
    (hpres : PreservesGrading G 𝒜) (x : FixedSubalgebra k G R) :
    DirectSum ι (fun d => FixedPieceInFixedSubalgebra G 𝒜 d) := by
  classical
  exact (DirectSum.mk (fun d => FixedPieceInFixedSubalgebra G 𝒜 d)
    ((DirectSum.decompose 𝒜 (x : R)).support))
    (fun d => ⟨⟨((DirectSum.decompose 𝒜 (x : R)) d.1 : R),
      fixed_component_is_fixed G 𝒜 hpres x d.1⟩,
      fixed_component_mem_degree G 𝒜 x d.1⟩)

/-- **Push-forward of the witness equals the original `R`-decomposition.** -/
private lemma decomposesWitness_map_forget
    (hpres : PreservesGrading G 𝒜) (x : FixedSubalgebra k G R) :
    DirectSum.map (fun d => fixedPieceForget G 𝒜 d) (decomposesWitness G 𝒜 hpres x) =
      DirectSum.decompose 𝒜 (x : R) := by
  classical
  ext d
  by_cases hd : d ∈ (DirectSum.decompose 𝒜 (x : R)).support
  · rw [DirectSum.map_apply, decomposesWitness, DirectSum.mk_apply_of_mem hd]
    simp [fixedPieceForget]
  · rw [DirectSum.map_apply, decomposesWitness, DirectSum.mk_apply_of_notMem hd,
      DFinsupp.notMem_support_iff.mp hd]
    simp

/-- **Surjectivity** of `DirectSum.coeAddMonoidHom B`: the witness `decomposesWitness x`
maps to `x` under the assembled inclusion. Chase the same square as in `decomposes_injective`
to reduce to `DirectSum.Decomposition.left_inv` applied to `(x : R)`. -/
private lemma decomposes_surjective
    (hpres : PreservesGrading G 𝒜) (x : FixedSubalgebra k G R) :
    ∃ y, DirectSum.coeAddMonoidHom
        (fun d => FixedPieceInFixedSubalgebra G 𝒜 d) y = x := by
  refine ⟨decomposesWitness G 𝒜 hpres x, ?_⟩
  apply Subtype.ext
  let coeFixed : FixedSubalgebra k G R →+ R :=
    { toFun := fun x => (x : R), map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hcomp : coeFixed.comp (DirectSum.coeAddMonoidHom
        (fun d => FixedPieceInFixedSubalgebra G 𝒜 d)) =
      (DirectSum.coeAddMonoidHom 𝒜).comp
        (DirectSum.map (fun d => fixedPieceForget G 𝒜 d)) := by
    apply DirectSum.addHom_ext; intro i y; simp [coeFixed, fixedPieceForget]
  have hyR := DFunLike.congr_fun hcomp (decomposesWitness G 𝒜 hpres x)
  simp only [AddMonoidHom.coe_comp, Function.comp_apply] at hyR
  rw [show ((DirectSum.coeAddMonoidHom (fun d => FixedPieceInFixedSubalgebra G 𝒜 d))
      (decomposesWitness G 𝒜 hpres x) : R) = _ from hyR,
    decomposesWitness_map_forget G 𝒜 hpres x]
  exact DirectSum.Decomposition.left_inv (ℳ := 𝒜) (x : R)

/-- **Inherited grading on `R^G`.** Under grading-preservation, the invariant subalgebra `R^G`
is the internal direct sum of the pieces `FixedPieceInFixedSubalgebra G 𝒜 d = 𝒜 d ∩ R^G`.

Math statement: `DirectSum.IsInternal (fun d => FixedPieceInFixedSubalgebra G 𝒜 d)`.

Proof idea: `IsInternal` unfolds to `Bijective (coeAddMonoidHom B)`. Injectivity is
`decomposes_injective`; surjectivity is `decomposes_surjective`. -/
theorem fixedSubalgebra_decomposes
    (hpres : PreservesGrading G 𝒜) :
    DirectSum.IsInternal
      (fun d : ι => FixedPieceInFixedSubalgebra G 𝒜 d) := by
  change Function.Bijective ⇑(DirectSum.coeAddMonoidHom _)
  exact ⟨fun a b => decomposes_injective G 𝒜 a b, decomposes_surjective G 𝒜 hpres⟩

end GIT
