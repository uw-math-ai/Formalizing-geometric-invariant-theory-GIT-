import Mathlib.Algebra.Ring.Action.Group
import Mathlib.Algebra.Ring.Action.Invariant
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Maps
import GIT.ReynoldsOperator

/-!
# Hilbert finiteness for geometric invariant theory

Let a linearly reductive group `G` act on a finitely generated `ℕ`-graded `k`-algebra `R` by
grading-preserving `k`-algebra automorphisms, with the action locally finite. This file proves
that the invariant subalgebra `R^G` is again finitely generated as a `k`-algebra.

## Main result

* `GIT_finiteType_invariants`: `R^G` is of finite type over `k`.

## Strategy

The proof assembles four ingredients, one per section below.

* **A. Inherited grading.** `R^G` inherits the grading of `R`, i.e.
  `R^G = ⨁ d, (𝒜 d ∩ R^G)` (`fixedSubalgebra_decomposes`).
* **B. Finite generation from the irrelevant ideal.** A graded algebra whose irrelevant ideal is
  finitely generated is of finite type over its degree-`0` piece, hence over `k`
  (`finiteType_k_of_finitely_generated_irrelevant_ideal`, `fixedSubalgebra_finiteType`).
* **C. Reynolds ideal machinery.** Using a Reynolds projection `ρ : R → R^G`, the irrelevant ideal
  of `R^G` is finitely generated as an ideal of `R^G` (`RGplusA_fg_of_reynolds`).
* **D. Assembly.** Combining the above with the multiplicative Reynolds projection from
  `GIT.ReynoldsOperator` yields the main theorem.
-/

open scoped DirectSum
open scoped BigOperators

universe u v w uR

namespace GIT

/-! ## A. Inherited grading on the invariant subalgebra -/

section InheritedGrading

-- Basic objects

variable {k : Type u} [Field k]
variable (G : Type v) [Group G]
variable {ι : Type w} [DecidableEq ι] [AddMonoid ι]
variable {R : Type*} [Semiring R] [Algebra k R]
variable (𝒜 : ι → Submodule k R)

-- Grading on R

variable [GradedAlgebra 𝒜]

-- Group action by ring/algebra automorphisms via a `MulSemiringAction`.
-- `MulSemiringAction G R` extends `DistribMulAction` and bundles `smul_one`, `smul_mul`;
-- combined with `SMulCommClass G k R` it captures exactly "action by `k`-algebra automorphisms".

variable [MulSemiringAction G R] [SMulCommClass G k R]

-- The grading-preservation hypothesis

def PreservesGrading : Prop :=
  ∀ (g : G) (d : ι) {r : R}, r ∈ 𝒜 d → g • r ∈ 𝒜 d

-- The invariant subalgebra R^G

def FixedSubalgebra (k : Type u) [Field k] (G : Type v) [Group G]
    (R : Type*) [Semiring R] [Algebra k R] [MulSemiringAction G R]
    [SMulCommClass G k R] : Subalgebra k R where
  carrier := { r : R | ∀ g : G, g • r = r }
  zero_mem' g := smul_zero g
  one_mem' g := smul_one g
  add_mem' hx hy g := by simp [smul_add, hx g, hy g]
  mul_mem' hx hy g := by simp [smul_mul', hx g, hy g]
  algebraMap_mem' a g := smul_algebraMap g a

-- Degree-d piece in R^G

def FixedPieceInFixedSubalgebra (d : ι) :
    Submodule k (FixedSubalgebra k G R) where
  carrier := { x | (x : R) ∈ 𝒜 d }
  zero_mem' := Submodule.zero_mem (𝒜 d)
  add_mem' hx hy := Submodule.add_mem (𝒜 d) hx hy
  smul_mem' a _ hx := Submodule.smul_mem (𝒜 d) a hx

-- Auxiliary lemma
lemma fixed_component_mem_degree
    (x : FixedSubalgebra k G R) (d : ι) :
    ((DirectSum.decompose 𝒜 (x : R)) d : R) ∈ 𝒜 d :=
  ((DirectSum.decompose 𝒜 (x : R)) d).property

lemma proj_commutes_of_preservesGrading
    (hpres : PreservesGrading G 𝒜)
    (g : G) (d : ι) :
    (GradedAlgebra.proj 𝒜 d).comp (DistribSMul.toLinearMap k R g) =
      (DistribSMul.toLinearMap k R g).comp (GradedAlgebra.proj 𝒜 d) := by
  refine DirectSum.decompose_lhom_ext 𝒜 (fun e => ?_)
  ext y
  have hyρ : (DistribSMul.toLinearMap k R g) (y : R) ∈ 𝒜 e := by
    simpa using hpres g e y.property
  by_cases h : e = d
  · subst d
    change ↑(((DirectSum.decompose 𝒜) ((DistribSMul.toLinearMap k R g) (y : R))) e) =
        (DistribSMul.toLinearMap k R g) (↑(((DirectSum.decompose 𝒜) (y : R)) e))
    rw [DirectSum.decompose_of_mem_same 𝒜 hyρ,
        DirectSum.decompose_of_mem_same 𝒜 y.property]
  · change ↑(((DirectSum.decompose 𝒜) ((DistribSMul.toLinearMap k R g) (y : R))) d) =
        (DistribSMul.toLinearMap k R g) (↑(((DirectSum.decompose 𝒜) (y : R)) d))
    rw [DirectSum.decompose_of_mem_ne 𝒜 hyρ h,
        DirectSum.decompose_of_mem_ne 𝒜 y.property h]
    simp

lemma fixed_component_is_fixed
    (hpres : PreservesGrading G 𝒜)
    (x : FixedSubalgebra k G R)
    (d : ι) :
    ((DirectSum.decompose 𝒜 (x : R)) d : R) ∈
      (FixedSubalgebra k G R).toSubmodule := by
  intro g
  have hlin :
      (GradedAlgebra.proj 𝒜 d).comp (DistribSMul.toLinearMap k R g) =
        (DistribSMul.toLinearMap k R g).comp (GradedAlgebra.proj 𝒜 d) :=
    proj_commutes_of_preservesGrading
      G 𝒜
      hpres g d
  have hcomm :
      GradedAlgebra.proj 𝒜 d ((DistribSMul.toLinearMap k R g) (x : R)) =
        (DistribSMul.toLinearMap k R g) (GradedAlgebra.proj 𝒜 d (x : R)) := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun F : R →ₗ[k] R => F (x : R)) hlin
  have hxfix : (DistribSMul.toLinearMap k R g) (x : R) = (x : R) := by
    simpa using x.property g
  rw [hxfix] at hcomm
  simpa [GradedAlgebra.proj_apply] using hcomm.symm

-- Forget map
def fixedPieceForget (d : ι) :
    FixedPieceInFixedSubalgebra
      G 𝒜 d →+ 𝒜 d where
  toFun x := ⟨((x : FixedSubalgebra k G R) : R), x.property⟩
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl

omit [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜] in
lemma fixedPieceForget_injective (d : ι) :
    Function.Injective
      (fixedPieceForget
        G 𝒜 d) := fun _ _ h =>
  Subtype.ext (Subtype.ext (congrArg (fun z : 𝒜 d => (z : R)) h))


-- Direct-sum decomposition of R^G: R^G = ⨁ d, (R_d ∩ R^G)

theorem fixedSubalgebra_decomposes
    (hpres : PreservesGrading G 𝒜) :
    DirectSum.IsInternal
      fun d : ι =>
        FixedPieceInFixedSubalgebra
          G 𝒜 d := by
  classical
  let B : ι → Submodule k (FixedSubalgebra k G R) :=
    fun d =>
      FixedPieceInFixedSubalgebra
        G 𝒜 d
  let forget : (d : ι) → B d →+ 𝒜 d :=
    fun d =>
      fixedPieceForget
        G 𝒜 d
  let coeFixed : FixedSubalgebra k G R →+ R := {
    toFun := fun x => (x : R)
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
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
        coeFixed ((DirectSum.coeAddMonoidHom B) b) :=
      congrArg (fun z : FixedSubalgebra k G R => coeFixed z) h
    have ha :
        coeFixed ((DirectSum.coeAddMonoidHom B) a)
          =
        (DirectSum.coeAddMonoidHom 𝒜) ((DirectSum.map forget) a) :=
      congrArg (fun F : (DirectSum ι fun d => B d) →+ R => F a) hcomp
    have hb :
        coeFixed ((DirectSum.coeAddMonoidHom B) b)
          =
        (DirectSum.coeAddMonoidHom 𝒜) ((DirectSum.map forget) b) :=
      congrArg (fun F : (DirectSum ι fun d => B d) →+ R => F b) hcomp
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
            G 𝒜 d))
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
                G 𝒜
                hpres x d.1
            ⟩,
            fixed_component_mem_degree
              G 𝒜
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
                    G 𝒜
                    hpres x d
                ⟩,
                fixed_component_mem_degree
                  G 𝒜
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
        (DirectSum.coeAddMonoidHom 𝒜) ((DirectSum.map forget) y) :=
      congrArg (fun F : (DirectSum ι fun d => B d) →+ R => F y) hcomp
    calc
      coeFixed ((DirectSum.coeAddMonoidHom B) y)
          =
        (DirectSum.coeAddMonoidHom 𝒜) ((DirectSum.map forget) y) := hyR
      _ =
        (DirectSum.coeAddMonoidHom 𝒜) (DirectSum.decompose 𝒜 (x : R)) := by
          rw [hy_decomp]
      _ = (x : R) := DirectSum.Decomposition.left_inv (ℳ := 𝒜) (x : R)

end InheritedGrading

/-! ## B. Finite generation of a graded algebra from its irrelevant ideal -/

section GradedAlgebraFiniteType

/-! If `R₊` is finitely generated as an ideal, then `R` is finitely generated as an algebra over
the degree-`0` graded piece `𝒜 0`. To conclude finite generation over the base field `k`, one
still needs a separate hypothesis that `𝒜 0` is finitely generated as a `k`-algebra (then apply
transitivity); that extra hypothesis cannot be dropped in general. -/

section

variable {k : Type u} [Field k]
variable {R : Type uR} [CommRing R] [Algebra k R]
variable {𝒜 : ℕ → Submodule k R} [GradedAlgebra 𝒜]

abbrev irrelevantIdeal : Ideal R := (HomogeneousIdeal.irrelevant 𝒜).toIdeal

lemma exists_finset_homogeneous_pos_generators
    (h : (irrelevantIdeal (𝒜 := 𝒜)).FG) :
    ∃ T : Finset R,
      (Ideal.span (T : Set R) = irrelevantIdeal (𝒜 := 𝒜)) ∧
      (∀ t ∈ T, ∃ d : ℕ, 0 < d ∧ t ∈ 𝒜 d) := by
  classical
  let s : Set R := ⋃ i : ℕ, ⋃ _ : 0 < i, (𝒜 i : Set R)
  have hirr : irrelevantIdeal (𝒜 := 𝒜) = Ideal.span s := by
    simpa [irrelevantIdeal, s] using (HomogeneousIdeal.irrelevant_eq_span (𝒜 := 𝒜))
  have hspan_s_fg : (Ideal.span s : Ideal R).FG := by
    rcases h with ⟨S, hS⟩
    refine ⟨S, ?_⟩
    calc
      Ideal.span (S : Set R)
          = irrelevantIdeal (𝒜 := 𝒜) := hS
      _   = Ideal.span s := hirr
  have hfg_submodule : (Submodule.span R s).FG := by
    rcases hspan_s_fg with ⟨S, hS⟩
    exact ⟨S, congrArg (fun (I : Ideal R) => (I : Submodule R R)) hS⟩
  rcases (Submodule.fg_span_iff_fg_span_finset_subset (R := R) (M := R) s).1 hfg_submodule with
    ⟨T, hTs, hspan⟩
  refine ⟨T, ?_, ?_⟩
  · have : Ideal.span s = Ideal.span (T : Set R) :=
      congrArg (fun (N : Submodule R R) => (N : Ideal R)) hspan
    calc
      Ideal.span (T : Set R) = Ideal.span s := this.symm
      _ = irrelevantIdeal (𝒜 := 𝒜) := hirr.symm
  · intro t ht
    have : t ∈ s := hTs (by simpa using ht)
    rcases Set.mem_iUnion.1 this with ⟨d, hd⟩
    rcases Set.mem_iUnion.1 hd with ⟨hdpos, hmem⟩
    exact ⟨d, hdpos, hmem⟩

noncomputable def inst_algebra_degreeZero :
    Algebra (𝒜 0) R := inferInstance

noncomputable def inst_isScalarTower_degreeZero :
    IsScalarTower k (𝒜 0) R := by
  letI : Algebra (𝒜 0) R := inst_algebra_degreeZero (𝒜 := 𝒜)
  refine IsScalarTower.of_algebraMap_eq' (R := k) (S := (𝒜 0)) (A := R) ?_
  ext x
  simp

lemma homogeneous_mem_adjoin_of_irrelevant_eq_span
    {T : Finset R}
    (hspan : Ideal.span (T : Set R) = irrelevantIdeal (𝒜 := 𝒜))
    (hT : ∀ t ∈ T, ∃ d : ℕ, 0 < d ∧ t ∈ 𝒜 d) :
    ∀ d : ℕ, ∀ y : R, y ∈ 𝒜 d → y ∈ Algebra.adjoin (𝒜 0) (T : Set R) := by
  classical
  intro d
  refine Nat.strong_induction_on d ?_
  intro d ih y hy
  by_cases hd0 : d = 0
  · subst hd0
    simpa using (Subalgebra.algebraMap_mem (Algebra.adjoin (𝒜 0) (T : Set R)) ⟨y, hy⟩)
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    have hy_irrel : y ∈ irrelevantIdeal (𝒜 := 𝒜) := by
      simpa [irrelevantIdeal] using
        HomogeneousIdeal.mem_irrelevant_of_mem (𝒜 := 𝒜) (x := y) (i := d) hdpos hy
    have hy_span : y ∈ Ideal.span (T : Set R) := by
      simpa [hspan] using hy_irrel
    have hy_span' : y ∈ (Submodule.span R (T : Set R) : Submodule R R) := by
      change y ∈ ((Ideal.span (T : Set R) : Ideal R) : Submodule R R)
      exact hy_span
    rcases
        (Finsupp.mem_span_iff_linearCombination (R := R) (M := R) (s := (T : Set R)) y).1 hy_span'
      with ⟨l, hl⟩
    -- Choose a positive degree for each generator `t ∈ T`.
    choose degT hdegTpos hdegTmem
      using (fun t : (T : Set R) => (hT t.1 (by simp [Finset.mem_coe.mp t.2])))
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
      have h1 : πd (Finsupp.linearCombination R (fun t : (T : Set R) => (t : R)) l) = πd y := by
        simpa [hl] using congrArg πd hl
      have h1' : πd (Finset.sum l.support (fun t => l t * (t : R))) = πd y := by
        rw [← hl_sum]; exact h1
      have h2 : Finset.sum l.support (fun t => πd (l t * (t : R))) = πd y := by
        simpa [map_sum] using h1'
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
      have ht_mem : (t : R) ∈ Algebra.adjoin (𝒜 0) (T : Set R) :=
        Algebra.subset_adjoin t.2
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
        rw [hπ]
        exact
          (Subsemiring.mul_mem (Algebra.adjoin (𝒜 0) (T : Set R)).toSubsemiring hcoeff_mem ht_mem)
      · have hπ0 : πd (l t * (t : R)) = 0 := by
          simpa [πd] using
            (DirectSum.coe_decompose_mul_of_right_mem_of_not_le (𝒜 := 𝒜)
              (a := l t) (b := (t : R)) (n := d) (i := degT t) ht_hom hle)
        rw [hπ0]
        exact zero_mem _
    simpa [hproj] using hsum_mem

lemma finiteType_degreeZero_of_irrelevant_fg
    (h : (irrelevantIdeal (𝒜 := 𝒜)).FG) :
    Algebra.FiniteType (𝒜 0) R := by
  classical
  obtain ⟨T, hspan, hT⟩ := exists_finset_homogeneous_pos_generators (𝒜 := 𝒜) h
  refine ⟨⟨T, ?_⟩⟩
  rw [eq_top_iff]
  intro r _
  rw [← DirectSum.sum_support_decompose 𝒜 r]
  refine Subalgebra.sum_mem (Algebra.adjoin (𝒜 0) (T : Set R)) ?_
  intro i _
  have hy : ((DirectSum.decompose 𝒜 r) i : R) ∈ 𝒜 i :=
    SetLike.coe_mem ((DirectSum.decompose 𝒜 r) i)
  exact homogeneous_mem_adjoin_of_irrelevant_eq_span (𝒜 := 𝒜) hspan hT i _ hy

theorem finiteType_of_finitely_generated_irrelevant_ideal
    (h : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG) :
    Algebra.FiniteType (𝒜 0) R :=
  finiteType_degreeZero_of_irrelevant_fg (𝒜 := 𝒜) (h := by
    simpa [irrelevantIdeal] using h)

theorem finiteType_k_of_finitely_generated_irrelevant_ideal
    [Algebra.FiniteType k (𝒜 0)] (h : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG) :
    Algebra.FiniteType k R := by
  classical
  letI : Algebra (𝒜 0) R := inst_algebra_degreeZero (𝒜 := 𝒜)
  letI : IsScalarTower k (𝒜 0) R := inst_isScalarTower_degreeZero (𝒜 := 𝒜)
  exact Algebra.FiniteType.trans (R := k) (S := 𝒜 0) (A := R)
    (hRS := inferInstance) (hSA := finiteType_of_finitely_generated_irrelevant_ideal h)
end

/-- If `toR : A →ₐ[k] R` is grading-preserving (sends `𝒜G d` into `𝒜 d`),
then taking the degree-`0` component commutes with `toR`. -/
lemma AlgHom.map_decompose_zero
    {k : Type u} [Field k]
    {A : Type*} [CommRing A] [Algebra k A]
    {R : Type*} [CommRing R] [Algebra k R]
    (toR : A →ₐ[k] R)
    (𝒜G : ℕ → Submodule k A) [GradedAlgebra 𝒜G]
    (𝒜 : ℕ → Submodule k R) [GradedAlgebra 𝒜]
    (htoR : ∀ (d : ℕ) (a : A), a ∈ 𝒜G d → toR a ∈ 𝒜 d) (a : A) :
    toR ((DirectSum.decompose 𝒜G a) 0 : A) =
      ((DirectSum.decompose 𝒜 (toR a)) 0 : R) := by
  refine DirectSum.Decomposition.inductionOn (ℳ := 𝒜G)
    (motive := fun a => toR ((DirectSum.decompose 𝒜G a) 0 : A) =
      ((DirectSum.decompose 𝒜 (toR a)) 0 : R)) (by simp) ?_ ?_ a
  · rintro i ⟨c, hc⟩
    change toR ((DirectSum.decompose 𝒜G (c : A)) 0 : A) =
        ((DirectSum.decompose 𝒜 (toR (c : A))) 0 : R)
    by_cases hi : i = 0
    · subst hi
      rw [DirectSum.decompose_of_mem_same 𝒜G hc,
          DirectSum.decompose_of_mem_same 𝒜 (htoR 0 c hc)]
    · rw [DirectSum.decompose_of_mem_ne 𝒜G hc hi,
          DirectSum.decompose_of_mem_ne 𝒜 (htoR i c hc) hi]
      simp
  · intro x y hx hy
    simp only [DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add,
      map_add, hx, hy]

section FixedSubalgebraFiniteType

variable {k : Type u} [Field k]
variable {A : Type*} [CommRing A] [Algebra k A]
variable (𝒜G : ℕ → Submodule k A) [GradedAlgebra 𝒜G]

open Algebra HomogeneousIdeal

/-- The fixed subalgebra `A = R^G` is finitely generated as a `k`-algebra, provided its degree-`0`
piece is finitely generated over `k` and its irrelevant ideal is finitely generated as an ideal of
`A`. (Specialises `finiteType_k_of_finitely_generated_irrelevant_ideal` to `R^G`.) -/
theorem fixedSubalgebra_finiteType
    [FiniteType k (𝒜G 0)]
    (hfg : (irrelevant 𝒜G).toIdeal.FG) :
    FiniteType k A :=
  finiteType_k_of_finitely_generated_irrelevant_ideal hfg

end FixedSubalgebraFiniteType

end GradedAlgebraFiniteType

/-! ## C. Reynolds ideal machinery -/

section ReynoldsIdealMachinery

section ExtendedIdealNoether

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

/-- Since `R` is Noetherian, the ideal `R₊^G R` is finitely generated. -/
theorem extendedRGplus_fg (extendedRGplus : Ideal R) : extendedRGplus.FG :=
  IsNoetherian.noetherian extendedRGplus

end ExtendedIdealNoether

section ChooseFiniteGenerators

variable {R : Type*} [CommRing R]
variable {RGplusSet : Set R}
variable {extendedRGplus : Ideal R}

/-- If the extended ideal `R₊^G R` is generated by `RGplusSet` and is finitely generated as an
ideal of `R`, then one can choose finitely many generators from `RGplusSet`. -/
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
      (Submodule.span R RGplusSet : Submodule R R).FG := hfg_span_ideal
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

end ChooseFiniteGenerators

section RGplusA_FiniteGeneration

variable {k : Type u} [Field k]

variable {A : Type*} [CommRing A] [Algebra k A] [DecidableEq A]

variable {R : Type*} [CommRing R] [Algebra k R]

variable {toR : A →ₐ[k] R}
variable {ρ : R →ₗ[k] A}

variable {RGplusA : Ideal A}
variable {extendedRGplus : Ideal R}

variable {s : Finset R}

/-- The Reynolds/GIT spanning property.

If `toR f` lies in the `R`-ideal generated by `s`, then `f` lies in the `A`-ideal
generated by the Reynolds images `ρ x` for `x ∈ s`. -/
def ReynoldsGITSpanProperty (toR : A →ₐ[k] R) (ρ : R →ₗ[k] A) (s : Finset R) : Prop :=
  ∀ f : A,
    toR f ∈ Ideal.span (↑s : Set R) →
      f ∈ Ideal.span ↑(Finset.image (fun x => ρ x) s)

/-- Membership form: elements of `RGplusA` lie in the `A`-ideal generated by `ρ '' s`.

Hypotheses:
- `hs_span`: `s` spans `extendedRGplus` as an ideal of `R`;
- `hcomap`: `RGplusA` is the preimage of `extendedRGplus` under `toR`;
- `hReynolds`: `ReynoldsGITSpanProperty` (the concrete GIT/Reynolds input).
-/
theorem mem_span_of_reynolds_generators
    (hs_span : Ideal.span (↑s : Set R) = extendedRGplus)
    (hcomap : RGplusA = Ideal.comap (toR : A →+* R) extendedRGplus)
    (hReynolds : ReynoldsGITSpanProperty toR ρ s)
    (f : A) (hf : f ∈ RGplusA) :
    f ∈ Ideal.span ↑(Finset.image (fun x => ρ x) s) := by
  refine hReynolds f ?_
  have hf_comap : f ∈ Ideal.comap (toR : A →+* R) extendedRGplus := by
    simpa [hcomap] using hf
  have hf' : toR f ∈ extendedRGplus := Ideal.mem_comap.mp hf_comap
  simpa [hs_span] using hf'

/-- `RGplusA` is finitely generated.

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

end RGplusA_FiniteGeneration

section ReynoldsRewriting

variable {k : Type u} [Field k]
variable {A : Type*} [CommRing A] [Algebra k A]
variable {R : Type*} [CommRing R] [Algebra k R]
variable (toR : A →ₐ[k] R)
variable (ρ : R →ₗ[k] A)
variable (s : Finset R)
variable (lift : R → A)

/-- Applying the Reynolds operator to both sides of `toR f = ∑ x ∈ s, x * coeff x` yields
`f = ∑ x ∈ s, lift x * ρ (coeff x)`. -/
theorem reynolds_rewrite
    (f : A) (a_f : s → R)
    (hf : toR f = ∑ x ∈ s.attach, x.val * a_f x)
    (hlift : ∀ x ∈ s, toR (lift x) = x)
    (hρ_id : ∀ a : A, ρ (toR a) = a)
    (hρ_mul : ∀ (a : A) (r : R), ρ ((toR a) * r) = a * ρ r) :
    f = ∑ x ∈ s.attach, lift x.val * ρ (a_f x) := by
  have hρf : ρ (toR f) = ρ (∑ x ∈ s.attach, x.val * a_f x) := by
    rw [hf]
  rw [hρ_id] at hρf
  rw [map_sum] at hρf
  rw [hρf]
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hmul := hρ_mul (lift x.val) (a_f x)
  rw [hlift x.val x.property] at hmul
  exact hmul

/-- Ideal-membership form of `reynolds_rewrite`. -/
theorem mem_ideal_span_lift_of_reynolds
    (f : A) (coeff : s → R)
    (hf : toR f = ∑ x ∈ s.attach, x.val * coeff x)
    (hlift : ∀ x ∈ s, toR (lift x) = x)
    (hρ_id : ∀ a : A, ρ (toR a) = a)
    (hρ_mul : ∀ (a : A) (r : R), ρ ((toR a) * r) = a * ρ r) :
    f ∈ Ideal.span ((lift '' (s : Set R)) : Set A) := by
  rw [reynolds_rewrite toR ρ s lift f coeff hf hlift hρ_id hρ_mul]
  refine Ideal.sum_mem _ ?_
  intro x hx
  refine Ideal.mul_mem_right _ _ ?_
  refine Ideal.subset_span ?_
  exact Set.mem_image_of_mem lift x.property

/-- Auxiliary: from membership in `Ideal.span (s : Set R)` extract a presentation
`x = ∑ t ∈ s.attach, t.val * coeff t` for some `coeff : s → R`. -/
lemma exists_finset_presentation_of_mem_span
    {R : Type*} [CommRing R] (s : Finset R) (x : R)
    (hx : x ∈ Ideal.span (↑s : Set R)) :
    ∃ coeff : s → R, x = ∑ t ∈ s.attach, t.val * coeff t := by
  classical
  -- View the ideal-span hypothesis as a submodule-span hypothesis.
  have hxsub : x ∈ (Submodule.span R (↑s : Set R) : Submodule R R) := hx
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

/-- **The Reynolds operator witnesses `ReynoldsGITSpanProperty`.**

If every `x ∈ s` lifts to some `lift x ∈ A` with `toR (lift x) = x`, and `ρ` is the
Reynolds operator (identity on `toR '' A` and Reynolds-multiplicative on
`toR a * r`), then `ReynoldsGITSpanProperty toR ρ s` holds.

Proof: from `toR f ∈ Ideal.span s` get a presentation
`toR f = ∑ x ∈ s.attach, x.val * coeff x`. Apply `mem_ideal_span_lift_of_reynolds`
to land in `Ideal.span (lift '' s)`. On `s`,
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
  -- (b) land in `Ideal.span (lift '' s)`.
  have hf_lift :
      f ∈ Ideal.span ((lift '' (s : Set R)) : Set A) :=
    mem_ideal_span_lift_of_reynolds toR ρ s lift f coeff hcoeff hlift hρ_id hρ_mul
  -- (c) On `s`, `ρ x = lift x`.
  have hρ_eq_lift : ∀ x ∈ s, ρ x = lift x := fun x hx =>
    (congrArg ρ (hlift x hx).symm).trans (hρ_id (lift x))
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

end ReynoldsRewriting

end ReynoldsIdealMachinery

/-!
## D. The main GIT finiteness theorem

For a linearly reductive group `G` acting on a finitely generated `k`-algebra `R`,
the invariant subring `R^G` is finitely generated as a `k`-algebra.

The proof assembles the pieces from the preceding sections:
* **Reynolds projection**: from `IsLinearlyReductive` + `IsLocallyFinite`, the upstream
  `exists_reynolds_mul_compat_of_locallyFinite` (in `GIT.ReynoldsOperator`) gives a
  multiplicative Reynolds projection `R ↠ R^G`.
* **Extended ideal generators** (`ReynoldsIdealMachinery`):
  `extendedRGplus_fg` (Noether) + `exists_generators_extendedRGplus_from_RGplus` pick
  finitely many generators inside `R₊^G`.
* **Pushing back via Reynolds** (`RGplusA_fg_of_reynolds`,
  `reynoldsGITSpanProperty_of_reynolds`): the irrelevant ideal of `R^G` is f.g. as
  an ideal of `R^G`.
* **Finite generation from f.g. irrelevant ideal** (`GradedAlgebraFiniteType`):
  `fixedSubalgebra_finiteType` (specializing `finiteType_k_of_finitely_generated_irrelevant_ideal`)
  concludes `FiniteType k (R^G)`.

The inherited grading `R^G = ⨁ d, (𝒜 d ∩ R^G)` itself is the standalone result
`fixedSubalgebra_decomposes` in `InheritedGrading`; the main theorem takes
`[GradedAlgebra 𝒜G]` as a hypothesis rather than constructing it here.
-/

section GIT_MainTheorem

-- `k`, `G`, `R` share universe `u` so that `exists_reynolds_of_locallyFinite` applies.
variable (k : Type u) [Field k]
variable (G : Type u) [Group G]
variable (R : Type u) [CommRing R] [Algebra k R]

-- Action of `G` on `R` as a `MulSemiringAction` — a single typeclass bundling both the
-- ring-automorphism structure (needed for `FixedSubalgebra`) and the linear-action structure
-- (needed for the Reynolds machinery via `Representation.ofDistribMulAction`).
variable [MulSemiringAction G R] [SMulCommClass G k R]

-- The grading on `R`.
variable (𝒜 : ℕ → Submodule k R) [GradedAlgebra 𝒜]

-- The induced grading on `R^G`.
variable (𝒜G : ℕ → Submodule k (FixedSubalgebra k G R))
  [GradedAlgebra 𝒜G]

open Algebra HomogeneousIdeal

/-- **Main GIT theorem.**

Let `G` be a linearly reductive group acting on a finitely generated `k`-algebra `R`
by `k`-algebra automorphisms, with the action preserving a chosen `ℕ`-grading on `R`
and being locally finite. Then the invariant subalgebra `R^G` is finitely generated
as a `k`-algebra.

Hypotheses:
* `hlr`     : `G` is linearly reductive over `k`.
* `hlf`     : the underlying `k`-module action of `G` on `R` is locally finite.
* `[FiniteType k R]`        : `R` is finitely generated as a `k`-algebra. This also makes `R`
  Noetherian (Hilbert basis theorem), which is what Step 3 needs to get `extendedRGplus.FG`.
* `[FiniteType k (𝒜G 0)]`   : the degree-`0` piece of `R^G` is f.g./k
  (automatic when `𝒜G 0 = k`).
-/
theorem GIT_finiteType_invariants
    [FiniteType k R]
    [FiniteType k (𝒜G 0)] /- need to be removed -/
    (hlr : IsLinearlyReductive k G)
    (hlf : Representation.IsLocallyFinite k G R)
    (h𝒜G : ∀ (d : ℕ) (a : FixedSubalgebra k G R),
      a ∈ 𝒜G d → (a : R) ∈ 𝒜 d) :
    FiniteType k (FixedSubalgebra k G R) := by
  classical
  -- `R` is Noetherian: it is a finite-type algebra over the field `k` (Hilbert basis theorem).
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  -- Reduction: it suffices to show the irrelevant ideal of `R^G` is f.g.
  -- (The Reynolds projection enters later, via `exists_reynolds_mul_compat_of_locallyFinite`,
  -- which provides the multiplicative version we actually need.)
  refine fixedSubalgebra_finiteType 𝒜G ?_
  -- ── Setup ────────────────────────────────────────────────────────────────
  -- `A = R^G` as a `k`-subalgebra, plus inclusion `toR : A →ₐ[k] R`.
  let A : Subalgebra k R := FixedSubalgebra k G R
  let toR : A →ₐ[k] R := A.val
  -- The irrelevant ideal of `A` and its extension to `R`.
  let RGplusA : Ideal A := (irrelevant 𝒜G).toIdeal
  change RGplusA.FG
  let extendedRGplus : Ideal R := Ideal.map (toR : A →+* R) RGplusA
  let RGplusSet : Set R := (toR : A → R) '' (RGplusA : Set A)
  -- ── The extended ideal is f.g. (Noetherian) ──────────────────────────────
  have h_ext_fg : extendedRGplus.FG :=
    extendedRGplus_fg extendedRGplus
  -- ── Span property: `RGplusSet` ideal-spans `extendedRGplus` ──────────────
  have hspan_RG : Ideal.span RGplusSet = extendedRGplus := by
    change Ideal.span ((toR : A → R) '' (RGplusA : Set A)) = Ideal.map (toR : A →+* R) RGplusA
    rw [Ideal.map]; rfl
  -- ── Pick finitely many generators inside `RGplusSet` ─────────────────────
  obtain ⟨s, hs_sub, hs_span⟩ :=
    exists_generators_extendedRGplus_from_RGplus hspan_RG h_ext_fg
  -- ── Comap identification: `RGplusA = comap toR extendedRGplus` ──────────
  have htoR_inj : Function.Injective (toR : A →+* R) := Subtype.val_injective
  -- Compatibility of deg-0 components: the inclusion `A ↪ R` sends `(decompose 𝒜G a) 0`
  -- to `(decompose 𝒜 (toR a)) 0`. Proved by induction on the graded decomposition.
  have hdecomp0 : ∀ a : A,
      (((DirectSum.decompose 𝒜G a) 0 : A) : R) =
        ((DirectSum.decompose 𝒜 (toR a)) 0 : R) :=
    AlgHom.map_decompose_zero toR 𝒜G 𝒜 h𝒜G
  -- Each `a ∈ irrelevant 𝒜G` has `toR a ∈ irrelevant 𝒜` in `R`.
  have h_ext_le_irrR : extendedRGplus ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
    refine Ideal.map_le_iff_le_comap.mpr ?_
    intro a ha
    have h0A : ((DirectSum.decompose 𝒜G a) 0 : A) = 0 := by
      have hp := (HomogeneousIdeal.mem_irrelevant_iff (𝒜 := 𝒜G) a).mp ha
      simpa [GradedRing.proj_apply] using hp
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
        have hp := (HomogeneousIdeal.mem_irrelevant_iff (𝒜 := 𝒜) (toR x)).mp htoR_x
        simpa [GradedRing.proj_apply] using hp
      have hRA0 : (((DirectSum.decompose 𝒜G x) 0 : A) : R) = 0 := by
        rw [hdecomp0 x]; exact h0R
      have h0A : ((DirectSum.decompose 𝒜G x) 0 : A) = 0 := htoR_inj hRA0
      change x ∈ HomogeneousIdeal.irrelevant 𝒜G
      rw [HomogeneousIdeal.mem_irrelevant_iff]
      simpa [GradedRing.proj_apply] using h0A
  -- ── Lifts: each `x ∈ s` comes from some element of `RGplusA ⊆ A` ─────────
  choose liftFn hliftFn_mem hliftFn_eq using hs_sub
  let lift : R → A := fun x => if hx : x ∈ s then liftFn x hx else 0
  have hlift : ∀ x ∈ s, toR (lift x) = x := fun x hx => by
    simp only [lift, dif_pos hx]; exact hliftFn_eq x hx
  -- ── Reynolds linear map `ρ_lin : R →ₗ[k] A` from the multiplicative `Rep`-projection ─
  -- `σ.invariants` and `A` share the same carrier `{r | ∀ g, g • r = r}`, so the Reynolds
  -- projection `π'` co-restricts to a `k`-linear map into `A`. The required identities
  -- come from `IsProj` plus the `R^G`-multiplicativity bundled by Reynolds.
  obtain ⟨π', hπ'_proj, hπ'_mul⟩
    := IsLinearlyReductive.exists_reynolds_mulCompat_of_isLocallyFinite hlr R hlf
  have hA_inv : ∀ {a : A}, (a : R) ∈ (Representation.ofDistribMulAction k G R).invariants :=
    fun {a} => (Representation.mem_invariants _ _).mpr a.property
  have hπ'_to_A : ∀ r : R, π'.hom.hom r ∈ A.toSubmodule := fun r g =>
    ((Representation.ofDistribMulAction k G R).mem_invariants _).mp (hπ'_proj.map_mem r) g
  let ρ_lin : R →ₗ[k] A := LinearMap.codRestrict A.toSubmodule π'.hom.hom hπ'_to_A
  have hρ_id : ∀ a : A, ρ_lin (toR a) = a := fun a =>
    Subtype.ext (hπ'_proj.map_id (a : R) hA_inv)
  have hρ_mul : ∀ (a : A) (r : R), ρ_lin ((toR a) * r) = a * ρ_lin r := fun a r =>
    Subtype.ext (hπ'_mul hA_inv r)
  have hρ_gen : ∀ x ∈ s, ρ_lin x ∈ RGplusA := fun x hx => by
    rw [← hliftFn_eq x hx, hρ_id]; exact hliftFn_mem x hx
  -- ── The Reynolds spanning property `ReynoldsGITSpanProperty toR ρ_lin s` ──
  have hReynolds : ReynoldsGITSpanProperty toR ρ_lin s :=
    reynoldsGITSpanProperty_of_reynolds toR ρ_lin s lift hlift hρ_id hρ_mul
  -- ── Assemble — `RGplusA.FG` ──────────────────────────────────────────────
  exact RGplusA_fg_of_reynolds hs_span hcomap hρ_gen hReynolds

end GIT_MainTheorem
end GIT
